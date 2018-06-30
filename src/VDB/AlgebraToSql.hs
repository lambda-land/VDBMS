module VDB.AlgebraToSql where 

import Prelude hiding (EQ, NEQ ,LT ,LTE , GTE ,GT)
import VDB.Target 
-- import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  

import Database.HDBC
import Database.HDBC.PostgreSQL

import Data.Map(Map)
import qualified Data.Map as Map 

type QueryClause = String 

-- | select attributelist, relationlist, condition in plain string 
querySFW :: String -> String -> String -> QueryClause  
querySFW al rl cond = if length cond == 0 
                    then buildQuery ["SELECT ", al , " FROM ",rl ]
                    else buildQuery ["SELECT ", al , " FROM ",rl , " WHERE ", cond ]

-- | build a list of string into Query clause
buildQuery :: [String] -> String 
buildQuery list = filter (/= '\n') $ unlines list

-- | transfer sql value to string 
sqlRowToString = map (fromSql :: SqlValue -> String)


-- main :: IO ()
-- main = do 
--         conn <- connectPostgreSQL "host=localhost dbname=ai_db"
--         result <- quickQuery conn (querySFW "*" "taughtby" "") []
--         mapM_ print $ map sqlRowToString result

-- main :: IO ()
-- main = do 
--         conn <- connectPostgreSQL "host=localhost dbname=ai_db"
--         result <- quickQuery conn (q0) []
--         mapM_ print $ map sqlRowToString result

-- data Query = QueryOp SetOp Query Query 
--            | Select [Attribute] Query 
--            | From Relation (Maybe T.Condition)            
--            | EmptyQuery
--   deriving (Show)

data Query = QueryOp SetOp Query Query 
           | Select [Attribute] Query 
           | Where (Maybe T.Condition) Query 
           | From Relation            
           | EmptyQuery
  deriving (Show)

-- | TO DO: update predence condition
type SqlQuery = String 

type TableAlias = String 

type FeatureEnv = Map Attribute F.FeatureExpr

-- | TO DO : 1. make a map for feature expression for each attribute
--           2. variational queries

-- | translate variational algebra to sql query AST
transAlgebraToQuery :: Algebra -> FeatureEnv -> Query  
transAlgebraToQuery (SetOp Prod  a1 a2)  m = QueryOp Prod (transAlgebraToQuery a1) (transAlgebraToQuery a2) 
transAlgebraToQuery (SetOp Diff  a1 a2)  m = QueryOp Diff (transAlgebraToQuery a1) (transAlgebraToQuery a2)  
transAlgebraToQuery (SetOp Union a1 a2)  m = QueryOp Union (transAlgebraToQuery a1) (transAlgebraToQuery a2)   
transAlgebraToQuery (Proj  opAttrList a) m = 
  let m' = foldl (\m-> \(f,a) -> Map.insert a f m ) Map.empty opAttrList 
  in Select (map lift opAttrList) (transAlgebraToQuery a m')
transAlgebraToQuery (Sel   cond  a)      m = 
  let cond' = updateCond cond m 
  Where (Just cond' ) (transAlgebraToQuery a m) 
transAlgebraToQuery (AChc  f a1 a2)      m = undefined 
transAlgebraToQuery (TRef  r)            m = From r 
transAlgebraToQuery (Empty)              m = EmptyQuery

--| transfer condition into target condition. (condition + SAT FeatureExpr)
updateCond :: C.Condtion -> FeatureEnv -> T.Condition 
updateCond (CChc f cond1 cond2 ) m = undefined
updateCond _                     m = undefined -- SAT

-- | translate sql query AST to plain sql string with counter 
transQueryToSql' :: Query -> SqlQuery -> Int -> (SqlQuery, TableAlias, Int )
transQueryToSql' (Select attrList q) p c =
  let t =  "T" ++ show c 
      (p',q',c') = transQueryToSql' q p (c+1)
  in ((buildQuery [" SELECT ", prettyAttrList attrList, " FROM ", p']), t, c')
transQueryToSql' (QueryOp Prod l r) p c = 
  let t = "T" ++ show c
      (pl,ql,cl) = transQueryToSql' l p (c+1)
      (pr,qr,cr) = transQueryToSql' r pl cl   
  in ((buildQuery [" (SELECT * ", " FROM ", pl, " , ", pr, " ) "]), t, cr)
transQueryToSql' (Where Nothing q) p c  = transQueryToSql' q p c 
transQueryToSql' (Where (Just cond) q) p c  =   
  let t = "T" ++ show c 
      (p',q',c') = transQueryToSql' q p c
  in (p' ++ buildQuery [" WHERE ", prettyCond cond], t, c')
transQueryToSql' (From r) p c = 
  let t = "T" ++ show c 
  in (buildQuery [" (SELECT * ", " FROM ",relationName r," )", " as ", t], t, c+1)
transQueryToSql' (empty) p c              = undefined

transQueryToSql :: Query -> (SqlQuery, TableAlias, Int )
transQueryToSql q = transQueryToSql' q " " 0

-- | abstract plain sql query from *plain sql query with counter*
-- sendToPosgreSQL :: Query -> QueryClause
-- sendToPosgreSQL (QueryOp Prod q1 q2)  = sendToPosgreSQL q1 ++ sendToPosgreSQL q2
-- sendToPosgreSQL (QueryOp Diff q1 q2)  = undefined
-- sendToPosgreSQL (QueryOp Union q1 q2) = undefined
-- sendToPosgreSQL (Select attrList q)   = buildQuery [" SELECT ", prettyAttrList attrList, sendToPosgreSQL q]
-- sendToPosgreSQL (From r )              = buildQuery [" FROM ", prettyRel r, " as ", prettyRel r]
-- sendToPosgreSQL (From r (Just cond)) = undefined

-- | lift the a from *opt a* 
lift :: Opt a  -> a  
lift (_,a)= a 


-- | pretty print the condition in module target
prettyCond :: T.Condition -> QueryClause
prettyCond (T.Lit  b)                 = show b
prettyCond (T.Comp compOp a1 a2)      = prettyAtom a1 ++ prettyCompOp compOp ++ prettyAtom a2
prettyCond (T.Not  cond)              = undefined
prettyCond (T.Or   cond1 cond2)       = undefined
prettyCond (T.And  cond1 cond2)       = undefined
prettyCond (T.SAT  f)                 = "SAT(" ++ F.prettyFeatureExpr f ++ ") "

-- | pretty print the compare operator 
prettyCompOp :: CompOp ->QueryClause
prettyCompOp EQ  = "=="
prettyCompOp NEQ = "/="
prettyCompOp LT  = "<"
prettyCompOp LTE = "<="
prettyCompOp GTE = ">="
prettyCompOp GT  = ">"

-- | pretty print the relation
prettyRel :: Relation -> QueryClause 
prettyRel = relationName

-- | pretty print the plain attribute list , which means no opt/tag with attribute
prettyAttrList :: [Attribute] -> QueryClause
prettyAttrList []     = ""
prettyAttrList [x]    = attributeName x
prettyAttrList (x:xs) = attributeName x ++ "," ++ prettyAttrList xs

-- | pretty print the Atom 
prettyAtom :: C.Atom -> QueryClause
prettyAtom (C.Val  v  ) = prettyValue v
prettyAtom (C.Attr attr ) = attributeName attr

-- | pretty print the value in Condition
prettyValue :: Value -> QueryClause
prettyValue (I i) = show i
prettyValue (B b) = show b 
prettyValue (S s) = s

-- 
--  Examples
-- 
t0 =  (Relation {relationName = "taughtby"})
t1 = (Relation {relationName = "courselevel"})
a1 = Attribute {attributeName = "course"}
a2 = Attribute {attributeName = "professor"}
f0 = (Feature {featureName = "US"})

q1 = Select [a1,a2] $ From t0 
q2 = Select [a1,a2] $ QueryOp Prod (From t0 ) (From t1)

q3 = Select [a1,a2] $ Where (Just (T.Comp GT (C.Attr a1) (C.Val (I 5))) ) $ From t0 
q4 = Select [a1,a2] $ Where (Just (T.SAT (F.Ref f0 ))) $ From t0 

w1 = Where (Just (T.SAT (F.Ref f0 ))) $ From t0 

e1 = SetOp Prod (TRef "r1") (TRef "r2")

e2 = Proj [(F.And 
                    (F.Ref (Feature {featureName = "A"})) 
                    (F.Ref (Feature {featureName = "A"})), 
                   Attribute {attributeName = "1"})
                 ,
                  (F.Ref (Feature {featureName = "B"}),
                   Attribute {attributeName = "2"})
                 ] 
          (TRef "Table1")

e3 =  Proj [(F.And 
                    (F.Ref (Feature {featureName = "A"})) 
                    (F.Ref (Feature {featureName = "A"})), 
                   Attribute {attributeName = "1"})
                 ,
                  (F.Ref (Feature {featureName = "B"}),
                   Attribute {attributeName = "2"})
                 ] 
          (SetOp Prod 
                (AChc (F.Ref (Feature {featureName = " B"})) 
                      (TRef (Relation {relationName = "1"})) 
                       Empty) 
                (SetOp Prod 
                      (AChc (F.Ref (Feature {featureName = "C"})) 
                            (TRef (Relation {relationName = "2"})) 
                             Empty) 
                       Empty))


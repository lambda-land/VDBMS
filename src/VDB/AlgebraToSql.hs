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
-- import Database.HDBC.PostgreSQL

import Data.Map(Map)
import qualified Data.Map as Map 

import Data.Set (Set)
import qualified Data.Set as Set

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

data Query = QueryOp SetOp Query Query 
           | Select [Attribute] Query 
           | Where (Maybe T.Condition) Query 
           | From Relation            
           | EmptyQuery
  deriving (Show,Eq)

-- | TO DO: update predence condition
type SqlQuery = String 

type TableAlias = String 

type FeatureEnv = Map Attribute F.FeatureExpr
type ConditionEnv = Set T.Condition

-- ToDo: Make enviroment as condition + featureExpr

-- | TO DO : 1. make a map for feature expression for each attribute -- (half done;)
--           2. variational queries -- Done; (use Union)

-- | translation from algebra to plain sql query
translate :: Algebra -> SqlQuery
translate a = let (q, t, i ) = transQueryToSql $ transAlgebraToQuery a 
              in q 


-- | translate variational algebra to sql query AST
transAlgebraToQuery' :: Algebra -> FeatureEnv -> T.Condition -> Query  
transAlgebraToQuery' (SetOp Prod  a1 a2)  m s = QueryOp Prod (transAlgebraToQuery' a1 m s) (transAlgebraToQuery' a2 m s) 
transAlgebraToQuery' (SetOp Diff  a1 a2)  m s = QueryOp Diff (transAlgebraToQuery' a1 m s) (transAlgebraToQuery' a2 m s)  
transAlgebraToQuery' (SetOp Union a1 a2)  m s = QueryOp Union (transAlgebraToQuery' a1 m s) (transAlgebraToQuery' a2 m s)   
transAlgebraToQuery' (Proj  opAttrList a) m s = 
  let m' = foldl (\m-> \(f,a) -> Map.insert a f m ) Map.empty opAttrList 
  in Select (map lift opAttrList) (transAlgebraToQuery' a m' s)
transAlgebraToQuery' (Sel cond  a)        m s = 
  case cond of 
    (C.CChc f cond1 cond2 ) -> let newAlgebra = AChc f (Sel cond1 a) (Sel cond2 a) 
                               in  transAlgebraToQuery' newAlgebra m s
    _                       -> let cond' = updateCond cond m
                               in transAlgebraToQuery' a m (T.And cond' s)
transAlgebraToQuery' (AChc f l r)       m s =
  let l' = transAlgebraToQuery' l m (T.And (T.SAT f) s) 
      r' = transAlgebraToQuery' r m (T.And (T.SAT (F.Not f)) s)
  in QueryOp Union l' r'    
transAlgebraToQuery' (TRef  r)            m s = Where (Just s) (From r)       -- ToDO : update where condition according to environment(fetureExpr) 
transAlgebraToQuery' (Empty)              m s = EmptyQuery


transAlgebraToQuery :: Algebra -> Query 
transAlgebraToQuery a = transAlgebraToQuery' a Map.empty (Lit True)


-- | transfer condition into target condition. (condition + SAT FeatureExpr)
updateCond :: C.Condition -> FeatureEnv -> T.Condition 
updateCond (C.Lit  b)              m = T.Lit b
updateCond (C.Comp op a1 a2)       m = T.Comp op a1 a2 
updateCond (C.Not  cond)           m = T.Not (updateCond cond m)
updateCond (C.Or   cond1 cond2)    m = T.Or (updateCond cond1 m) (updateCond cond2 m)
updateCond (C.And  cond1 cond2)    m = T.And (updateCond cond1 m) (updateCond cond2 m)


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
  in (buildQuery ["( ", p' , " WHERE ", prettyCond cond, " )", " as ", t], t, c'+1)
transQueryToSql' (From r) p c = 
  let t = "T" ++ show c 
  in (buildQuery [" SELECT * ", " FROM ",relationName r], t, c+1)
transQueryToSql' (EmptyQuery) p c              = (" ", p , c )  
transQueryToSql' (QueryOp Union l EmptyQuery) p c = 
  let (l', pr ,cr) = (transQueryToSql' l p c)
      t = "T" ++ show c
  in (l', t, c+1 )
transQueryToSql' (QueryOp Union EmptyQuery r) p c = 
  let (r', pr ,cr) = transQueryToSql' r p c
      t = "T" ++ show c
  in (r', t, c+1 )

transQueryToSql :: Query -> (SqlQuery, TableAlias, Int )
transQueryToSql q = transQueryToSql' q " " 0



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
prettyCond (T.SAT  f)                 = "SAT(" ++ F.prettyFeatureExpr f ++ ")"

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
f1 = (Feature {featureName = "F"})
cond1 = (C.Comp GT (C.Attr a1) (C.Val (I 5)))

q1 = Select [a1,a2] $ From t0 
q2 = Select [a1,a2] $ QueryOp Prod (From t0 ) (From t1)

q3 = Select [a1,a2] $ Where (Just (T.Comp GT (C.Attr a1) (C.Val (I 5))) ) $ From t0 
e_4 = Proj [(F.Ref (Feature {featureName = "A"}),a1)] $ Sel cond1 $ (TRef t0)
q4 = Select [a1,a2] $ Where (Just (T.SAT (F.Ref f0 ))) $ From t0 

w1 = Where (Just (T.SAT (F.Ref f0 ))) $ From t0 

e1 = SetOp Prod (TRef "r1") (TRef "r2")

e2 = Proj [(F.And 
                    (F.Ref (Feature {featureName = "A"})) 
                    (F.Ref (Feature {featureName = "B"})), 
                   Attribute {attributeName = "a1"})
                 ,
                  (F.Ref (Feature {featureName = "C"}),
                   Attribute {attributeName = "a2"})
                 ] 
          (TRef "Table1")

e3 =  Proj [(F.And 
                    (F.Ref (Feature {featureName = "A"})) 
                    (F.Ref (Feature {featureName = "B"})), 
                   Attribute {attributeName = "a1"})
                 ,
                  (F.Ref (Feature {featureName = "B"}),
                   Attribute {attributeName = "a2"})
                 ] 
          (SetOp Prod 
                (AChc (F.Ref (Feature {featureName = " FB"})) 
                      (TRef (Relation {relationName = "r1"})) 
                       Empty) 
                (AChc (F.Ref (Feature {featureName = "FC"})) 
                            (TRef (Relation {relationName = "r2"})) 
                             Empty))

e4 = Proj [((F.Lit True),a1)] (Sel cond2 (TRef t0))

cond2 = C.CChc (F.Ref f1) (C.Comp GT (C.Attr a1) (C.Val (I 5))) (C.Comp LT (C.Attr a1) (C.Val (I 5)))

test1 =  Proj [(F.Lit True, 
                   Attribute {attributeName = "a1"})
               ,(F.Lit True,
                   Attribute {attributeName = "a2"})
               ] 
          (TRef "Table1") 
test3 = Proj [(F.Lit True, Attribute {attributeName = "a1"})] $ 
            Sel (C.CChc (F.Ref (Feature {featureName = "F"}))
                       (C.Comp GT (C.Attr a1) (C.Val (I 5))) 
                       (C.Comp LT (C.Attr a1) (C.Val (I 5)))) $ 
            (TRef (Relation {relationName = "Table2"}))

test4 = AChc (F.Ref (Feature {featureName = "F"})) 
             (Proj [(F.Lit True, Attribute {attributeName = "a1"})] (TRef (Relation {relationName = "Table2"}))) 
             (Proj [(F.Lit True, Attribute {attributeName = "a1"})] (TRef (Relation {relationName = "Table2"})))
-- | translate variational algebra to sql query AST ** condition as a Set 
-- transAlgebraToQuery' :: Algebra -> FeatureEnv -> ConditionEnv -> Query  
-- transAlgebraToQuery' (SetOp Prod  a1 a2)  m s = QueryOp Prod (transAlgebraToQuery' a1 m s) (transAlgebraToQuery' a2 m s) 
-- transAlgebraToQuery' (SetOp Diff  a1 a2)  m s = QueryOp Diff (transAlgebraToQuery' a1 m s) (transAlgebraToQuery' a2 m s)  
-- transAlgebraToQuery' (SetOp Union a1 a2)  m s = QueryOp Union (transAlgebraToQuery' a1 m s) (transAlgebraToQuery' a2 m s)   
-- transAlgebraToQuery' (Proj  opAttrList a) m s = 
--   let m' = foldl (\m-> \(f,a) -> Map.insert a f m ) Map.empty opAttrList 
--   in Select (map lift opAttrList) (transAlgebraToQuery' a m' s)
-- transAlgebraToQuery' (Sel   cond  a)      m s = 
--   let cond' = updateCond cond m
--       s' = Set.insert cond' s 
--   in transAlgebraToQuery' a m s'
-- transAlgebraToQuery' (AChc  f a1 a2)      m s = undefined    
-- transAlgebraToQuery' (TRef  r)            m s = Where From r       -- ToDO : update where condition according to environment 
-- transAlgebraToQuery' (Empty)              m s = EmptyQuery


-- | abstract plain sql query from *plain sql query with counter*
-- sendToPosgreSQL :: Query -> QueryClause
-- sendToPosgreSQL (QueryOp Prod q1 q2)  = sendToPosgreSQL q1 ++ sendToPosgreSQL q2
-- sendToPosgreSQL (QueryOp Diff q1 q2)  = undefined
-- sendToPosgreSQL (QueryOp Union q1 q2) = undefined
-- sendToPosgreSQL (Select attrList q)   = buildQuery [" SELECT ", prettyAttrList attrList, sendToPosgreSQL q]
-- sendToPosgreSQL (From r )              = buildQuery [" FROM ", prettyRel r, " as ", prettyRel r]
-- sendToPosgreSQL (From r (Just cond)) = undefined


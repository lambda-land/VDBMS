-- | translation from variational relational algebra to ** SQL + SAT() **

-- | TO DO: 1. add update predence condition into TRANSLATED SQL
--          2. update where condition according to environment(fetureExpr) 
--          3. SAT(False), since in env [] -> False
--          4. "Where" always in the inner most level
--          -- fixed 3. original condition is true in T.Condition, make sure it is not use AND to concatenate with feature expressiion.
--          -- fixed 4. If query have condition (not includring Lit True), then should cancel the Lit true as condition.  
--          
-- | NOTE : 1. opt True --> do not insert feature Expr in attrFeatureEnv

module VDB.AlgebraToSql where 

import Prelude hiding (EQ ,LT ,GT)
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


type QueryClause = String 

-- | select attributelist, relationlist, condition in plain string 
querySFW :: String -> String -> String -> QueryClause  
querySFW al rl cond = if length cond == 0 
                    then buildQuery ["SELECT ", al , " FROM ",rl ]
                    else buildQuery ["SELECT ", al , " FROM ",rl , " WHERE ", cond ]



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

type SqlQuery = String 

type TableAlias = String 

type AttrFeatureEnv = Map Attribute F.FeatureExpr
type ConditionEnv = Set T.Condition




-- | translation from algebra to plain sql query
translate :: Algebra -> SqlQuery
translate a = transQueryToSql $ transAlgebraToQuery a 
              


-- | translate variational algebra to sql query AST
transAlgebraToQuery' :: Algebra -> AttrFeatureEnv -> Maybe T.Condition -> Query  
transAlgebraToQuery' (SetOp Prod  a1 a2)  m s = QueryOp Prod (transAlgebraToQuery' a1 m s) (transAlgebraToQuery' a2 m s) 
transAlgebraToQuery' (SetOp Diff  a1 a2)  m s = QueryOp Diff (transAlgebraToQuery' a1 m s) (transAlgebraToQuery' a2 m s)  
transAlgebraToQuery' (SetOp Union a1 a2)  m s = QueryOp Union (transAlgebraToQuery' a1 m s) (transAlgebraToQuery' a2 m s)   
transAlgebraToQuery' (Proj  opAttrList a) _ s = 
  -- let m' = foldl (\m -> \(f,a) -> Map.insert a f m ) Map.empty opAttrList
  let m' = foldl insertAttrFeatureExpr Map.empty opAttrList 
  in Select (map lift opAttrList) (transAlgebraToQuery' a m' s)

transAlgebraToQuery' (Sel cond  a)        m s = 
  case cond of 
    (C.CChc f cond1 cond2 ) -> let newAlgebra = AChc f (Sel cond1 a) (Sel cond2 a) 
                               in  transAlgebraToQuery' newAlgebra m s
    _                       -> case s of 
                                 Nothing -> let cond' = updateCond cond m
                                            in transAlgebraToQuery' a m (Just cond') 
                                 Just s' -> let cond' = updateCond cond m
                                            in transAlgebraToQuery' a m (Just (T.And cond' s'))
transAlgebraToQuery' (AChc f l r)       m s =
  case s of 
    Nothing -> let l' = transAlgebraToQuery' l m (Just (T.SAT f) ) 
                   r' = transAlgebraToQuery' r m (Just (T.SAT (F.Not f)))
               in QueryOp Union l' r'    
    Just s' -> let l' = transAlgebraToQuery' l m (Just (T.And (T.SAT f) s') )
                   r' = transAlgebraToQuery' r m (Just (T.And (T.SAT (F.Not f)) s'))
               in QueryOp Union l' r'    
transAlgebraToQuery'  (TRef  r)            m s = 
  let sat_cond = takeAttrFeatureExpr m s 
  in Where (sat_cond) (From r)       -- ToDO : update where condition according to environment(fetureExpr) 
transAlgebraToQuery'  (Empty)              _ _ = EmptyQuery



-- | insert feature Expr into Map. Make sure do not insert True into Map. 
insertAttrFeatureExpr :: AttrFeatureEnv -> Opt Attribute -> AttrFeatureEnv
insertAttrFeatureExpr m (F.Lit True, _) = m      -- env unchange if the featureExpr is true 
insertAttrFeatureExpr m (f,a)= Map.insert a f m 

-- | make featureExpr in attribute list has Or realtion between each others and then combine with where condition.

takeAttrFeatureExpr :: AttrFeatureEnv -> Maybe T.Condition -> Maybe T.Condition 
takeAttrFeatureExpr m Nothing         = case Map.null m of 
                                          True  -> Nothing 
                                          False ->  Just (T.SAT (flatFeatureExprMap (Map.elems m))) 
takeAttrFeatureExpr m (Just s)        = 
  let sat = T.SAT (flatFeatureExprMap (Map.elems m))
  in Just (T.And sat s ) 

  -- let f a b  = T.Or a (T.SAT b) 
  -- in Just (Map.foldl f s m)
-- | use T.Or concatenate the attribute featureExpr 
flatFeatureExprMap :: [F.FeatureExpr] -> F.FeatureExpr
flatFeatureExprMap []     = F.Lit False
flatFeatureExprMap (x:xs) = (F.Or x (flatFeatureExprMap xs))

transAlgebraToQuery :: Algebra -> Query 
transAlgebraToQuery a = transAlgebraToQuery' a Map.empty Nothing 

-- | transfer condition into target condition. (condition + SAT FeatureExpr)
updateCond :: C.Condition -> AttrFeatureEnv -> T.Condition 
updateCond (C.Lit  b)              _ = T.Lit b
updateCond (C.Comp op a1 a2)       _ = T.Comp op a1 a2 
updateCond (C.Not  cond)           m = T.Not (updateCond cond m)
updateCond (C.Or   cond1 cond2)    m = T.Or (updateCond cond1 m) (updateCond cond2 m)
updateCond (C.And  cond1 cond2)    m = T.And (updateCond cond1 m) (updateCond cond2 m)
updateCond (C.CChc _ _ _ )         _ = undefined

-- | translate sql query AST to plain sql string with counter 
transQueryToSql' :: Query -> SqlQuery -> Int -> (SqlQuery, TableAlias, Int )
transQueryToSql' (QueryOp Union l EmptyQuery) p c = 
  let (l', _ ,_) = (transQueryToSql' l p c)
      t = "T" ++ show c
  in (l', t, c+1 )
transQueryToSql' (QueryOp Union EmptyQuery r) p c = 
  let (r', _ ,_) = transQueryToSql' r p c
      t = "T" ++ show c
  in (r', t, c+1 )
transQueryToSql' (QueryOp Union l r) p c = 
  let (l', pl ,cl) = transQueryToSql' l p c
      (r', _, _) = transQueryToSql' r pl cl
      q = buildQuery ["( ", l', " )", " UNION ", "( ", r', " ) "]
      t = "T" ++ show c
  in (q, t, c+2 )
transQueryToSql' (QueryOp Prod l r) p c = 
  let t = "T" ++ show c
      (pl,_,cl) = transQueryToSql' l p (c+1)
      (pr,_,cr) = transQueryToSql' r pl cl   
  in ((buildQuery [" (SELECT * ", " FROM ", pl, " , ", pr, " ) "]), t, cr)
transQueryToSql' (Select attrList q) p c =
  let t =  "T" ++ show c 
      (p',_,c') = transQueryToSql' q p (c+1)
  in ((buildQuery [" SELECT ", prettyAttrList attrList, " FROM ", p']), t, c')
transQueryToSql' (Where Nothing q) p c  = transQueryToSql' q p c 
transQueryToSql' (Where (Just cond) q) p c  =   
  let t = "T" ++ show c 
      (p',_ ,c') = transQueryToSql' q p c
  in (buildQuery [ "( ", p' , " WHERE ", prettyCond cond, " )", " as ", t], t, c'+1)
transQueryToSql' (From r) _ c = 
  let t = "T" ++ show c 
  in (buildQuery [" SELECT * ", " FROM ",relationName r], t, c+1)
transQueryToSql' (EmptyQuery) p c              = (" ", p , c )  
transQueryToSql' (QueryOp Diff _ _) _ _              = undefined

transQueryToSql :: Query -> SqlQuery
transQueryToSql q = let (a,_,_) = transQueryToSql' q " " 0
                    in a

-- | lift the a from *opt a* 
lift :: Opt a  -> a  
lift (_,a)= a 

-- | build a list of string into Query clause
buildQuery :: [String] -> String 
buildQuery list = filter (/= '\n') $ unlines list

-- | pretty print the condition in module target
prettyCond :: T.Condition -> QueryClause
prettyCond (T.Lit  b)            = show b
prettyCond (T.Comp compOp a1 a2) = prettyAtom a1 ++ prettyCompOp compOp ++ prettyAtom a2
prettyCond (T.Not  cond)         = buildQuery [" NOT ",  (prettyCond cond)]
prettyCond (T.Or   cond1 cond2)  = buildQuery [(prettyCond cond1), " OR ",  (prettyCond cond2)]
prettyCond (T.And  cond1 cond2)  = buildQuery [(prettyCond cond1), " AND ",  (prettyCond cond2)]
prettyCond (T.SAT  f)            = buildQuery ["SAT(" , F.prettyFeatureExpr f , ")"]

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
t0 =  (Relation "taughtby")
t1 = (Relation "courselevel")
a1 = Attribute "course"
a2 = Attribute "professor"
f0 = (Feature "US")
f1 = (Feature "C")
cond1 = (C.Comp GT (C.Attr a1) (C.Val (I 5)))

q1 = Select [a1,a2] $ From t0 
q2 = Select [a1,a2] $ QueryOp Prod (From t0 ) (From t1)

q3 = Select [a1,a2] $ Where (Just (T.Comp GT (C.Attr a1) (C.Val (I 5))) ) $ From t0 
e_4 = Proj [(F.Ref (Feature {featureName = "A"}),a1)] $ Sel cond1 $ (TRef t0)
q4 = Select [a1,a2] $ Where (Just (T.SAT (F.Ref f0 ))) $ From t0 

w1 = Where (Just (T.SAT (F.Ref f0 ))) $ From t0 

e1 = SetOp Prod (TRef "r1") (TRef "r2")

e2 = Proj [(F.And 
                    (F.Ref (Feature "A")) 
                    (F.Ref (Feature "B")), 
                   Attribute "a1")
                 ,
                  (F.Ref (Feature "C"),
                   Attribute "a2")
                 ] 
          (TRef "Table1")

alist = [(F.And 
                    (F.Ref (Feature "A")) 
                    (F.Ref (Feature "B")), 
                   Attribute "a1")
                 ,
                  (F.Ref (Feature "C"),
                   Attribute "a2")
                 ]

e3 =  Proj [(F.And 
                    (F.Ref (Feature "A")) 
                    (F.Ref (Feature "B")), 
                   Attribute "a1")
                 ,
                  (F.Ref (Feature "B"),
                   Attribute "a2")
                 ] 
          (SetOp Prod 
                (AChc (F.Ref (Feature " FB")) 
                      (TRef (Relation "r1")) 
                       Empty) 
                (AChc (F.Ref (Feature "FC")) 
                            (TRef (Relation "r2")) 
                             Empty))
achc =            (AChc (F.Ref (Feature " FB")) 
                      (TRef (Relation "r1")) 
                       Empty)


e4 = Proj [((F.Lit True),a1)] (Sel cond2 (TRef t0))

cond2 = C.CChc (F.Ref f1) (C.Comp GT (C.Attr a1) (C.Val (I 5))) (C.Comp LT (C.Attr a1) (C.Val (I 5)))

test1 =  Proj [(F.Lit True, 
                   Attribute "a1")
               ,(F.Lit True,
                   Attribute "a2")
               ] 
          (TRef "Table1") 

test2 = Proj [(F.Lit True, Attribute "a1")] $ 
            Sel (C.Comp GT 
                  (C.Attr (Attribute "a1")) 
                  (C.Val (I 5))) $ 
            (TRef (Relation "Table2"))

test3 = Proj [(F.Lit True, Attribute "a1")] $ 
            Sel (C.CChc (F.Ref (Feature "F"))
                       (C.Comp GT (C.Attr a1) (C.Val (I 5))) 
                       (C.Comp LT (C.Attr a1) (C.Val (I 5)))) $ 
            (TRef (Relation "Table2"))

test3_sub = (AChc (F.Ref (Feature " FB")) 
                      (TRef (Relation "r1")) 
                       Empty) 
test4 = AChc (F.Ref (Feature  "F")) 
             (Proj [(F.Lit True, Attribute "a1")] (TRef (Relation "Table2"))) 
             (Proj [(F.Lit True, Attribute "a1")] (TRef (Relation "Table2")))

fexpr = Feature "F"

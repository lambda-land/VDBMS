module VDB.AlgebraToSql where 

-- import VDB.Target 
-- import VDB.SQL 
-- import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import VDB.Variational
-- import VDB.Value

import Database.HDBC
-- import Database.HDBC.PostgreSQL

type QueryClause = String 

-- | select attributelist, relationlist, condition in plain string 
querySFW :: String -> String -> String -> QueryClause  
querySFW al rl cond = if length cond == 0 
                    then buildQuery ["SELECT ", al , " FROM ",rl ]
                    else buildQuery ["SELECT ", al , " FROM ",rl , " WHERE ", cond ]

-- | build a list of string into Query clause
buildQuery :: [String] -> QueryClause
buildQuery list = filter (/= '\n') $ unlines list

-- | transfer sql value to string 
sqlRowToString = map (fromSql :: SqlValue -> String)


main :: IO ()
main = do 
        conn <- connectPostgreSQL "host=localhost dbname=ai_db"
        result <- quickQuery conn (querySFW "*" "taughtby" "") []
        mapM_ print $ map sqlRowToString result

--
-- ** Variational relational algebra.
--

data SetOp = Union | Diff | Prod
   deriving(Show)


data Algebra
   = Proj  [Opt Attribute] (Maybe C.Condition) Relations 
   | AChc  F.FeatureExpr Algebra Algebra  
   deriving(Show)

data Relations  
    = TRef  Relation
    | SetOp SetOp Relations Relations
    | Empty
     deriving(Show)

lift :: Opt a  -> a  
lift (_,a)= a 

data Query = Nested SetOp Query Query 
           | Select [Attribute] [Relation] (Maybe C.Condition)
  deriving (Show)
-- tran1 = transAlgebraToSql $ Proj [(F.Ref "f1","A1"),(F.Ref "f2","A2")] Nothing (SetOp Prod (TRef "relation1") (TRef "relation2"))

transAlgebraToSql :: Algebra -> Query  
transAlgebraToSql (Proj oplist cond (TRef r)) = Select (map lift oplist) [r] cond 
transAlgebraToSql (Proj oplist cond p)        = Select (map lift oplist) (transProduct p) cond                          
transAlgebraToSql (AChc _      a1   a2)       = Nested Union (transAlgebraToSql a1) (transAlgebraToSql a2)

transProduct :: Relations -> [Relation]
transProduct (TRef r)           = [r]
transProduct (SetOp Prod r1 r2) = transProduct r1 ++ transProduct r2 
transProduct Empty              = []





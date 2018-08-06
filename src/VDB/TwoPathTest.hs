module VDB.TwoPathTest where 

import VDB.AlgebraToSql
import VDB.Config
import VDB.Algebra
import VDB.Variational 

import qualified Data.Map as Map

import Database.HDBC hiding (run)
import Database.HDBC.PostgreSQL

import Test.QuickCheck 
import Test.QuickCheck.Monadic

-- | configuration from Vquery to Query 
--   used in the path1: Vquery --> Query --> SQL --> Result 
configFromVQuery ::  Config Bool -> Algebra -> Query 
configFromVQuery c (SetOp op a1 a2)   = QueryOp op (configFromVQuery c a1) (configFromVQuery c a2) 
configFromVQuery c (Proj attrlist a)  = Select (configureOptList c attrlist) (configFromVQuery c a)  
configFromVQuery c (Sel   cond a)     = Where (Just (updateCond  (configure c cond) Map.empty)) (configFromVQuery c a)  
configFromVQuery c achc@(AChc _ _ _)  = configFromVQuery c $ configure c achc
configFromVQuery _ (TRef  r)          = From r 
configFromVQuery _ (Empty)            = EmptyQuery

type QResult =  [[SqlValue]]
type VQResult = [[SqlValue]]

configFromVResult :: Config Bool -> IO VQResult -> IO QResult 
configFromVResult = undefined 

queryDB :: SqlQuery -> IO [[SqlValue]]
queryDB sqlQ = do
                 conn <- connectPostgreSQL "host=localhost dbname=ai_db"
                 result <- quickQuery conn sqlQ []
                 return result 
                 -- mapM_ print $ map sqlRowToString result

queryVDB :: SqlQuery -> IO [[SqlValue]]
queryVDB sqlQ = do
                 conn <- connectPostgreSQL "host=localhost dbname=vai_db"
                 result <- quickQuery conn sqlQ []
                 return result 
                 -- mapM_ print $ map sqlRowToString result

-- | Property1:
prop_twoPath_equal algebra config = monadicIO $ do
    let sqlQ  = transQueryToSql $ configFromVQuery config algebra  
    l <- run $ queryDB sqlQ 
    let vsqlQ = translate algebra
        vrel  = queryVDB vsqlQ     
    r <- run $ configFromVResult config vrel                        
    assert (l == r )

qc_main = quickCheck prop_twoPath_equal

-- data Algebra
--    = SetOp SetOp Algebra Algebra
--    | Proj  [Opt Attribute] Algebra
--    | Sel   Condition Algebra
--    | AChc  FeatureExpr Algebra Algebra
--    | TRef  Relation
--    | Empty 
--   deriving (Data,Eq,Show,Typeable,Ord)
instance Arbitrary Algebra where
  -- arbitrary = oneof []

instance Arbitrary (Config a) where 
  -- arbitrary = undefined 








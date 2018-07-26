module VDB.TwoPathTest where 

import VDB.AlgebraToSql
import VDB.Config
import VDB.Algebra
import VDB.Variational 

import qualified Data.Map as Map 

-- | configuration from Vquery to Query 
--   used in the path1: Vquery --> Query --> SQL --> Result 
configFromVQuery ::  Config Bool -> Algebra -> Query 
configFromVQuery c (SetOp op a1 a2)   = QueryOp op (configFromVQuery c a1) (configFromVQuery c a2) 
configFromVQuery c (Proj attrlist a)  = Select (configureOptList c attrlist) (configFromVQuery c a)  
configFromVQuery c (Sel   cond a)     = Where (Just (updateCond  (configure c cond) Map.empty)) (configFromVQuery c a)  
configFromVQuery c achc@(AChc _ _ _)  = configFromVQuery c $ configure c achc
configFromVQuery _ (TRef  r)          = From r 
configFromVQuery _ (Empty)            = EmptyQuery



module VDB.Example.EmployeeUseCase.EmployeeVQuery where

import VDB.Algebra
import qualified VDB.Condition as C
import VDB.Example.EmployeeUseCase.EmployeeQuery
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Type
import VDB.Variational 

import Database.HDBC 
import Prelude hiding (EQ, NEQ, LT ,LTE ,GTE,GT)


-- | push the gaven featureExpr to plain algebra(query) and get a v-algebra(V-query)
-- pushFeatureToAlgebra :: FeatureExpr -> Algebra -> Algebra
-- pushFeatureToAlgebra f (SetOp op l r)  = undefined
-- pushFeatureToAlgebra f (Proj  alist a) = undefined
-- pushFeatureToAlgebra f (Sel   cond  a) = undefined
-- pushFeatureToAlgebra f (AChc  v  l  r) = undefined
-- pushFeatureToAlgebra f r@(TRef  rel)   = r
-- pushFeatureToAlgebra f  Empty          = Empty

--
-- ** small test suite
--

testq1,testq2 :: Algebra
-- SELECT A1 FROM T1
testq1 = Proj [ plainAttr "A1" ] $ TRef (Relation "T1")
-- SELECT A2 FROM T1 Where A2 > 5
testq2 = Proj [plainAttr "A2"] $ Sel cond $ TRef (Relation "T1")
		where cond = C.Comp GT (C.Attr (Attribute "A2")) (C.Val (SqlInt32 5))
-- SELECT 



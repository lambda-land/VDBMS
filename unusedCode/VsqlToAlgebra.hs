-- | translation from V-SQL Query to Variational Relational Algebra
module VDBMS.QueryTrans.VsqlToAlgebra where 

import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import VDB.Variational


-- | Translate variational SQL into Variational relational algebra
vsqlToAlgebra :: VQuery -> Algebra 
vsqlToAlgebra (VSelect as rs Nothing)     = Proj as $ transRelationList rs
vsqlToAlgebra (VSelect as rs (Just cond)) = Proj as $ Sel cond $ transRelationList rs
vsqlToAlgebra (QChc f l r)                = AChc f (vsqlToAlgebra l) (vsqlToAlgebra r) 

-- | A helper function to translate RealtionList to the version of Algebra
transRelationList :: [(F.FeatureExpr, Relation)]-> Algebra
transRelationList []     = Empty
-- transRelationList [x]    = SetOp Prod (transOptRelation x) Empty  -- ?
transRelationList (x:xs) = SetOp Prod (transOptRelation x) (transRelationList xs)  

-- | A helper function to translate Relation to the version of Algebra
transOptRelation :: Opt Relation -> Algebra
transOptRelation (f,r) = if f == (F.Lit True) 
                         then TRef r
                         else AChc f (TRef r) Empty 

optRel = (F.Lit True, Relation "Table1")

 

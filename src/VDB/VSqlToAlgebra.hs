module VDB.VSqlToAlgebra where 

import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import VDB.Variational
import VDB.Value


-- | Translate variational SQL into Variational relational algebra
vsqlToAlgebra :: VQuery -> Algebra 
vsqlToAlgebra (Select as rs Nothing)     = Proj as $ transRelationList rs
vsqlToAlgebra (Select as rs (Just cond)) = Proj as $ Sel cond $ transRelationList rs
vsqlToAlgebra (QChc f l r)               = AChc f (vsqlToAlgebra l) (vsqlToAlgebra r) 

-- | A helper function to translate RealtionList to the version of Algebra
transRelationList :: RelationList -> Algebra
transRelationList []     = Empty
transReltaionList (x:xs) = SetOp Prod (transOptRelation x) (transRelationList xs)  

-- | A helper function to translate Relation to the version of Algebta
transOptRelation :: Opt Relation -> Algebra
transOptRelation (f,r) = if f == (F.Lit True) 
                         then TRef r
                         else AChc f (TRef r) Empty 




 

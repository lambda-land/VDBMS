module VDB.SqlToAlgebra where 

import VDB.SQL 
import VDB.Algebra
import VDB.Name
import VDB.FeatureExpr


-- | Comments: 
-- | 1. should we consider the subquery? such as EXIST, ANY, IN
--

-- | translate variational SQL into Variational relational algebra
sqlToAlgebra :: Query -> Algebra 
sqlToAlgebra (Select as rs Nothing)     = Proj as $ TRef rs 
sqlToAlgebra (Select as rs (Just cond)) = Proj as $ Sel cond $ TRef rs
sqlToAlgebra (QChc f l r)               = AChc f (sqlToAlgebra l) (sqlToAlgebra r) 

    
-- sqlToAlgebra $ (Select [((And (Ref (Feature { featureName = "A" }) ) (Ref (Feature { featureName = "A" }) )),(Attribute { attributeName = "1" })), ((Ref (Feature { featureName = "B" })),(Attribute { attributeName = "2" }))] [((Ref (Feature { featureName=" B" })),(Relation { relationName = "1" })), ((Ref (Feature { featureName = "C" })),( Relation { relationName = "2" }))]) Nothing





 

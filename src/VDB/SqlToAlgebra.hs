module VDB.SqlToAlgebra where 

import VDB.SQL 
import VDB.Algebra
import VDB.Name
import VDB.FeatureExpr
import VDB.Variational

-- | Comments: 
-- | 1. should we consider the subquery? such as EXIST, ANY, IN
--

-- | translate variational SQL into Variational relational algebra
sqlToAlgebra :: Query -> Algebra 
sqlToAlgebra (Select as rs Nothing)     = Proj as $ transRelationList rs
sqlToAlgebra (Select as rs (Just cond)) = Proj as $ Sel cond $ transRelationList rs
sqlToAlgebra (QChc f l r)               = AChc f (sqlToAlgebra l) (sqlToAlgebra r) 

    


transRelationList :: RelationList -> Algebra
transRelationList []     = Empty
transRelationList (x:xs) = SetOp Prod (transOptRelation x) (transRelationList xs)  

transOptRelation :: Opt Relation -> Algebra
transOptRelation (f,r) = AChc f (TRef r) Empty 

-- | sqlToAlgebra $ (Select [((And (Ref (Feature { featureName = "A" }) ) 
--                                 (Ref (Feature { featureName = "f1" }) )),
--                              (Attribute { attributeName = "a1" })), 
--                           ((Ref (Feature { featureName = "f2" })),
--                              (Attribute { attributeName = "a2" }))] 
--                          [((Ref (Feature { featureName="f3" })),
--                              (Relation { relationName = "r1" })), 
--                           ((Ref (Feature { featureName = "f4" })),
--                              ( Relation { relationName = "r2" }))]) 
--                    Nothing

-- | Proj [(A∧f1,Attribute {attributeName = "a1"}),(f2,Attribute {attributeName = "a2"})] 
--   (SetOp Prod (AChc f3 (TRef (Relation {relationName = "r1"})) Empty) 
--          (SetOp Prod (AChc f4 (TRef (Relation {relationName = "r2"})) Empty) Empty))




 

module VDB.VSqlToAlgebra where 

import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import VDB.Variational
import VDB.Value

-- | Comments: 
-- | 1. should we consider the subquery? such as EXIST, ANY, IN
--

-- | translate variational SQL into Variational relational algebra
vsqlToAlgebra :: Query -> Algebra 
vsqlToAlgebra (Select as rs Nothing)     = Proj as $ transRelationList rs
vsqlToAlgebra (Select as rs (Just cond)) = Proj as $ Sel cond $ transRelationList rs
vsqlToAlgebra (QChc f l r)               = AChc f (vsqlToAlgebra l) (vsqlToAlgebra r) 

-- | A helper function to translate RealtionList to the version of Algebra
transRelationList :: RelationList -> Algebra
transRelationList []     = Empty
transRelationList (x:xs) = SetOp Prod (transOptRelation x) (transRelationList xs)  

-- | A helper function to translate Relation to the version of Algebta
transOptRelation :: Opt Relation -> Algebra
transOptRelation (f,r) = if f == (F.Lit True) 
                         then TRef r
                         else AChc f (TRef r) Empty 

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




 

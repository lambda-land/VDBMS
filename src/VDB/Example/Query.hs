module VDB.Example.Query where

import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import qualified VDB.Value as V

import VDB.VSqlToAlgebra 

-- | Basic compolent for Queryies 
fA :: F.FeatureExpr 
fA = F.Ref (Feature "A")
fB = F.Ref (Feature "B")
fTrue = F.Lit True
fFalse = F.Lit False

attr1 :: Attribute
attr1 = Attribute "a1"
attr2 = Attribute "a2"

rel1 :: Relation 
rel1 = Relation "Table1"
rel2 = Relation "Table2"

-- |
-- | ** Examples for Variational Query 
-- | 

-- Vquery without condition and feature Expr included 
vq1 :: VQuery 
vq1 = VSelect [(fTrue, attr1), (fTrue, attr2)] 
              [(fTrue, rel1)] 
              Nothing

-- VQuery with featureExpr included 
vq2 :: VQuery
vq2 = VSelect [(fA, attr1), (fB, attr2)] 
              [(fTrue, rel1)] 
              Nothing 

vq3 :: VQuery
vq3 = VSelect [(fA, attr1), (fB, attr2)]
              [(fA, rel1)] Nothing
-- VQuury with featureExpr and condition included
vq4 :: VQuery
vq4 = VSelect [(fA, attr1), (fB, attr2)] 
              [(fA, rel1)] 
              (Just (C.Comp V.GT (C.Attr attr1) (C.Val (V.I 5))) )

-- VQuury with featureExpr and condition included
vq5 :: VQuery
vq5 = VSelect [(fA, attr1), (fB, attr2)] 
              [(fA, rel1),(fB, rel2)] 
              Nothing












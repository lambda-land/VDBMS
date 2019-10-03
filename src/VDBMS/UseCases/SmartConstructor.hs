 -- | Example Queries upon an employee data base
module VDBMS.UseCases.SmartConstructor where

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.UseCases.EmployeeUseCase.EmployeeSchema
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.CompOp
import Prelude hiding (Ordering(..))

-- 
-- * Smart Constructors
--

-- | attaches the feature expression true to an attribute. 
trueAttr :: Attr -> OptAttribute
trueAttr a = (F.Lit True, genRenameAttr a)

genRenameAlgebra :: Algebra -> Rename Algebra
genRenameAlgebra alg = Rename Nothing alg

genRenameRelation :: Relation -> Rename Relation
genRenameRelation rel = Rename Nothing rel

tRef :: Relation -> Algebra 
tRef rel = TRef $ Rename Nothing rel 

joinTwoRelation :: Relation -> Relation -> Attr -> Algebra
joinTwoRelation rel1 rel2 commonAttr = Join (genRenameAlgebra (tRef rel1)) (genRenameAlgebra (tRef rel2)) join_cond
  where join_cond = C.Comp EQ (C.Att (qualifiedAttr rel1 commonAttr)) (C.Att (qualifiedAttr rel2 commonAttr))

-- | Join three relation(a,b,c) based on commonAttr. 
--   (rel1 join(rel1.commonAttr = rel2.commonAttr) rel2) join(rel1.commonAttr = rel3.commonAttr) rel3
joinThreeRelation :: Relation -> Relation -> Relation -> Attr -> Algebra
joinThreeRelation rel1 rel2 rel3 commonAttr = Join (genRenameAlgebra (joinTwoRelation rel1 rel2 commonAttr)) (genRenameAlgebra (tRef rel3)) cond 
  where cond = C.Comp EQ (C.Att (qualifiedAttr rel1 commonAttr)) (C.Att (qualifiedAttr rel3 commonAttr))

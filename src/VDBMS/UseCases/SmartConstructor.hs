 -- | Example Queries upon an employee data base
module VDBMS.UseCases.SmartConstructor where

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.CompOp
import Prelude hiding (Ordering(..))
import qualified Data.Map as M 
import VDBMS.DBMS.Value.Value
import VDBMS.Variational.Opt
import qualified VDBMS.VDB.Name as N
import VDBMS.VDB.Schema.Variational.Schema

newtype QueryT = QueryT String
  deriving (Show, Eq)

-- 
-- * Smart Constructors for Query
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

joinTwoRelation :: Relation -> Relation -> N.Name -> Algebra
joinTwoRelation rel1 rel2 commonAttr = Join (genRenameAlgebra (tRef rel1)) (genRenameAlgebra (tRef rel2)) join_cond
  where join_cond = C.Comp EQ (C.Att (qualifiedAttr rel1 commonAttr)) (C.Att (qualifiedAttr rel2 commonAttr))

-- | Join three relation(a,b,c) based on commonAttr. 
--   (rel1 join(rel1.commonAttr = rel2.commonAttr) rel2) join(rel1.commonAttr = rel3.commonAttr) rel3
joinThreeRelation :: Relation -> Relation -> Relation -> N.Name -> Algebra
joinThreeRelation rel1 rel2 rel3 commonAttr = Join (genRenameAlgebra (joinTwoRelation rel1 rel2 commonAttr)) (genRenameAlgebra (tRef rel3)) cond 
  where cond = C.Comp EQ (C.Att (qualifiedAttr rel1 commonAttr)) (C.Att (qualifiedAttr rel3 commonAttr))

--
-- * Smart Constructor for Schema
--

-- | Gaven a relation name and generate a relation without alias 
genRelation :: N.Name -> N.Rename N.Relation
genRelation relName  =  N.Rename Nothing (N.Relation relName)

-- | Gaven a attribute name and return a Attr with no Qualifier
attr :: N.Name -> N.Attr 
attr n = N.Attr (N.Attribute n) Nothing 

-- | Gaven a attribute name (a) and return a Attr with Qualifier (rel)
qualifiedAttr :: N.Relation -> N.Name -> N.Attr
qualifiedAttr rel a = N.Attr (N.attribute (attr a)) (Just (N.RelQualifier rel))

genQualifiedAttrList :: [(N.Relation, N.Name)] -> [N.Attr] 
genQualifiedAttrList = map $ \(rel,a) -> qualifiedAttr rel a

-- | Generate Rename Attr
genRenameAttr :: N.Attr -> N.Rename N.Attr
genRenameAttr att = N.Rename Nothing $ att

-- | Generate Rename Attrs
genRenameAttrList:: [N.Attr] -> [N.Rename N.Attr]
genRenameAttrList = map genRenameAttr 

-- | Genrate Rename Attr with qualifier
genQualifiedRenameAttr :: N.Name -> N.Attr -> N.Rename N.Attr
genQualifiedRenameAttr rel att = N.Rename Nothing $ N.Attr (N.attribute att) (Just (N.RelQualifier (N.Relation rel)))

-- | Genrate Rename Attrs with qualifier
genQualifiedRenameAttrList :: [(N.Name, N.Attr)] -> [N.Rename N.Attr]
genQualifiedRenameAttrList = map $ \(rel,a) -> genQualifiedRenameAttr rel a

-- | contruct plain relation schema without tag assigned based on a list of [(Relation, [Attribute, Sqltype])] 
constructRelMap :: [(N.Relation, [(N.Attribute, SqlType)])] -> M.Map N.Relation (Opt RowType) 
constructRelMap nrlist = M.fromList $ map (\(relName, rt) -> ( relName, (F.Lit True, constructRowType rt))) nrlist

-- | contruct rowType based on a list of [(Attribute, SqlType)]
constructRowType ::  [(N.Attribute,SqlType)]  -> RowType
constructRowType attrTypeList  = M.fromList  $ map (\(a, t) -> (a, (F.Lit True, t))) attrTypeList

-- | contruct plain Schema with assigned tag based on a list of v-relation
constructOptRelMap :: [(F.FeatureExpr, N.Relation, [(F.FeatureExpr, N.Attribute, SqlType)])] -> M.Map N.Relation (Opt RowType) 
constructOptRelMap nrlist = M.fromList $ map (\(f , relName, rt) -> ( relName, (f, constructOptRowType rt))) nrlist

-- | contruct rowType based on a list of [(Attribute, SqlType)]
constructOptRowType ::  [(F.FeatureExpr, N.Attribute,SqlType)]  -> RowType
constructOptRowType attrTypeList  = M.fromList  $ map (\(f, a, t) -> (a, (f, t))) attrTypeList

constructAllTrueRelSchema :: [(String, SqlType)] -> [(F.FeatureExpr, N.Attribute, SqlType)] 
constructAllTrueRelSchema  =  map (\ (a, t) -> (F.Lit True, N.Attribute a, t))

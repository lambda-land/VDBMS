 -- | Example Queries upon an employee data base
module VDBMS.QueryLang.RelAlg.Variational.SmartConstructor where

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
import VDBMS.VDB.Schema.Relational.Types

-- newtype QueryT = QueryT String
--   deriving (Show, Eq)

-- 
-- * Smart Constructors for Query
--

project :: OptAttributes -> Algebra -> Algebra
project as q = Proj as q

att2optatt :: Attribute -> F.FeatureExpr -> OptAttribute
att2optatt a f = mkOpt f (att2attr a)

-- | attaches the feature expression true to an attribute. 
trueAttr :: Attribute  -> OptAttribute
trueAttr a = att2optatt a (F.Lit True) 

trueAttrQualRel :: Attribute -> Relation -> OptAttribute
trueAttrQualRel a r = att2optattQualRel a r (F.Lit True) 

trueAttrQual :: Attribute -> Name -> OptAttribute
trueAttrQual a n = att2optattQualRel a n (F.Lit True) 

att2optattQual :: Attribute -> Name -> F.FeatureExpr -> OptAttribute
att2optattQual a n f = mkOpt f (att2attrQual a n)

att2optattQualRel :: Attribute -> Relation -> F.FeatureExpr -> OptAttribute
att2optattQualRel a r f = mkOpt f (att2attrQualRel a r)

att2attr :: Attribute -> Attr 
att2attr a = Attr a Nothing

att2attrQual :: Attribute -> Name -> Attr
att2attrQual a n = Attr a (Just (SubqueryQualifier n))

att2attrQualRel :: Attribute -> Relation -> Attr
att2attrQualRel a r = Attr a (Just (RelQualifier r))

select :: VsqlCond -> Algebra -> Algebra
select c q = Sel c q

eqAttrsSqlCond :: Attr -> Attr -> VsqlCond
eqAttrsSqlCond a1 a2 = VsqlCond $ C.Comp EQ (C.Att a1) (C.Att a2)

eqAttrsCond :: Attr -> Attr -> C.Condition
eqAttrsCond a1 a2 = C.Comp EQ (C.Att a1) (C.Att a2)

eqAttsSqlCond :: Attribute -> Attribute -> VsqlCond
eqAttsSqlCond a1 a2 = VsqlCond $ C.Comp EQ (C.Att $ att2attr a1) (C.Att $ att2attr a2)

eqAttValSqlCond :: Attribute -> SqlValue -> VsqlCond 
eqAttValSqlCond a v = VsqlCond $ C.Comp EQ (C.Att $ att2attr a) (C.Val v)

eqAttrValSqlCond :: Attr -> SqlValue -> VsqlCond 
eqAttrValSqlCond a v = VsqlCond $ C.Comp EQ (C.Att a) (C.Val v)

choice :: F.FeatureExpr -> Algebra -> Algebra -> Algebra
choice f q1 q2 = AChc f q1 q2

joinTwoRels :: Relation -> Relation -> Attribute -> Algebra
joinTwoRels r1 r2 a = Join (tRef r1) (tRef r2) 
  (joinEqCond (att2attrQualRel a r1) (att2attrQualRel a r2))
  -- where
  --   joinEqCond :: Relation -> Relation -> Attribute -> Condition
  --   joinEqCond l r at =  C.Comp EQ (C.Att $ att2attrQualRel at l) 
  --                                  (C.Att $ att2attrQualRel at r)

joinEqCond :: Attr -> Attr -> Condition
joinEqCond a1 a2 = C.Comp EQ (C.Att a1) (C.Att a2)

-- joinThreeRels :: Relation -> Relation -> Relation -> Attribute -> Algebra
-- joinThreeRels r1 r2 r3 a = 
--   Join (renameQ "temp" $ joinTwoRels r1 r2 a) (tRef r3) 
--     (joinEqCond )

joinTwoRelsRename :: Relation -> Name -> Relation -> Name -> Attribute -> Algebra
joinTwoRelsRename r1 n1 r2 n2 a = 
  Join (renameQ n1 $ tRef r1) (renameQ n2 $ tRef r2) (joinCond n1 n2 a)
    where
      joinCond l r at = C.Comp EQ (C.Att $ att2attrQual a l)
                                  (C.Att $ att2attrQual a r)

joinRename :: Algebra -> Name -> Algebra -> Name -> C.Condition -> Algebra
joinRename q1 n1 q2 n2 c = Join (renameQ n1 q1) (renameQ n2 q2) c

join :: Algebra -> Algebra -> Condition -> Algebra
join = Join

-- | creates join condition from an attribute.


-- genRenameRelation :: Relation -> Rename Relation
-- genRenameRelation rel = Rename Nothing rel

tRef :: Relation -> Algebra 
tRef rel = TRef rel 

-- tRefNoRename :: Relation -> Rename Algebra
-- tRefNoRename rel = Rename Nothing (TRef rel)

-- | Gaven a alias and algebra and generate a algebra with alias 
renameQ :: N.Name -> Algebra -> Algebra
renameQ alias algebra  =  RenameAlg alias algebra


-- | join two realtiaon based on their common attribute
-- joinTwoRelation :: Relation -> Relation -> N.Name -> Algebra
-- joinTwoRelation rel1 rel2 commonAttr = undefined
-- Join (genRenameAlgebra (tRef rel1)) (genRenameAlgebra (tRef rel2)) join_cond
 --  where join_cond = C.Comp EQ (C.Att (qualifiedAttr rel1 commonAttr)) (C.Att (qualifiedAttr rel2 commonAttr))

-- | generate subquery 
-- genRenameAlgebra :: Algebra -> Rename Algebra
-- genRenameAlgebra alg = Rename Nothing alg

-- | Gaven a attribute name (a) and return a Attr with Qualifier (rel)
-- subqueryQualifiedAttr :: N.Name -> N.Name -> N.Attr
-- subqueryQualifiedAttr subq a = N.Attr (N.attribute (attr a)) (Just (N.SubqueryQualifier subq))

-- | Join three relation(a,b,c) based on commonAttr. 
--   (rel1 join(rel1.commonAttr = rel2.commonAttr) rel2) join(rel1.commonAttr = rel3.commonAttr) rel3
joinThreeRelation :: Relation -> Relation -> Relation -> N.Name -> Algebra
joinThreeRelation rel1 rel2 rel3 commonAttr = undefined
-- Join (genRenameAlgebra (joinTwoRelation rel1 rel2 commonAttr)) (genRenameAlgebra (tRef rel3)) cond 
 --  where cond = C.Comp EQ (C.Att (qualifiedAttr rel1 commonAttr)) (C.Att (qualifiedAttr rel3 commonAttr))

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

-- | Smart Constructor For Pure Relational Schema
constructRTable :: [(N.Attribute, SqlType)] -> RTableSchema
constructRTable = M.fromList  

constructRSchema ::  [(N.Relation, [(N.Attribute, SqlType)])] -> RSchema
constructRSchema nrlist = M.fromList $ map (\(relName, at) -> ( relName, constructRTable at)) nrlist

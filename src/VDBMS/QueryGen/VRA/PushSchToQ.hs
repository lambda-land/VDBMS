-- | pushs the vschema onto the query so that
--   configuring a query without passing the schema
--   would result in the correct relational query.
module VDBMS.QueryGen.VRA.PushSchToQ (

       pushSchToQ

)where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.VDB.Name
import VDBMS.VDB.GenName
import VDBMS.Variational.Opt (getFexp, getObj)
import VDBMS.Features.FeatureExpr.FeatureExpr

-- import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Maybe (isJust)

-- | pushes the schema onto the vq after type checking 
--   the query. in order for the commuting diagram to
--   hold.
pushSchToQ :: Schema -> Algebra -> Algebra
pushSchToQ s (SetOp o l r) 
  = SetOp o (pushSchToQ s l) (pushSchToQ s r) 
pushSchToQ s (Proj as rq) = undefined
  -- = Proj () (renameMap (pushSchToQ s) rq)
pushSchToQ s (Sel c rq) 
  = Sel (pushSchToCond s c) (renameMap (pushSchToQ s) rq)
pushSchToQ s (AChc f l r) 
  = AChc f (pushSchToQ s l) (pushSchToQ s r)
pushSchToQ s (Join rl rr c) 
  = Join (renameMap (pushSchToQ s) rl) (renameMap (pushSchToQ s) rr) c
pushSchToQ s (Prod rl rr) 
  = Prod (renameMap (pushSchToQ s) rl) (renameMap (pushSchToQ s) rr)
pushSchToQ s q@(TRef rr) 
  = Proj (relSchToOptAtts (thing rr) s) (renameNothing q)
pushSchToQ _ Empty = Empty


-- | takes a relation and schema and generates
--   the list of optattributes of the relationschema
--   in the schema. 
relSchToOptAtts :: Relation -> Schema -> OptAttributes
relSchToOptAtts r s =
  case (lookupTableSch r s) of
    (Just tsch) -> tsch2optAtts r fm tsch
    _ -> error "q has been type checked! not possible! relSchToOptAtts func in PushSchToQ!"
  where 
    fm = featureModel s

-- | takes a relation, the feature model and table schema and 
--   produces the opt attribute list from them.
--   Note that it qualifies all attributes by the relation name.
tsch2optAtts :: Relation -> FeatureExpr -> TableSchema -> OptAttributes
tsch2optAtts r fm tsch = oas
  where
    rf = getFexp tsch
    row = getObj tsch
    oas = map (\(a,f) -> (conjFexp [fm,rf,f], 
                          renameNothing (Attr a (Just (RelQualifier r)))))
      $ M.toList $ M.map getFexp row  

-- | 
pushSchToOptAtts :: Schema -> OptAttributes -> OptAttributes
pushSchToOptAtts = undefined

-- | pushes schema to vsqlcond.
pushSchToCond :: Schema -> VsqlCond -> VsqlCond
pushSchToCond _ cnd@(VsqlCond _) = cnd
pushSchToCond s (VsqlIn a q)     = VsqlIn a (pushSchToQ s q)
pushSchToCond s (VsqlNot c)      = VsqlNot (pushSchToCond s c)
pushSchToCond s (VsqlOr l r) 
  = VsqlOr (pushSchToCond s l) (pushSchToCond s r)
pushSchToCond s (VsqlAnd l r) 
  = VsqlAnd (pushSchToCond s l) (pushSchToCond s r)
pushSchToCond s (VsqlCChc f l r) 
  = VsqlCChc f (pushSchToCond s l) (pushSchToCond s r)


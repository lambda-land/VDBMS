-- | pushs the vschema onto the query so that
--   configuring a query without passing the schema
--   would result in the correct relational query.
-- Instead of defining new helpers, we could have
-- used the type system.
-- This is referred to as constraining the query 
-- by schema in our vldb paper.
module VDBMS.QueryGen.VRA.PushSchToQ (

       pushSchToQ

)where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.VDB.Name
import VDBMS.VDB.GenName
import VDBMS.Variational.Opt (getFexp, getObj)
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.TypeSystem.Variational.TypeSystem (typeOfQuery, typeEnve2OptAtts)

-- import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Maybe (isJust, fromJust)

-- | pushes the schema onto the vq after type checking 
--   the query. in order for the commuting diagram to
--   hold.
pushSchToQ :: Schema -> Algebra -> Algebra
pushSchToQ s (SetOp o l r) 
  = SetOp o (pushSchToQ s l) (pushSchToQ s r) 
pushSchToQ s (Proj as q) 
  = Proj (intersectOptAtts as' as) subq 
    where subq = pushSchToQ s q
          as' = typeEnve2OptAtts $ fromJust $ typeOfQuery subq (featureModel s) s
pushSchToQ s (Sel c q) 
  = Sel (pushSchToCond s c) (pushSchToQ s q)
pushSchToQ s (AChc f l r)  
  = AChc f (pushSchToQ s l) (pushSchToQ s r)
pushSchToQ s (Join l r c) 
  = Join (pushSchToQ s l) (pushSchToQ s r) c
pushSchToQ s (Prod l r) 
  = Prod (pushSchToQ s l) (pushSchToQ s r)
pushSchToQ s q@(TRef r) = Proj as q
  where as = typeEnve2OptAtts $ fromJust $ typeOfQuery q (featureModel s) s
pushSchToQ s (RenameAlg n q) = RenameAlg n (pushSchToQ s q)
pushSchToQ _ Empty = Empty


-- | takes a relation and schema and generates
--   the list of optattributes of the relationschema
--   in the schema. 
-- relSchToOptAtts :: Relation -> Schema -> OptAttributes
-- relSchToOptAtts r s =
--   case lookupTableSch r s of
--     Just tsch -> tsch2optAtts r fm tsch
--     _ -> error "q has been type checked! not possible! relSchToOptAtts func in PushSchToQ!"
--   where 
--     fm = featureModel s

-- | takes a relation, the feature model and table schema and 
--   produces the opt attribute list from them.
--   Note that it qualifies all attributes by the relation name or 
--   the alias if available.
-- tsch2optAtts :: Relation -> F.FeatureExpr -> TableSchema -> OptAttributes
-- tsch2optAtts r fm tsch = 
--   case r of 
--   Just n -> map (\(a,f) -> (F.conjFexp [fm,rf,f], 
--                             renameNothing (Attr a (Just (SubqueryQualifier n)))))
--             $ M.toList $ M.map getFexp row  
--   _ -> oas
--   where
--     rf = getFexp tsch
--     row = getObj tsch
--     oas = map (\(a,f) -> (F.conjFexp [fm,rf,f], 
--                           renameNothing (Attr a (Just (RelQualifier (thing rr))))))
--       $ M.toList $ M.map getFexp row  

-- | returns the outermost opt atts of a query, 
--   knowing that the passed query definitely has a projected list
--   and it is type correct.
-- outerMostOptAttQ :: Algebra -> OptAttributes
-- outerMostOptAttQ = undefined
-- outerMostOptAttQ (SetOp _ l _) = outerMostOptAttQ l
-- outerMostOptAttQ (Proj as _)   = as 
-- outerMostOptAttQ (Sel _ rq)    = outerMostOptAttQ $ thing rq
-- outerMostOptAttQ (AChc f l r) 
--   = unionOptAtts oal oar
--     where
--       oal = pushFexp2OptAtts f (outerMostOptAttQ l) 
--       oar = pushFexp2OptAtts (F.Not f) (outerMostOptAttQ r)
-- outerMostOptAttQ (Join rl rr _) 
--   = outerMostOptAttQ (thing rl) ++ outerMostOptAttQ (thing rr)
-- outerMostOptAttQ (Prod rl rr)
--   = outerMostOptAttQ (thing rl) ++ outerMostOptAttQ (thing rr)
-- outerMostOptAttQ (RenameAlg n q) = undefined
-- outerMostOptAttQ _
--   = error "doesnt have a list of projected atts"

-- | unions two opt atts. 
-- unionOptAtts :: OptAttributes -> OptAttributes -> OptAttributes
-- unionOptAtts = (++)

-- | intersects two opt atts. the first list subsumes the second one,
--   checked by the type system. it returns attributes in the subsumed
--   list with their fexp conjuncted with the correspondent fexps 
--   (disjuncted if more than one) in the
--   bigger list (the first one). if the attr has qualifier in the 
--   subsumed list it is only matched with attributes with the same
--   qualifier, otherwise it is matched with all attributes with 
--   the same name. 
--   Note it needs to look into the first list completely
--                  subsumes      -> isSubsumed    -> intersection
intersectOptAtts :: OptAttributes -> OptAttributes -> OptAttributes
intersectOptAtts big small = map (restrictOptAtt big) small
  where
    restrictOptAtt :: OptAttributes -> OptAttribute -> OptAttribute
    restrictOptAtt oas oa = conjFexpOptAttr (genFexp oasFiltered) oa
      where 
        att = attrOfOptAttr oa 
        qual = qualOfOptAttr oa 
        oasFiltered = filter check oas 
        check a = case qual of 
          Just aq -> qual == qualOfOptAttr a && att == attrOfOptAttr a 
          _ -> att == attrOfOptAttr a
        genFexp :: OptAttributes -> F.FeatureExpr
        genFexp [] = error "shouldnt be getting empty list. func: intersectOptAtts in PushSchToQ"
        genFexp (x:xs) = foldl (\f at -> F.Or f (getFexp at)) (getFexp x) xs

-- | pushes schema to vsqlcond which pushes the schema into the
--   query used in sqlin condition.
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


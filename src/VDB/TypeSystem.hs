module VDB.TypeSystem where 

import VDB.Algebra 
import Prelude hiding (EQ,LT , GT)
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import VDB.Variational
import VDB.Schema
import VDB.SAT
import VDB.Type
import VDB.Config
import VDB.VqueryConfigSem

-- import Data.Map(Map)
import qualified Data.Map as M 
-- import qualified Data.Map.Internal as IM
-- import qualified Data.Map.Lazy as LM
import qualified Data.Map.Strict as SM
import qualified Data.Map.Merge.Strict as StrictM


--import Data.Traversable

-- import Control.Monad.State
-- import Control.Monad (liftM2)

-- import Data.Set(Set) 
import qualified Data.Set as Set 

-- import Data.List((\\),nub)

-- import Data.Maybe(catMaybes)


type VariationalContext = F.FeatureExpr

-- type TypeEnv = RowType
type TypeEnv' = TableSchema

--
-- * static semantics of variational conditions:
--   based on inference rules in the PVLDB paper 
--
typeOfVcond :: C.Condition -> VariationalContext -> TypeEnv' -> Bool
typeOfVcond (C.Lit True)     _ _ = True
typeOfVcond (C.Lit False)    _ _ = True
typeOfVcond (C.Comp _ l r)   ctx env@(envf,envr) = case (l, r) of 
  (C.Attr a, C.Val v)  -> case lookupAttFexpTypeInRowType a envr of 
                            Just (f',t') -> tautology (F.imply ctx (F.And envf f')) &&
                              typeOf v == t'
                            _ -> False
  (C.Attr a, C.Attr a') -> case (lookupAttFexpTypeInRowType a envr, lookupAttFexpTypeInRowType a' envr) of 
                            (Just (f',t'), Just (f'',t'')) | t' == t'' -> tautology (F.imply ctx (F.And envf f'))
                                                                        && tautology (F.imply ctx (F.And envf f''))
                            _ -> False
  _ -> False
typeOfVcond (C.Not c)      ctx env = typeOfVcond c ctx env
typeOfVcond (C.Or l r)     ctx env = typeOfVcond l ctx env && typeOfVcond r ctx env
typeOfVcond (C.And l r)    ctx env = typeOfVcond l ctx env && typeOfVcond r ctx env
typeOfVcond (C.CChc d l r) ctx env = typeOfVcond l (F.And ctx d) env 
  && typeOfVcond r (F.And ctx (F.Not d)) env

-- | check commuty diagram for type system.
typeCommutyDiagram :: [Config Bool] -> VariationalContext -> Schema -> Algebra -> Bool
typeCommutyDiagram cs ctx s vq = foldr (&&) True (map (typeDiagram_c ctx s vq) cs)
  where
    typeDiagram_c ctx s vq c = case (vEnv,env_c) of
      (Just env, Just envc) -> vEnv_c == envc
        where vEnv_c = configureTypeEnv env c
      (Nothing, _) -> error "the vq isn't type correct!"
      (Just _, Nothing) -> error "sth went terribly wrong when checking type diagram!!"
      where 
        vEnv = typeOfVquery' vq ctx s 
        q_c = configureVquery vq c 
        env_c = typeOfVquery' q_c (F.Lit True) s 

-- | applies a config to a type env.
configureTypeEnv :: TypeEnv' -> Config Bool -> TypeEnv'
configureTypeEnv = flip appConfRowType' 


-- | verifies and similifies the final type env return by the type system, i.e.,
--   checks the satisfiability of all attributes' pres conds conjoined
--   with table pres cond.
-- SHRINK!!!
verifyTypeEnv :: TypeEnv' -> Maybe TypeEnv'
verifyTypeEnv env 
  | satisfiable (getFexp env) = Just $ propagateFexpToTsch env
  | otherwise = Nothing

-- 
-- static semantics that returns a table schema,
-- i.e. it includes the fexp of the whole table!
-- 
typeOfVquery' :: Algebra -> VariationalContext -> Schema -> Maybe TypeEnv'
typeOfVquery' (SetOp Union q q') ctx s = case (typeOfVquery' q ctx s, typeOfVquery' q' ctx s) of 
  (Just t, Just t') | typeEq (appFexpTableSch ctx t) (appFexpTableSch ctx t') -> Just t
  _ -> Nothing
typeOfVquery' (SetOp Diff q q')  ctx s = case (typeOfVquery' q ctx s, typeOfVquery' q' ctx s) of 
  (Just t, Just t') | typeEq (appFexpTableSch ctx t) (appFexpTableSch ctx t') -> Just t
  _ -> Nothing
typeOfVquery' (SetOp Prod q q')  ctx s = case (typeOfVquery' q ctx s, typeOfVquery' q' ctx s) of 
  (Just t, Just t') -> Just (typeProduct t t')
  _ -> Nothing
typeOfVquery' (Proj as q)        ctx s = case typeOfVquery' q ctx s of 
  Just t' -> case typeProj as t' of 
    Just t | typeSubsume t t' -> Just $ appFexpTableSch ctx t'
  _ -> Nothing
typeOfVquery' (Sel c q)          ctx s = case typeOfVquery' q ctx s of
  Just env | typeOfVcond c ctx env -> Just $ appFexpTableSch ctx env
  _ -> Nothing
typeOfVquery' (AChc d q q')      ctx s = case (typeOfVquery' q (F.And ctx d) s, typeOfVquery' q' (F.And ctx (F.Not d)) s) of 
  (Just t, Just t') -> Just $ mkOpt (F.Or (getFexp t) (getFexp t')) $ rowTypeUnion (getObj t) (getObj t')
  _ -> Nothing
typeOfVquery' (TRef r)           ctx s = case lookupRowType r s of 
  Just t | tautology (F.imply ctx $ getFexp t) -> Just $ appFexpTableSch ctx t
  _ -> Nothing
typeOfVquery' Empty              ctx _ = Just $ appFexpTableSch ctx $ mkOpt (F.Lit True) M.empty
-- mkOpt f M.empty

-- | applies the ctx to the table schema.
--   it drops the attributes that (f_A and ctx and f_R) is unsatisfiable.
--   but it doesn't update the pres cond of attributes. it only
--   updates the pres cond of the table.
-- appCtxTableSch :: FeatureExpr -> TypeEnv' -> TypeEnv'
-- appCtxTableSch = appFexpTableSch

--
-- * static semantics of variational queires
--   based on inference rules in the PVLDB paper
--   f<q,q'> case: note that it doesen't have duplicate attributes
--
-- typeOfVquery :: Algebra -> VariationalContext -> Schema -> Maybe TypeEnv
-- typeOfVquery (SetOp Union q q') f s = case (typeOfVquery q f s, typeOfVquery q' f s) of 
--   (Just t, Just t') | typeEq (cxtAppType f t) (cxtAppType f t') -> Just t
--   _ -> Nothing
-- typeOfVquery (SetOp Diff q q')  f s = case (typeOfVquery q f s, typeOfVquery q' f s) of 
--   (Just t, Just t') | typeEq (cxtAppType f t) (cxtAppType f t') -> Just t
--   _ -> Nothing
-- typeOfVquery (SetOp Prod q q')  f s = case (typeOfVquery q f s, typeOfVquery q' f s) of 
--   (Just t, Just t') -> Just (typeProduct t t')
--   _ -> Nothing
-- typeOfVquery (Proj as q)        f s = case typeOfVquery q f s of 
--   Just t' -> case typeProj as t' of 
--     Just t | typeSubsume t t' -> Just (cxtAppType f t')
--   _ -> Nothing
-- typeOfVquery (Sel c q)          f s = case typeOfVquery q f s of
--   Just t | typeOfVcond c f t -> Just (cxtAppType f t)
--   _ -> Nothing
-- typeOfVquery (AChc d q q')      f s = case (typeOfVquery q (F.And f d) s, typeOfVquery q' (F.And f (F.Not d)) s) of 
--   (Just t, Just t') -> Just (typeUnion (cxtAppType (F.And f d) t) (cxtAppType (F.And f (F.Not d)) t'))
--   _ -> Nothing
-- typeOfVquery (TRef r)           f s = case lookupRowType r s of 
--   Just (f',t) | tautology (F.imply f f') -> Just (cxtAppType f t)
--   _ -> Nothing
-- typeOfVquery Empty              _ _ = Just M.empty



-- | context appication to type enviornment
-- cxtAppType :: VariationalContext -> TypeEnv'-> TypeEnv'
-- cxtAppType f r = undefined
-- SM.map (\(f',t) -> ((F.And f f'),t)) r

-- | Type enviornment equilvanecy, checks that the vCtxt are 
--   equivalent, both env have the same set of attributes,
--   and attributes fexp are equivalent
typeEq :: TypeEnv'-> TypeEnv'-> Bool
typeEq lenv renv = equivalent (getFexp lenv) (getFexp renv) 
  && getRowTypeAtts (getObj lenv) == getRowTypeAtts (getObj renv) 
  && SM.isSubmapOfBy (\(o,t) (o',t') -> t == t' && equivalent o o') (getObj lenv) (getObj renv) 

-- | Type enviornment cross product. does this cause any problem?!?!?
--   specifically adding prefix to attributes!!!
--   any other ideas for updating the keys?!?!?
typeProduct :: TypeEnv'-> TypeEnv'-> TypeEnv'
typeProduct lenv renv = mkOpt (F.Or (getFexp lenv) (getFexp renv)) rt
  where
    rt = M.union unionWithoutIntersection
                           (M.union updatedT updatedT')
    lrowtype = getObj lenv
    rrowtype = getObj renv
    unionWithoutIntersection = StrictM.merge StrictM.preserveMissing 
                                             StrictM.preserveMissing 
                                             matched lrowtype rrowtype
    matched = StrictM.zipWithMaybeMatched (\_ _ _ -> Nothing)
    t  = M.difference lrowtype unionWithoutIntersection
    t' = M.difference rrowtype unionWithoutIntersection
    updatedT  = addPrefix "1." t
    updatedT' = addPrefix "2." t'

-- | aux for type product. adds prefix to attributes of a typeEnv
addPrefix :: String -> RowType -> RowType
addPrefix s r = M.fromList $ map updateAttName l
  where
    updateAttName (a,(o,t)) = (Attribute Nothing (s ++ attributeName a), (o,t))
    l = M.toList r

{-
-- | type enviornment join, when we have the same attribute
--   in both type env we combine their feature expr.
--   add it when you add natural join to your operands!
typeJoin :: TypeEnv -> TypeEnv -> TypeEnv
typeJoin r r' = undefined
  -- SM.unionWith 
  -- (\(o,t) (o',t') -> if t==t' then ((F.And o o'),t) else) r r'
-}

-- | Projects a list of optional attributes from a type env.
--   it updates included attribute's pres cond by the fexp
--   assigned to them in the list. it keeps the pres cond of
--   the whole table the same as before.
typeProj :: [Opt Attribute] -> TypeEnv' -> Maybe TypeEnv'
typeProj ((p,a):pas) env 
  | elem a as = case lookupAttFexpTypeInRowType a $ getObj env of 
                    Just (f,at) -> case typeProj pas env of 
                                     Just t -> Just $ mkOpt (getFexp env) $ M.union (M.singleton a (F.And p f,at)) $ getObj t
                                     _ -> Nothing
                    _ -> Nothing
  | otherwise = Nothing
    where as = getTableSchAtts env 
typeProj [] env = Just $ mkOpt (getFexp env) M.empty

-- | projecting a row type onto another row type,
--   i.e. getting the attributes that exists in the first one from the 
--   second one. it'll check that all attributes in t exists in t'
--   in the typesubsume function. So we're not checking it here again!
typeEnvPrj :: RowType -> RowType -> RowType
typeEnvPrj t t' = M.restrictKeys t as 
  where
    as = M.keysSet $ M.intersection t t'

-- | env is subsumed by env'.
typeSubsume :: TypeEnv' -> TypeEnv' -> Bool
typeSubsume env env' 
  | Set.null (Set.difference at at') && 
    (tautology $ F.imply (getFexp env) (getFexp env')) = M.foldr (&&) True res
  | otherwise = False
    where 
      res = M.intersectionWith implies envObj filteredt'
      -- implies :: (FeatureExpr,Type) -> (FeatureExpr,Type) -> FeatureExpr
      implies (f,_) (f',_) = tautology (F.imply f f')
      filteredt' = typeEnvPrj (M.map (\(f,t) -> (F.And f envFexp,t)) envObj) (M.map (\(f,t) -> (F.And f envFexp',t)) envObj')
      at  = getAttTypeFromRowType envObj
      at' = getAttTypeFromRowType envObj'
      envObj = getObj env
      envFexp = getFexp env
      envObj' = getObj env'
      envFexp' = getFexp env'

                              
-- | union two type. doesn't evaluate the feature expressions.
-- typeUnion :: TypeEnv'-> TypeEnv'-> TypeEnv'
-- typeUnion = undefined
-- 	-- rowTypeUnion


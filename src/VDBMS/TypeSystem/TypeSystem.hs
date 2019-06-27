-- | Statically syntesizes the types of vqs.
module VDBMS.TypeSystem.TypeSystem (

        TypeEnv'
        , VariationalContext
        , typeOfVquery'

) where 

import qualified VDBMS.QueryLang.RelAlg.Variational.Algebra as A
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
-- import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Schema
import VDBMS.Features.SAT
import VDBMS.DBMS.Value.Value
import VDBMS.Features.Config

import Prelude hiding (EQ,LT , GT)
import qualified Data.Map as M 
import qualified Data.Map.Strict as SM
import qualified Data.Map.Merge.Strict as StrictM
import qualified Data.Set as Set 
import Data.Set (Set)

import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Control.Monad.Catch 

type VariationalContext = F.FeatureExpr

-- type TypeEnv = RowType
type TypeEnv' = TableSchema

-- | Errors in type env.
data TypeError = RelationInvalid Relation VariationalContext F.FeatureExpr
  | VcondNotHold A.Condition VariationalContext TypeEnv'
  | DoesntSubsumeTypeEnv TypeEnv' TypeEnv'
  | NotEquiveTypeEnv TypeEnv' TypeEnv' VariationalContext TypeEnv' TypeEnv'
  | AttributeNotInTypeEnv Attribute TypeEnv' (Set Attribute)
  | EnvFexpUnsat F.FeatureExpr TypeEnv'
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception TypeError  

--
-- * static semantics of variational conditions:
--   based on inference rules in the PVLDB paper 
--
typeOfVcond :: A.Condition -> VariationalContext -> TypeEnv' -> Bool
typeOfVcond (A.Lit True)     _ _ = True
typeOfVcond (A.Lit False)    _ _ = True
typeOfVcond (A.Comp _ l r)   ctx env@(envf,envr) = case (l, r) of 
  (A.Attr a, A.Val v)  -> 
    maybe False
          (\ (f',t') -> 
            tautology (F.imply ctx (F.And envf f')) && typeOf v == t') 
          $ lookupAttFexpTypeInRowType a envr
  -- case lookupAttFexpTypeInRowType a envr of 
  --                           Just (f',t') -> tautology (F.imply ctx (F.And envf f')) &&
  --                             typeOf v == t'
  --                           _ -> False
  (A.Attr a, A.Attr a') -> 
    case (lookupAttFexpTypeInRowType a envr, lookupAttFexpTypeInRowType a' envr) of 
                            (Just (f',t'), Just (f'',t'')) | t' == t'' -> tautology (F.imply ctx (F.And envf f'))
                                                                        && tautology (F.imply ctx (F.And envf f''))
                            _ -> False
                                -- maybe False 
    --       (\ ((f',t'), (f'',t'')) ->
    --          t' == t'' 
    --          && tautology (F.imply ctx (F.And envf f'))
    --          && tautology (F.imply ctx (F.And envf f'')))
    --       $ (lookupAttFexpTypeInRowType a envr, lookupAttFexpTypeInRowType a' envr)

  _ -> False
typeOfVcond (A.Not c)      ctx env = typeOfVcond c ctx env
typeOfVcond (A.Or l r)     ctx env = typeOfVcond l ctx env && typeOfVcond r ctx env
typeOfVcond (A.And l r)    ctx env = typeOfVcond l ctx env && typeOfVcond r ctx env
typeOfVcond (A.CChc d l r) ctx env = typeOfVcond l (F.And ctx d) env 
  && typeOfVcond r (F.And ctx (F.Not d)) env 



-- | verifies and similifies the final type env return by the type system, i.e.,
--   checks the satisfiability of all attributes' pres conds conjoined
--   with table pres cond.
-- SHRINK!!!
verifyTypeEnv :: MonadThrow m => TypeEnv' -> m TypeEnv'
verifyTypeEnv env 
  | satisfiable (getFexp env) = return $ propagateFexpToTsch env
  | otherwise = throwM $ EnvFexpUnsat (getFexp env) env

-- 
-- static semantics that returns a table schema,
-- i.e. it includes the fexp of the whole table!
-- 
typeOfVquery' :: MonadThrow m => A.Algebra -> VariationalContext 
                              -> Schema -> m TypeEnv'
typeOfVquery' (A.SetOp A.Union q q') ctx s = 
  do t  <- typeOfVquery' q ctx s
     t' <- typeOfVquery' q' ctx s
     let env  = appFexpTableSch ctx t
         env' = appFexpTableSch ctx t'
     if typeEq env env' 
     then return t
     else throwM $ NotEquiveTypeEnv env env' ctx t t'
typeOfVquery' (A.SetOp A.Diff q q')  ctx s = 
  do t  <- typeOfVquery' q ctx s
     t' <- typeOfVquery' q' ctx s
     let env = appFexpTableSch ctx t
         env' = appFexpTableSch ctx t'
     if typeEq env env'
     then return t 
     else throwM $ NotEquiveTypeEnv env env' ctx t t' 
-- typeOfVquery' (A.Prod r r' rl)  ctx s = undefined
  -- do t  <- typeOfVquery' q ctx s
  --    t' <- typeOfVquery' q' ctx s
  --    return $ typeProduct t t'
typeOfVquery' (A.Proj as q)        ctx s = 
  do t' <- typeOfVquery' q ctx s
     t  <-  typeProj as t'
     if typeSubsume t t'
     then return $ appFexpTableSch ctx t'
     else throwM $ DoesntSubsumeTypeEnv t t'
typeOfVquery' (A.Sel c q)          ctx s = 
  do env <- typeOfVquery' q ctx s
     if typeOfVcond c ctx env 
     then return $ appFexpTableSch ctx env
     else throwM $ VcondNotHold c ctx env
typeOfVquery' (A.AChc d q q')      ctx s = 
  do t <- typeOfVquery' q (F.And ctx d) s
     t' <- typeOfVquery' q' (F.And ctx (F.Not d)) s
     return $ mkOpt (F.Or (getFexp t) (getFexp t')) $ rowTypeUnion (getObj t) (getObj t')
typeOfVquery' (A.TRef r)           ctx s = 
  do t <- lookupRowType r s
     if tautology (F.imply ctx $ getFexp t)
     then return $ appFexpTableSch ctx t
     else throwM $ RelationInvalid r ctx (getFexp t)
typeOfVquery' A.Empty              ctx _ = 
  return $ appFexpTableSch ctx $ mkOpt (F.Lit True) M.empty


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
    updateAttName (a,(o,t)) = (Attribute (s ++ attributeName a), (o,t))
    l = M.toList r


-- | Projects a list of optional attributes from a type env.
--   it updates included attribute's pres cond by the fexp
--   assigned to them in the list. it keeps the pres cond of
--   the whole table the same as before.
typeProj :: MonadThrow m => [Opt Attribute] -> TypeEnv' -> m TypeEnv'
typeProj ((p,a):pas) env 
  | elem a as = 
    do (f,at) <- lookupAttFexpTypeInRowType a $ getObj env
       t <- typeProj pas env
       return $ mkOpt (getFexp env) $ M.union (M.singleton a (F.And p f,at)) $ getObj t
  | otherwise = throwM $ AttributeNotInTypeEnv a env as
    where as = getTableSchAtts env 
typeProj [] env = return $ mkOpt (getFexp env) M.empty

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

                              
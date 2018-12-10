module VDB.TypeSystem.Semantics where 

import VDB.Algebra 
import Prelude hiding (EQ,LT , GT)
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import VDB.Variational
import VDB.Type  
import VDB.Schema
import VDB.Config 
--import VDB.AlgebraToSql
import VDB.SAT

import Data.Map(Map)
import qualified Data.Map as M 
import qualified Data.Map.Internal as IM
-- import qualified Data.Map.Lazy as LM
import qualified Data.Map.Strict as SM
import qualified Data.Map.Merge.Strict as StrictM


--import Data.Traversable

import Control.Monad.State
import Control.Monad (liftM2)

import Data.Set(Set) 
import qualified Data.Set as Set 

import Data.List((\\),nub)

-- import Data.Maybe(catMaybes)


type VariationalContext = F.FeatureExpr

type TypeEnv = RowType
-- type RowType = [Opt (Attribute, Type)]
-- type RowType = Map Attribute (Opt Type)

--
-- * static semantics of variational conditions:
--   based on inference rules in the PVLDB paper 
--
typeOfVcond :: C.Condition -> VariationalContext -> TypeEnv -> Bool
typeOfVcond (C.Lit True)     _ _ = True
typeOfVcond (C.Lit False)    _ _ = True
typeOfVcond (C.Comp _ l r)   f t = case (l, r) of 
  (C.Attr a, C.Val v)  -> case lookupAttFexpInRowType a t of 
                            Just f' -> tautology (F.imply f f')
                            _ -> False
  (C.Attr a, C.Attr a') -> case (lookupAttFexpTypeInRowType a t, lookupAttFexpTypeInRowType a' t) of 
                            (Just (f',t'), Just (f'',t'')) | t' == t'' -> tautology (F.imply f f') 
                                                                        && tautology (F.imply f f'')
                            _ -> False
typeOfVcond (C.Not c)      f t = typeOfVcond c f t
typeOfVcond (C.Or l r)     f t = typeOfVcond l f t && typeOfVcond r f t
typeOfVcond (C.And l r)    f t = typeOfVcond l f t && typeOfVcond r f t
typeOfVcond (C.CChc d l r) f t = typeOfVcond l (F.And f d) t 
  && typeOfVcond r (F.And f (F.Not d)) t


--
-- * static semantics of variational queires
--   based on inference rules in the PVLDB paper
--   f<q,q'> case: note that it doesen't have duplicate attributes
--
typeOfVquery :: Algebra -> VariationalContext -> Schema -> Maybe TypeEnv
typeOfVquery (SetOp Union q q') f s = case (typeOfVquery q f s, typeOfVquery q' f s) of 
  (Just t, Just t') | typeEq (cxtAppType f t) (cxtAppType f t') -> Just t
  _ -> Nothing
typeOfVquery (SetOp Diff q q')  f s = case (typeOfVquery q f s, typeOfVquery q' f s) of 
  (Just t, Just t') | typeEq (cxtAppType f t) (cxtAppType f t') -> Just t
  _ -> Nothing
typeOfVquery (SetOp Prod q q')  f s = case (typeOfVquery q f s, typeOfVquery q' f s) of 
  (Just t, Just t') -> Just (typeProduct t t')
  _ -> Nothing
typeOfVquery (Proj as q)        f s = case typeOfVquery q f s of 
  Just t' -> case typeProj as t' of 
    Just t | typeSubsume t t' -> Just (cxtAppType f t')
  _ -> Nothing
typeOfVquery (Sel c q)          f s = case typeOfVquery q f s of
  Just t | typeOfVcond c f t -> Just (cxtAppType f t)
  _ -> Nothing
typeOfVquery (AChc d q q')      f s = case (typeOfVquery q (F.And f d) s, typeOfVquery q' (F.And f (F.Not d)) s) of 
  (Just t, Just t') -> Just (typeUnion (cxtAppType (F.And f d) t) (cxtAppType (F.And f (F.Not d)) t'))
  _ -> Nothing
typeOfVquery (TRef r)           f s = case lookupRowType r s of 
  Just (f',t) | tautology (F.imply f f') -> Just (cxtAppType f t)
  _ -> Nothing
typeOfVquery Empty              _ _ = Just M.empty

-- | context appication to type enviornment
cxtAppType :: VariationalContext -> TypeEnv -> TypeEnv
cxtAppType f r = SM.map (\(f',t) -> ((F.And f f'),t)) r

-- | Type enviornment equilvanecy, checks that the vCtxt are 
--   equivalent, both env have the same set of attributes,
--   and attributes fexp are equivalent
typeEq :: TypeEnv -> TypeEnv -> Bool
typeEq r r' = getRowTypeAtts r == getRowTypeAtts r' &&
  SM.isSubmapOfBy (\(o,t) (o',t') -> t == t' && equivalent o o') r r'
  -- attTypeEq as as' && equivAttFexp as as' -- OLD


-- ******************************************************************
-- ******************************************************************
-- DISCUSS WITH ERIC IN MEETING!!
-- | Type enviornment cross product. does this cause any problem?!?!?
--   specifically adding prefix to attributes!!!
--   any other ideas for updating the keys?!?!?
typeProduct :: TypeEnv -> TypeEnv -> TypeEnv
typeProduct e e' = M.union unionWithoutIntersection
                           (M.union updatedT updatedT')
  where 
    -- unionWithoutIntersection = M.difference (M.union e e') (M.intersection e e')
    unionWithoutIntersection = StrictM.merge StrictM.preserveMissing 
                                             StrictM.preserveMissing 
                                             matched e e'
    matched = StrictM.zipWithMaybeMatched (\_ _ _ -> Nothing)
    t  = M.difference e unionWithoutIntersection
    t' = M.difference e' unionWithoutIntersection
    updatedT  = addPrefix "1." t
    updatedT' = addPrefix "2." t'
-- ******************************************************************
-- ******************************************************************

-- | aux for type product. adds prefix to attributes of a typeEnv
addPrefix :: String -> TypeEnv -> TypeEnv
addPrefix s r = M.fromList $ map updateAttName l
  where
    updateAttName (a,(o,t)) = (Attribute(s ++ attributeName a), (o,t))
    l = M.toList r

-- | type enviornment join, when we have the same attribute
--   in both type env we combine their feature expr.
--   add it when you add natural join to your operands!
typeJoin :: TypeEnv -> TypeEnv -> TypeEnv
typeJoin r r' = undefined
  -- SM.unionWith 
  -- (\(o,t) (o',t') -> if t==t' then ((F.And o o'),t) else) r r'

-- | Projects a list of optional attributes from a type env
typeProj :: [Opt Attribute] -> TypeEnv -> Maybe TypeEnv
typeProj atts@((p,a):pas) r 
  | let as = getRowTypeAtts r in 
      elem a as = case lookupAttFexpTypeInRowType a r of 
                    Just (f,at) -> case typeProj pas r of 
                                     Just t -> Just $ M.union (M.singleton a (F.And p f,at)) t
                    _ -> Nothing
  | otherwise = Nothing

-- | projecting a type env onto another type env,
--   i.e. getting the attributes that exists in the first one from the 
--   second one. it'll check that all attributes in t exists in t'
--   in the typesubsume function. So we're not checking it here again!
typeEnvPrj :: TypeEnv -> TypeEnv -> TypeEnv
typeEnvPrj t t' = M.restrictKeys t as 
  where
    as = M.keysSet $ M.intersection t t'

-- | t is subsumed by t'. according to the def. in PVLDB paper
typeSubsume :: TypeEnv -> TypeEnv -> Bool
typeSubsume t t' 
  | Set.null (Set.difference at at') = M.foldr (&&) True res
  | otherwise = False
    where 
      res = M.intersectionWith implies t filteredt'
      -- implies :: (FeatureExpr,Type) -> (FeatureExpr,Type) -> FeatureExpr
      implies (f,_) (f',_) = tautology (F.imply f f')
      filteredt' = typeEnvPrj t t'
      at  = getAttTypeFromRowType t
      at' = getAttTypeFromRowType t'

                              
-- | union two type. doesn't evaluate the feature expressions.
typeUnion :: TypeEnv -> TypeEnv -> TypeEnv
typeUnion e e' = StrictM.merge 
                   StrictM.preserveMissing 
                   StrictM.preserveMissing 
                   matched e e'
  where 
    matched = StrictM.zipWithMaybeMatched (\_ (o,t) (o',t') -> 
      case t==t' of
        True -> Just ((F.Or o o'),t)
        _    -> Nothing)



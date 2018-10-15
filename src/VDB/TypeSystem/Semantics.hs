module VDB.TypeSystem.Semantics where 

import VDB.Algebra 
import Prelude hiding (EQ,LT , GT)
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import VDB.Variational
import VDB.Value  
import VDB.Schema
import VDB.Config 
--import VDB.AlgebraToSql
import VDB.SAT

import Data.Map(Map)
import qualified Data.Map as M 
import qualified Data.Map.Internal as IM

--import Data.Traversable

import Control.Monad.State
import Control.Monad (liftM2)

import Data.Set(Set) 
import qualified Data.Set as Set 

import Data.List((\\),nub)

-- import Data.Maybe(catMaybes)


type VariationalContext = F.FeatureExpr

type TypeEnv = RowType


-- | Get an attribute prescence condition from the type env
lookupAttFexpEnv :: Attribute -> TypeEnv -> Maybe F.FeatureExpr
lookupAttFexpEnv a r = case retrieve r a of 
                              Just (f',_) -> Just f'
                              _ -> Nothing

-- | Get an attribute type and presence condition from a type env
lookupAttEnv :: Attribute -> TypeEnv -> Maybe (Opt Type)
lookupAttEnv a r = retrieve r a

--
-- * static semantics of variational conditions:
--   based on inference rules in the PVLDB paper 
--
typeOfVcond :: C.Condition -> VariationalContext -> TypeEnv -> Bool
typeOfVcond (C.Lit True)     _ _ = True
typeOfVcond (C.Lit False)    _ _ = True
typeOfVcond (C.Comp _ l r)   f t = case (l, r) of 
  (C.Attr a, C.Val v)  -> case lookupAttFexpEnv a t of 
                            Just f' -> tautology (F.imply f f')
                            _ -> False
  (C.Attr a, C.Attr a') -> case (lookupAttEnv a t, lookupAttEnv a' t) of 
                            (Just (f',t'), Just (f'',t'')) | t' == t'' -> tautology (F.imply f f') 
                                                                        && tautology (F.imply f f'')
                            _ -> False
typeOfVcond (C.Not c)      f t = typeOfVcond c f t
typeOfVcond (C.Or l r)     f t = typeOfVcond l f t && typeOfVcond r f t
typeOfVcond (C.And l r)    f t = typeOfVcond l f t && typeOfVcond r f t
typeOfVcond (C.CChc d l r) f t = typeOfVcond l (F.And f d) t 
  && typeOfVcond r (F.And f (F.Not d)) t




-- | set the variational context at the beginning
--   to the presence condition of the v-schema
--
initialVarCtxt :: Schema -> VariationalContext
initialVarCtxt (f,_) = f


--
-- * static semantics of variational queires
--   based on inference rules in the PVLDB paper
--   f<q,q'> case: the shrinkTypeUnion removes the duplicate attributes
--                 while the typeUnion keep the duplicates in the order of
--                 the result of each query --> may need to adjust this 
--                 based on the setting to represent the result to the user
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
--  (Just t, Just t') -> Just (typeUnion (cxtAppType (F.And f d) t) (cxtAppType (F.And f (F.Not d)) t'))
  (Just t, Just t') -> Just (shrinkTypeUnion (typeUnion (cxtAppType (F.And f d) t) (cxtAppType (F.And f (F.Not d)) t')))
--  (Just t, _) -> Just t
--  (_, Just t) -> Just t
  _ -> Nothing
typeOfVquery (TRef r)           f s = case lookupRowType r s of 
  Just (f',t) | tautology (F.imply f f') -> Just (cxtAppType f t)
  _ -> Nothing
typeOfVquery Empty              _ _ = Just []


-- | context appication to type enviornment
cxtAppType :: VariationalContext -> TypeEnv -> TypeEnv
cxtAppType f as = map (\(f',(a,t)) -> ((F.And f f'),(a,t))) as
-- cxtAppType f t = M.map (\f' -> F.shrinkFeatureExpr (F.And f f')) t

-- | helper function for typeEq
--   take two rowtypes and makes sure the attribute and types
--   are the same in both rowtypes
attTypeEq :: RowType -> RowType -> Bool
attTypeEq r r' = map snd r == map snd r' 

-- | helper function for typeEq
--   check the equivalency of presence conditions of the same 
--   attributes
--   Assumption: the number and order of attributes are exactly
--   the same in both row types
equivAttFexp :: RowType -> RowType -> Bool
equivAttFexp r r' = foldr (&&) True eqRes
  where 
    eqRes = map (\(f,f') -> equivalent f f') eq
    eq    = zip fr fr' 
    fr    = map fst r 
    fr'   = map fst r'

-- | Type enviornment equilvanecy, checks that the vCtxt are 
--   equivalent, both env have the same set of attributes,
--   and attributes fexp are equivalent
typeEq :: TypeEnv -> TypeEnv -> Bool
typeEq as as' = attTypeEq as as' && equivAttFexp as as'
--  equivalent r r' && 


-- | Type enviornment cross product
typeProduct :: TypeEnv -> TypeEnv -> TypeEnv
typeProduct r r' = r ++ r'
--  (F.And f f', r ++ r')

-- | helper for rowTypePrj
--   unsafe, only use it where you're checking that a is an 
--   element of the rowtype!!
lookupFexpType :: Attribute -> RowType -> (F.FeatureExpr, Type)
lookupFexpType a r = case retrieve r a of 
                       Just (f,t) -> (f,t)


-- | helper function for typeProj
rowTypePrj :: [Opt Attribute] -> RowType -> Maybe RowType
rowTypePrj atts@((p,a):pas) r = case (elem a as, rowTypePrj pas r) of
                                  (True, Just t) -> Just ((F.And p f,(a,at)):t)
  where 
    as     = map snd atts
    (f,at) = lookupFexpType a r
rowTypePrj []               r = Just []

-- | Projects a list of optional attributes from a type env
typeProj :: [Opt Attribute] -> TypeEnv -> Maybe TypeEnv
typeProj atts t = case rowTypePrj atts t of
                        Just t' -> Just t' 
                        _       -> Nothing
--case (elem a as, typeProj pas e) of
--  (True, Just t)  -> Just (f,((F.And p f, a):t))
--  (False, Just t) -> Just t
--  _               -> Nothing
--  where as = map snd atts
--typeProj []          (f,r)   = Just (f,[])

-- | projecting a type env onto another type env,
--   i.e. getting the attributes that exists in the first one from the 
--   second one
typeEnvPrj :: TypeEnv -> TypeEnv -> TypeEnv
typeEnvPrj t t' = filter (\(_,(a,at)) -> elem (a,at) (getAttListFromTypeEnv t)) t'

-- | t is subsumed by t'. according to the def. in PVLDB paper
typeSubsume :: TypeEnv -> TypeEnv -> Bool
typeSubsume t t' | null (at \\ at') = foldr (&&) True subRes
--  if tautology (F.imply f f') then True
--    else False
  where 
    subRes = map (\(f,f') -> tautology (F.imply f f')) sub
    sub    = zip fr fr' 
    fr     = map fst t 
    fr'    = map fst t''
    t''    = typeEnvPrj t t'
    at     = map snd t
    at'    = map snd t'

-- | get the list of attributes and their types from a type env
getAttListFromTypeEnv :: TypeEnv -> [(Attribute,Type)]
getAttListFromTypeEnv ((f,(a,t)):as) = [(a,t)] ++ getAttListFromTypeEnv as
getAttListFromTypeEnv []             = []

-- | get the presence condition of a pair of attribute and its type
--   from a type env
lookupAttTypeFexpEnv :: (Attribute,Type) -> TypeEnv -> Maybe F.FeatureExpr
lookupAttTypeFexpEnv (a,t) ((f,(a',t')):as) = if a==a' && t==t' 
                                              then (Just f) 
                                              else lookupAttTypeFexpEnv (a,t) as
lookupAttTypeFexpEnv _      []              = Nothing


                              
-- | union two type and keep the order of attributes and allow duplicate 
--   attributes. doesn't evaluate the feature expressions
typeUnion :: TypeEnv -> TypeEnv -> TypeEnv
typeUnion e e' = map (\(f,(a,t)) -> case lookupAttTypeFexpEnv (a,t) e' of 
                                      Just f' -> ((F.Or f f'),(a,t))
                                      _       -> (f,(a,t))) e ++
                 map (\(f,(a,t)) -> case lookupAttTypeFexpEnv (a,t) e of 
                                      Just f' -> ((F.Or f' f),(a,t))
                                      _       -> (f,(a,t))) e'


-- | shrinks a type by removing duplicates 
--   duplicates are the pair of (f,(a,t)) that are
--   exactly the same, i.e., the feature expression
--   must be exactly the same propositional formula
--   i.e. it doesn't check for equivalent feature expressions
--   instead it looks for the exact same formulas
shrinkTypeUnion :: TypeEnv -> TypeEnv
shrinkTypeUnion = nub




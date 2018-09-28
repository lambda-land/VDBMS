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
import VDB.AlgebraToSql
import VDB.SAT

import Data.Map(Map)
import qualified Data.Map as M 
import qualified Data.Map.Internal as IM

--import Data.Traversable

import Control.Monad.State
import Control.Monad (liftM2)

import Data.Set(Set) 
import qualified Data.Set as Set 

-- import Data.Maybe(catMaybes)


type VariationalContext = F.FeatureExpr


type TypeEnv = Opt RowType

-- | Get an attribute prescence condition from the type env
lookupAttPresCondInTypeEnv :: Attribute -> TypeEnv -> Maybe F.FeatureExpr
lookupAttPresCondInTypeEnv a (f, r) = case retrieve r a of 
                               Just (f',_) -> Just f'
                               _ -> Nothing

lookupAttPresAndType :: Attribute -> TypeEnv -> Maybe (F.FeatureExpr, Type)
lookupAttPresAndType a (f, r) = case retrieve r a of 
                                  Just (f', (_, t)) -> Just (f', t)
                                  _ -> Nothing

--
-- * static semantics of variational conditions:
--
typeOfVcond :: C.Condition -> (VariationalContext, TypeEnv) -> Bool
typeOfVcond (C.Lit True)      _ = True
typeOfVcond (C.Lit False)     _ = True
typeOfVcond (C.Comp _ l r)   (f, t) = case (l, r) of 
  (C.Attr a, C.Val v)  -> case lookupAttPresCondInTypeEnv a t of 
                            Just f' -> tautology (F.imply f f')
                            _ -> False
  (C.Attr a, C.Attr a') -> case (lookupAttPresAndType a t, lookupAttPresAndType a' t) of 
                             (Just (f',t'), Just (f'',t'')) -> tautology (F.imply f f') && 
                                                               tautology (F.imply f f'') &&
                                                               t' == t''
                             _ -> False
typeOfVcond (C.Not c)      e = typeOfVcond c e
typeOfVcond (C.Or l r)     e = typeOfVcond l e && typeOfVcond r e
typeOfVcond (C.And l r)    e = typeOfVcond l e && typeOfVcond r e
typeOfVcond (C.CChc d l r) (f, t) = typeOfVcond l ((F.And f d), t) && typeOfVcond r ((F.And f (F.Not d)), t)




-- set the variational context at the beginning
--
initialVarCtxt :: Schema -> VariationalContext
initialVarCtxt (f,_) = f

{--
--
-- * static semantics of variational queires
--
typeOfVquery :: Algebra -> VariationalContext -> Schema -> Maybe TypeEnv
typeOfVquery (SetOp Union q q') f s = case (typeOfVquery q f s, typeOfVquery q' f s) of 
  (Just t, Just t') | typeEq (cxtAppType f t) (cxtAppType f t') -> Just t
  _ -> Nothing
typeOfVquery (SetOp Diff q q')  f s = undefined
typeOfVquery (SetOp Prod q q')  f s = undefined
typeOfVquery (Proj as q)        f s = undefined
typeOfVquery (Sel c q)          f s = undefined
typeOfVquery (AChc d q q')      f s = undefined
typeOfVquery (TRef r)           f s = undefined
typeOfVquery Empty              f s = Just (f,[])


-- | context appication to type enviornment
cxtAppType :: VariationalContext -> TypeEnv -> TypeEnv
cxtAppType f (r,as) = (r, map (\(f',(a,t)) -> ((F.And f f'),(a,t))) as) 
-- cxtAppType f t = M.map (\f' -> F.shrinkFeatureExpr (F.And f f')) t

-- | helper function for typeEq
--   take two rowtypes and makes sure the attribute and types
--   are the same in both rowtypes
attTypeEq :: RowType -> RowType -> Bool
attTypeEq r r' = map snd r == map snd r' 

-- | helper function for typeEq
--   check the equivalency of presence conditions of the same 
--   attributes
equivAttPresCond :: RowType -> RowType -> Bool
equivAttPresCond r r' = undefined

-- | type enviornment equilvanecy 
typeEq :: TypeEnv -> TypeEnv -> Bool
typeEq (r,as) (r',as') = equivalent r r' && attTypeEq as as'
--}

--  M.isSubmapOfBy (\f f' -> equivalent f f') t t'
--as : [(f,(a,t))] 
{--
typeOfVquery' :: Algebra -> VariationalContext -> TypeEnv -> Maybe TypeEnv
typeOfVquery' (SetOp Union q q') f s = case (typeOfVquery' q f s, typeOfVquery' q' f s) of 
                                      (Just t, Just t') | typeEq (cxtAppType f t) (cxtAppType f t') == True -> Just t
                                      _ -> Nothing
typeOfVquery' (SetOp Diff q q')  f s = case (typeOfVquery' q f s, typeOfVquery' q' f s) of 
                                      (Just t, Just t') | typeEq (cxtAppType f t) (cxtAppType f t') == True -> Just t
                                      _ -> Nothing
typeOfVquery' (SetOp Prod q q')  f s = case (typeOfVquery' q f s, typeOfVquery' q' f s) of 
                                      (Just t, Just t') ->  typeProd t t'
--                                      ! (conflictValMerge t t') -> Just (M.unionWith t t')
                                      _ -> Nothing
typeOfVquery' (Proj [] q)        f _ = undefined
typeOfVquery' (Proj (a:as) q)    f _ = undefined
typeOfVquery' (Sel c q)          f s = case typeOfVquery' q f s of
                                      Just t | typeOfVcond c (f, t) -> Just (cxtAppType f t)
                                      _ -> Nothing
typeOfVquery' (AChc d q q')      f _ = undefined
typeOfVquery' (TRef r)           f s = case M.lookup (Right r) s of 
                                        Just f' | satisfiable (F.And f f') -> Just (cxtAppType f s)
                                        _ -> Nothing
typeOfVquery' Empty              f s = Just s


-- type enviornment equilvanecy 
typeEq :: TypeEnv -> TypeEnv -> Bool
typeEq t t' = M.isSubmapOfBy (\f f' -> equivalent f f') t t'
typeEq = M.isSubmapOfBy equivalent 

-- type enviornment production
typeProd :: TypeEnv -> TypeEnv -> Maybe TypeEnv
typeProd = unionWithA combineFeatureExprs 

-- | Union two maps, applying some effectful function to duplicates.
unionWithA :: (Applicative f, Ord k) => (k -> a -> a -> f a) -> Map k a -> Map k a -> f (Map k a)
unionWithA f m1 m2 =
  IM.mergeA
    IM.preserveMissing -- Preserve keys found in m1 but not m2
    IM.preserveMissing -- Preserve keys found in m2 but not m1
    (IM.zipWithAMatched f) -- Apply f when keys in both m1 and m2
    m1
    m2

-- helper function for type enviornment production
-- takes two feature exprs and if they're equivalent
-- returns one of them otherwise fails
combineFeatureExprs :: SAT a => k -> a -> a -> Maybe a
combineFeatureExprs _ f f' = case equivalent f f' of 
                             True -> Just f 
                             False -> Nothing

{--conflictValMerge :: TypeEnv -> TypeEnv -> Bool
conflictValMerge = undefined

traverseMaybeMap :: Map (Either Attribute Relation) (Maybe F.FeatureExpr) -> Bool


filterUnion :: (Ord k, SAT a) => (a -> a -> Maybe a) -> Map k a -> Map k a -> Map k (Maybe a)
filterUnion  = (\f f' -> 



typeUnion :: TypeEnv -> TypeEnv -> TypeEnv
typeUnion = M.unionWith (\f f' -> case equivalent f f' of 
                                      True -> f
                                      False )
--}


typesub :: TypeEnv -> TypeEnv -> Bool
typesub t t' = undefined

-- 
-- * dynamic semantics of variational objects:
--

-- | semantics of variational attributes
semOptAttr :: [Opt Attribute] -> Config Bool -> [Attribute]
semOptAttr []        _ = []
semOptAttr as        c = configureOptList c as 

-- | semantics of variational relation
semOptRel :: Opt RowType -> Config Bool -> [(Attribute, Type)]
semOptRel vrel c = case configureOpt c vrel of 
                      Nothing -> []
                      Just rowList -> configureOptList c rowList

-- | semantics of variational Schema
semVsch :: Schema -> Config Bool -> (Map Relation [(Attribute, Type)])
semVsch s@(_,m)  c = case M.null m of 
                         True  -> M.empty
                         _     -> case configureOpt c s of 
                                Just m ->  M.map ((flip semOptRel) c) m
                                Nothing -> M.empty 

-- | Traverse the Map and collect the Just results.
traverseRelMap :: Map Relation (Maybe RowType) -> Map Relation RowType 
traverseRelMap relM = M.mapMaybe (\v -> v) relM   

--}


--
-- * Variational Relational Algebra Validation Semantics / Type System
--

-- | type enviroment is a mapping from variational objects to their presence conditions
-- data Env a = Map Objects a 

-- type RowType = [Opt (Attribute,Type)]

type RowTypeP = [(Attribute, Type)]
type SchemaP = Map Relation RowTypeP

data Objects = TAttr Attribute 
             | TRel  Relation
             | TSch  SchemaP
             deriving (Show, Eq,Ord)

-- type Schema = Opt (Map Relation (Opt RowType))

-- | s: a mapping from objects to presence condition (featureExpr)
-- | result: presence condition (featureExpr)
type Env = StateT (Map Objects F.FeatureExpr) Maybe 

-- | static semantics for V-query
semVquery :: Algebra -> Env Schema
semVquery  (AChc  f l r)       = undefined
semVquery  (SetOp Prod l r)    = undefined 
semVquery  (SetOp Union l r)   = undefined
semVquery  (SetOp Diff l r)    = undefined
semVquery  (Proj  opAttrs a)   = do st <- get
                                    let newAList = map (\(f,a) ->  (TAttr a,f)) opAttrs
                                    let newMap = M.fromList newAList
                                    put $ M.union st newMap 
                                    semVquery a
semVquery  (Sel   cond a)      = undefined
    -- do st <- get 
    --                                 let newMap = semVcond cond 
    --                                 newMap' <- newMap
    --                                 put $ M.union st newMap'
    --                                 semVquery a
semVquery  (TRef  r)           = undefined   
semVquery   Empty              = undefined

-- | static semantics for V-conditions
semVcond :: C.Condition -> Env Schema 
semVcond (C.Lit b)             = undefined
semVcond (C.Comp op a1 a2)     = undefined 
semVcond (C.Not  cond)         = undefined
semVcond (C.Or   cond1 cond2)  = undefined
semVcond (C.And  cond1 cond2)  = undefined
semVcond (C.CChc _ _ _ )       = undefined









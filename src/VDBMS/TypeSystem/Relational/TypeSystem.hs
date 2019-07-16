-- | Statically syntesizes the types of relational queries.
module VDBMS.TypeSystem.Relational.TypeSystem 
(

        RTypeEnv
        , typeOfRQuery

) where 

import qualified Data.Map as M 
import qualified Data.Map.Strict as SM
import qualified Data.Set as Set 
import Data.Set (Set)

import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Control.Monad.Catch 

import VDBMS.VDB.Schema.Relational.Types
import VDBMS.VDB.Schema.Relational.Lookups
import VDBMS.QueryLang.SQL.Condition
import VDBMS.QueryLang.RelAlg.Relational.Algebra
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Core (typeOf)

-- | Relatioanl type enviornment.
type RTypeEnv = RTableSchema

-- | Type enviornment errors.
data RTypeError = 
    RCompInvalid Atom Atom RTypeEnv
  | RNotEquiveTypeEnv RTypeEnv RTypeEnv 
  | RAttributesNotInTypeEnv Attributes RTypeEnv
  | RAttributeNotInTypeEnv Attribute RTypeEnv
  | REmptyAttrList RAlgebra
  | RNotDisjointRels [Relation]
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception RTypeError 

-- | static semantics that returns a relational table schema.
typeOfRQuery :: MonadThrow m => RAlgebra -> RSchema -> m RTypeEnv
typeOfRQuery (RSetOp o l r)    s =
  do typel <- typeOfRQuery l s
     typer <- typeOfRQuery r s
     if typel == typer
     then return typel
     else throwM $ RNotEquiveTypeEnv typel typer
typeOfRQuery (RProj as rq)     s =
  do tq <- typeOfRQuery (thing rq) s
     if null as 
     then throwM $ REmptyAttrList (thing rq)
     else if attsSubTypeEnv as tq
          then return $ SM.restrictKeys tq $ attsSet as
          else throwM $ RAttributesNotInTypeEnv as tq
typeOfRQuery (RSel c rq)       s = 
  do tq <- typeOfRQuery (thing rq) s
     typeOfSqlCond c tq s 
typeOfRQuery (RJoin js)        s = typeOfJoins js s
typeOfRQuery (RProd rl rr rrs) s = 
  do r <- lookupRelation (thing rl) s
     l <- lookupRelation (thing rr) s
     rs <- mapM (flip lookupRelation s . thing) rrs
     if disjointTypeEnvs r l rs 
     then return $ SM.unions $ r : l : rs
     else throwM $ RNotDisjointRels $ fmap thing (rl : rr : rrs)
typeOfRQuery (RTRef rr)        s = lookupRelation (thing rr) s
typeOfRQuery REmpty            _ = return M.empty

-- | Static semantics of relational conditions.
typeOfSqlCond :: MonadThrow m => SqlCond RAlgebra -> RTypeEnv -> RSchema -> m RTypeEnv
typeOfSqlCond (SqlCond c)  t s = typeOfRCondition c t
typeOfSqlCond (SqlIn a q)  t s = 
  do t' <- typeOfRQuery q s
     attInTypeEnv (attribute a) t' 
typeOfSqlCond (SqlNot c)   t s = typeOfSqlCond c t s 
typeOfSqlCond (SqlOr l r)  t s = 
  do typeOfSqlCond l t s
     typeOfSqlCond r t s
typeOfSqlCond (SqlAnd l r) t s = 
  do typeOfSqlCond l t s
     typeOfSqlCond r t s

-- | Checks if the condition is compatible with type env.
typeOfRCondition :: MonadThrow m => RCondition -> RTypeEnv -> m RTypeEnv
typeOfRCondition (RLit b)      t = return t 
typeOfRCondition (RComp _ l r) t = typeOfComp l r t 
typeOfRCondition (RNot c)      t = typeOfRCondition c t
typeOfRCondition (ROr l r)     t = 
  do typeOfRCondition l t
     typeOfRCondition r t
typeOfRCondition (RAnd l r)    t = 
  do typeOfRCondition l t
     typeOfRCondition r t

-- | Checks if the type env is consistent with a comparison condition.
typeOfComp :: MonadThrow m => Atom -> Atom -> RTypeEnv -> m RTypeEnv
typeOfComp a@(Val l)  a'@(Val r)  t 
  | typeOf l == typeOf r = return t 
  | otherwise = throwM $ RCompInvalid a a' t 
typeOfComp a@(Val l)  a'@(Att r) t = 
  do attInTypeEnv (attribute r) t 
     at <- lookupAttrType (attribute r) t
     if typeOf l == at 
     then return t 
     else throwM $ RCompInvalid a a' t
typeOfComp a@(Att l) a'@(Val r)  t = 
  do attInTypeEnv (attribute l) t 
     at <- lookupAttrType (attribute l) t
     if typeOf r == at 
     then return t 
     else throwM $ RCompInvalid a a' t
typeOfComp a@(Att l) a'@(Att r) t = 
  do attInTypeEnv (attribute l) t 
     attInTypeEnv (attribute r) t 
     at  <- lookupAttrType (attribute l) t
     at' <-  lookupAttrType (attribute r) t
     if at == at'
     then return t 
     else throwM $ RCompInvalid a a' t

-- | Checks if the type env includes an attribute.
attInTypeEnv :: MonadThrow m => Attribute -> RTypeEnv -> m RTypeEnv
attInTypeEnv a t 
  | a `Set.member` SM.keysSet t = return t 
  | otherwise                   = throwM $ RAttributeNotInTypeEnv a t

-- | Type of joins. Note that for now joins are only among relations
--   and not queries.
typeOfJoins :: MonadThrow m => RJoins -> RSchema -> m RTypeEnv
typeOfJoins (RJoinTwoTable rl rr c) s = 
  do lt <- typeOfRQuery (RTRef rl) s
     rt <- typeOfRQuery (RTRef rr) s
     typeOfRCondition c (SM.union lt rt)
typeOfJoins (RJoinMore js rr c)     s = 
  do jt <- typeOfJoins js s 
     rt <- typeOfRQuery (RTRef rr) s
     typeOfRCondition c (SM.union jt rt)

-- | Attributes are all included in the type env.
attsSubTypeEnv :: Attributes -> RTypeEnv -> Bool
attsSubTypeEnv as t = attsSet as `Set.isSubsetOf` SM.keysSet t

-- | Checks if a non-empty list of type envs are disjoint or not.
--   Note that since we're adding type envs to the list we know 
--   for a fact that it isn't empty.
disjointTypeEnvs :: RTypeEnv -> RTypeEnv -> [RTypeEnv] -> Bool
disjointTypeEnvs l r ts 
  | SM.keysSet l `Set.disjoint` SM.keysSet r = disjointAll $ l : r : ts
  | otherwise = False
    where
      disjointAll (x : xs) = all (Set.disjoint (SM.keysSet x)) (fmap SM.keysSet xs) 
                             && disjointAll xs
      disjointAll [x]      = True
      disjointAll []       = True






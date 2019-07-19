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
import Data.List (nub)

import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Control.Monad.Catch 

import VDBMS.VDB.Schema.Relational.Types
import VDBMS.VDB.Schema.Relational.Lookups
import VDBMS.QueryLang.SQL.Condition
import VDBMS.QueryLang.RelAlg.Relational.Algebra
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Value (typeOf,SqlType)

-- | Attribute information for relational type env.
data RAttrInfo 
  = RAttrInfo {
      rAttrType :: SqlType
    , rAttrQuals :: Qualifier
    }
 deriving (Data,Ord,Eq,Show,Typeable)

-- | Comprehensive attribute information required for 
--   relational type env.
type RAttrInformation = [RAttrInfo]

-- | Relational type env.
type RTypeEnv = SM.Map Attribute RAttrInformation

-- | Type enviornment errors.
data RTypeError = 
    RCompInvalid Atom Atom RTypeEnv
  | RNotEquiveTypeEnv RTypeEnv RTypeEnv 
  | RAttributesNotInTypeEnv Attributes RTypeEnv
  | RAttributeNotInTypeEnv Attribute RTypeEnv
  | REmptyAttrList RAlgebra
  | RNotUniqueRelAlias [Rename Relation]
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception RTypeError 

-- | static semantics that returns a relational table schema.
typeOfRQuery :: MonadThrow m => RAlgebra -> RSchema -> m RTypeEnv
typeOfRQuery (RSetOp o l r)    s = 
  do tl <- typeOfRQuery l s
     tr <- typeOfRQuery r s
     sameType tl tr 
     return tl
typeOfRQuery (RProj as rq)     s = typeRProj as rq s 
typeOfRQuery (RSel c rq)       s = 
  do derivedQueryOK rq 
     t <- typeOfRQuery (thing rq) s
     let t' = updateNameSpaceREnv t (name rq)
     typeSqlCond c t' s
     return t'
typeOfRQuery (RJoin js)        s = typeJoins js s 
typeOfRQuery (RProd rl rr rrs) s = typeRProd (rl : rr : rrs) s
typeOfRQuery (RTRef rr)        s = typeRRel rr s 
typeOfRQuery REmpty            _ = return M.empty

-- | Determines the type of set operations.
sameType :: MonadThrow m 
           => RTypeEnv -> RTypeEnv 
           -> m ()
sameType tl tr 
  | SM.keysSet tl == SM.keysSet tr = return ()
  | otherwise = throwM $ RNotEquiveTypeEnv tl tr

-- | Determines the type of a relational projection.
typeRProj :: MonadThrow m 
          => Attributes -> Rename RAlgebra -> RSchema
          -> m RTypeEnv
typeRProj = undefined

-- | checks if an attribute is consistent with the type env.
attConsistentType :: MonadThrow m 
                  => Attr -> RTypeEnv
                  -> m ()
attConsistentType = undefined

-- | Checks if the derived query (subquery) is well-typed based on sql.
derivedQueryOK :: MonadThrow m 
               => Rename RAlgebra 
               -> m ()
derivedQueryOK = undefined

-- | checks if the list of attributes to be projected is 
--   ambiguous or not.
ambiguousAtts :: MonadThrow m => Attributes -> m ()
ambiguousAtts = undefined

-- | Checks if the sql condition is consistent with 
--   the relational type env and schema.
typeSqlCond :: MonadThrow m 
            => SqlCond RAlgebra -> RTypeEnv -> RSchema
            -> m ()
typeSqlCond (SqlCond c)  t s = typeRCondition c t
typeSqlCond (SqlIn a q)  t s = typeOfRQuery q s >>= onlyAttrInType a
typeSqlCond (SqlNot c)   t s = typeSqlCond c t s 
typeSqlCond (SqlOr l r)  t s = typeSqlCond l t s >> typeSqlCond r t s
typeSqlCond (SqlAnd l r) t s = typeSqlCond l t s >> typeSqlCond r t s
 
-- | Checks if the attribute is the only attribute of a type env.
--   Helper for the In queries.
onlyAttrInType :: MonadThrow m 
               => Attr -> RTypeEnv
               -> m ()
onlyAttrInType = undefined

-- | Checks if the relational condition is consistent 
--   with the relational type env.
typeRCondition :: MonadThrow m
               => RCondition -> RTypeEnv
               -> m ()
typeRCondition (RLit b)      t = return () 
typeRCondition (RComp _ l r) t = typeComp l r t 
typeRCondition (RNot c)      t = typeRCondition c t
typeRCondition (ROr l r)     t = typeRCondition l t >> typeRCondition r t
typeRCondition (RAnd l r)    t = typeRCondition l t >> typeRCondition r t

-- | Checks if the comparison is consistent with 
--   relational type env.
typeComp :: MonadThrow m
         => Atom -> Atom -> RTypeEnv
         -> m ()
typeComp = undefined

-- | Adjusts a relational type env with a new name.
--   Ie. it adds the name, if possible, to all 
--   attributes qualifiers.
updateNameSpaceREnv :: RTypeEnv -> Alias -> RTypeEnv
updateNameSpaceREnv = undefined

-- | Gives the type of rename joins.
typeJoins :: MonadThrow m 
          => RJoins -> RSchema
          -> m RTypeEnv
typeJoins j@(RJoinTwoTable rl rr c) s = 
  do uniqueRelAlias $ relJoins j
     tl <- typeRRel rl s 
     tr <- typeRRel rr s 
     t <- prodRTypes (pure tl ++ pure tr)
     typeRCondition c t
     return t
typeJoins j@(RJoinMore js rr c)     s = 
  do uniqueRelAlias $ relJoins j
     ts <- typeJoins js s
     tr <- typeRRel rr s
     t <- prodRTypes $ pure ts ++ pure tr
     typeRCondition c t
     return t

-- | Gets the relations/aliases from the joins.
relJoins :: RJoins -> [Rename Relation]
relJoins (RJoinTwoTable rl rr c) = pure rl ++ pure rr 
relJoins (RJoinMore js rr c)     = relJoins js ++ pure rr

-- | Gives the type of cross producting multiple rename relations.
typeRProd :: MonadThrow m 
          => [Rename Relation] -> RSchema
          -> m RTypeEnv
typeRProd rrs s = 
  do uniqueRelAlias rrs 
     ts <- mapM (flip typeRRel s) rrs
     t <- prodRTypes ts
     return $ t

-- | Gets a list of relational type env and product them.
--   i.e., for repeated attributes accumulates the qualifiers.
--   Note that it's ok if the same attributes with different 
--   qualifiers have different types. 
--   You need to make sure that types are disjoint, i.e., you 
--   can't have: t.A and t.A but you can have t.A and r.A.
--   uniqueRelAlias in typeRProd is taking care of this.
--   So while combining lists of attr info for a given attr
--   we don't need to check this anymore.
prodRTypes :: MonadThrow m => [RTypeEnv] -> m RTypeEnv
prodRTypes ts = return $ SM.unionsWith combAttInfos ts

-- | combinees attr informations. 
combAttInfos = (++) 

-- | Checks that table/alias are unique. The relation names or
--   their aliases must be unique.
uniqueRelAlias :: MonadThrow m => [Rename Relation] -> m ()
uniqueRelAlias rrs 
  | nub relNames == relNames = return ()
  | otherwise                = throwM $ RNotUniqueRelAlias rrs
    where
      relNames  = fmap relName rrs
      relName r = maybe (thing r) Relation (name r)

-- maybe :: b -> (a -> b) -> Maybe a -> b
-- | Returns the type of a rename relation.
typeRRel :: MonadThrow m 
          => Rename Relation -> RSchema
          -> m RTypeEnv
typeRRel rr s = 
  do r <- lookupRelation (thing rr) s
     return $ SM.map (sqlType2RAttrInfo rr) r 

-- | Generates a relational attr info from a rename relation and sql type.
--   If a name alias exists for the relation it considers it as the new 
--   name for the sql type, otherwise it attaches the relation name itself
--   to the sqltype.
sqlType2RAttrInfo :: Rename Relation -> SqlType -> RAttrInformation
sqlType2RAttrInfo rel at = pure $ 
  RAttrInfo at 
          $ maybe (RelQualifier (Relation relName))
                  (\n -> RelQualifier (Relation n)) 
                  newName
  where 
    relName = relationName $ thing rel 
    newName = name rel 
  



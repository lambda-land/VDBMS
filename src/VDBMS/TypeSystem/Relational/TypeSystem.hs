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
import VDBMS.DBMS.Value.Value (typeOf,SqlType)

-- | Attribute information for relational type env.
data RAttrInfo 
  = RAttrInfo {
      rAttrType :: SqlType
    , rAttrQuals :: [Qualifier]
    }
 deriving (Data,Ord,Eq,Show,Typeable)

-- | Relatioanl type enviornment.
-- type RTypeEnv = RTableSchema

-- | Relational type env.
type RTypeEnv = M.Map Attribute RAttrInfo

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
  do tl <- typeOfRQuery l s
     tr <- typeOfRQuery r s
     typeRSetOp tl tr 
typeOfRQuery (RProj as rq)     s = typeRProj as rq s 
typeOfRQuery (RSel c rq)       s = 
  do t <- typeOfRQuery (thing rq) s
     let t' = addNameToREnv t (name rq)
     typeSqlCond c t' s
     return t'
typeOfRQuery (RJoin js)        s = typeJoins js s 
typeOfRQuery (RProd rl rr rrs) s = typeRProd (rl : rr : rrs) s
typeOfRQuery (RTRef rr)        s = typeRRel rr s 
typeOfRQuery REmpty            _ = return M.empty

-- | Determines the type of set operations.
typeRSetOp :: MonadThrow m 
           => RTypeEnv -> RTypeEnv 
           -> m RTypeEnv
typeRSetOp = undefined

-- | Determines the type of a relational projection.
typeRProj :: MonadThrow m 
          => Attributes -> Rename RAlgebra -> RSchema
          -> m RTypeEnv
typeRProj = undefined

-- | Checks if the sql condition is consistent with 
--   the relational type env and schema.
typeSqlCond :: MonadThrow m 
            => SqlCond RAlgebra -> RTypeEnv -> RSchema
            -> m ()
typeSqlCond = undefined

-- | Checks if the relational condition is consistent 
--   with the relational type env.
typeRCondition :: MonadThrow m
               => RCondition -> RTypeEnv
               -> m ()
typeRCondition = undefined

-- | Checks if the comparison is consistent with 
--   relational type env.
typeComp :: MonadThrow m
         => Atom -> Atom -> RTypeEnv
         -> m ()
typeComp = undefined

-- | Adjusts a relational type env with a new name.
--   Ie. it adds the name, if possible, to all 
--   attributes qualifiers.
addNameToREnv :: RTypeEnv -> Alias -> RTypeEnv
addNameToREnv = undefined

-- | Gives the type of rename joins.
typeJoins :: MonadThrow m 
          => RJoins -> RSchema
          -> m RTypeEnv
typeJoins = undefined

-- | Gives the type of cross producting multiple rename relations.
typeRProd :: MonadThrow m 
          => [Rename Relation] -> RSchema
          -> m RTypeEnv
typeRProd = undefined

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
sqlType2RAttrInfo :: Rename Relation -> SqlType -> RAttrInfo
sqlType2RAttrInfo rel at = 
  RAttrInfo at 
          $ maybe (pure $ RelQualifier (Relation relName))
                  (\n -> pure $ RelQualifier (Relation n)) 
                  newName
  where 
    relName = relationName $ thing rel 
    newName = name rel 
  



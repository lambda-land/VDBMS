-- | Statically syntesizes the types of relational queries.
module VDBMS.TypeSystem.Relational.TypeSystem 
(

        RTypeEnv
        , typeOfQuery

) where 


-- import qualified VDBMS.QueryLang.RelAlg.Variational.Algebra as A
-- import VDBMS.VDB.Name
-- import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
-- -- import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
-- import VDBMS.Variational.Opt
-- import VDBMS.VDB.Schema.Schema
-- import VDBMS.Features.SAT
-- import VDBMS.DBMS.Value.Value
-- import VDBMS.Features.Config

-- import Prelude hiding (EQ,LT , GT)
import qualified Data.Map as M 
import qualified Data.Map.Strict as SM
-- import qualified Data.Map.Merge.Strict as StrictM
import qualified Data.Set as Set 
import Data.Set (Set)

import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Control.Monad.Catch 

import VDBMS.VDB.Schema.Relational.Types
import VDBMS.VDB.Schema.Relational.Lookups
import VDBMS.QueryLang.RelAlg.Relational.Condition
import VDBMS.QueryLang.RelAlg.Relational.Algebra
import VDBMS.VDB.Name

type RTypeEnv = RTableSchema

-- | Type enviornment errors.
data RTypeError = RRelationInvalid Relation
  | RVcondNotHold RCondition RTypeEnv
  | RDoesntSubsumeTypeEnv RTypeEnv RTypeEnv
  | NotEquiveTypeEnv RTypeEnv RTypeEnv 
  | RAttributeNotInTypeEnv Attribute RTypeEnv (Set Attribute)
  | RNotDisjointRels [Relation]
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception RTypeError  

-- | static semantics of relational conditions
typeOfCond :: RCondition -> RTypeEnv -> Bool
typeOfCond = undefined


-- | static semantics that returns a relational table schema.
typeOfQuery :: MonadThrow m => RAlgebra -> RSchema -> m RTypeEnv
typeOfQuery (RSetOp o l r)    s = undefined
typeOfQuery (RProj as rq)     s = undefined
typeOfQuery (RSel c rq)       s = undefined
typeOfQuery (RJoin js)        s = undefined
typeOfQuery (RProd rl rr rrs) s = 
  do r <- lookupRelation (thing rl) s
     l <- lookupRelation (thing rr) s
     rs <- mapM (flip lookupRelation s . thing) rrs
     if disjointTypeEnvs r l rs 
     then return $ SM.unions $ r : l : rs
     else throwM $ RNotDisjointRels $ fmap thing (rl : rr : rrs)
typeOfQuery (RTRef rr)        s = lookupRelation (thing rr) s
typeOfQuery REmpty            _ = return M.empty


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






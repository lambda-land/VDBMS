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
data RTypeError = -- RRelationInvalid Relation
    RVcondNotHold RCondition RTypeEnv
  | RMismatchTypes RTypeEnv RTypeEnv
  | NotEquiveTypeEnv RTypeEnv RTypeEnv 
  | RAttributeNotInTypeEnv Attributes RTypeEnv
  | RNotDisjointRels [Relation]
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception RTypeError 

-- | static semantics that returns a relational table schema.
typeOfQuery :: MonadThrow m => RAlgebra -> RSchema -> m RTypeEnv
typeOfQuery (RSetOp o l r)    s =
  do typel <- typeOfQuery l s
     typer <- typeOfQuery r s
     if typel == typer
     then return typel
     else throwM $ RMismatchTypes typel typer
typeOfQuery (RProj as rq)     s =
  do tq <- typeOfQuery (thing rq) s
     if attsSubTypeEnv as tq
     then return $ SM.restrictKeys tq $ attsSet as
     else throwM $ RAttributeNotInTypeEnv as tq
typeOfQuery (RSel c rq)       s = undefined
typeOfQuery (RJoin js)        s = typeOfJoins js s
typeOfQuery (RProd rl rr rrs) s = 
  do r <- lookupRelation (thing rl) s
     l <- lookupRelation (thing rr) s
     rs <- mapM (flip lookupRelation s . thing) rrs
     if disjointTypeEnvs r l rs 
     then return $ SM.unions $ r : l : rs
     else throwM $ RNotDisjointRels $ fmap thing (rl : rr : rrs)
typeOfQuery (RTRef rr)        s = lookupRelation (thing rr) s
typeOfQuery REmpty            _ = return M.empty

-- | static semantics of relational conditions
typeOfCond :: RCondition -> RTypeEnv -> Bool
typeOfCond = undefined

-- | 
typeOfJoins :: MonadThrow m => RJoins -> RSchema -> m RTypeEnv
typeOfJoins (RJoinTwoTable rl rr c) = undefined
typeOfJoins (RJoinMore js rr c) = undefined

-- | 
attsSubTypeEnv :: Attributes -> RTypeEnv -> Bool
attsSubTypeEnv as t = attsSet as `Set.isSubsetOf` SM.keysSet t

-- |
attsSet :: Attributes -> Set Attribute
attsSet = Set.fromList . fmap (getAtt . thing) 
  where
    getAtt :: SingleAttr -> Attribute
    getAtt (SingleAttr a) = a 
    getAtt (SingleQualifiedAttr (RelationQualifiedAttr a _)) = a 
    getAtt (SingleQualifiedAttr (SubqueryQualifiedAttr a _)) = a


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






-- | Statically syntesizes the types of vqs.
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
-- import qualified Data.Map.Strict as SM
-- import qualified Data.Map.Merge.Strict as StrictM
-- import qualified Data.Set as Set 
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
typeOfQuery (RProd rl rr rrs) s = undefined
typeOfQuery (RTRef rr)        s = lookupRelation (thing rr) s
typeOfQuery REmpty            _ = return M.empty









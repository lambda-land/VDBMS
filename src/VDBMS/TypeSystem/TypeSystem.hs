-- | Statically syntesizes the types of vqs.
module VDBMS.TypeSystem.TypeSystem (

        TypeEnv
        , VariationalContext
        -- , typeOfVquery

) where 


-- import qualified VDBMS.QueryLang.RelAlg.Variational.Algebra as A
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
-- -- import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
-- import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Schema
-- import VDBMS.Features.SAT
-- import VDBMS.DBMS.Value.Value
-- import VDBMS.Features.Config

-- import Prelude hiding (EQ,LT , GT)
-- import qualified Data.Map as M 
-- import qualified Data.Map.Strict as SM
-- import qualified Data.Map.Merge.Strict as StrictM
-- import qualified Data.Set as Set 
-- import Data.Set (Set)

import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Control.Monad.Catch 

-- | Variational context that the query is living in at the moment.
type VariationalContext = F.FeatureExpr

-- | Variational type env.
type TypeEnv = TableSchema

-- | Errors in type env.
data TypeError 
  = RelationInvalid Relation VariationalContext F.FeatureExpr
  -- | VcondNotHold A.Condition VariationalContext TypeEnv'
  -- | DoesntSubsumeTypeEnv TypeEnv' TypeEnv'
  -- | NotEquiveTypeEnv TypeEnv' TypeEnv' VariationalContext TypeEnv' TypeEnv'
  -- | AttributeNotInTypeEnv Attribute TypeEnv' (Set Attribute)
  -- | EnvFexpUnsat F.FeatureExpr TypeEnv'
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception TypeError  


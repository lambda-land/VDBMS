-- | Statically syntesizes the types of vqs.
module VDBMS.TypeSystem.TypeSystem (

        TypeEnv
        , VariationalContext
        , typeOfVquery

) where 


import VDBMS.QueryLang.RelAlg.Variational.Algebra 
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
-- -- import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Schema
import VDBMS.Features.SAT (equivalent)
-- import VDBMS.DBMS.Value.Value
-- import VDBMS.Features.Config

-- import Prelude hiding (EQ,LT , GT)
import qualified Data.Map as M 
import qualified Data.Map.Strict as SM
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
  | NotSubsumeTypeEnv TypeEnv TypeEnv
  | EmptyListOfAttr Algebra 
  | NotEquiveTypeEnv TypeEnv TypeEnv VariationalContext
  -- | AttributeNotInTypeEnv Attribute TypeEnv' (Set Attribute)
  -- | EnvFexpUnsat F.FeatureExpr TypeEnv'
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception TypeError  

-- 
-- Static semantics of a vquery that returns a table schema,
-- i.e. it includes the fexp of the whole table.
-- 
typeOfVquery :: MonadThrow m 
             => Algebra -> VariationalContext -> Schema 
             -> m TypeEnv
typeOfVquery (SetOp o l r)    ctx s = typeSetOp l r ctx s
typeOfVquery (Proj oas rq)    ctx s = undefined
typeOfVquery (Sel c rq)       ctx s = undefined
typeOfVquery (AChc f l r)     ctx s = undefined
typeOfVquery (Join js)        ctx s = undefined
typeOfVquery (Prod rl rr rrs) ctx s = undefined
typeOfVquery (TRef rr)        ctx s = undefined
typeOfVquery Empty            ctx s = undefined

-- | Determines the type of a projection query.
typeProj :: MonadThrow m 
         => OptAttributes -> Rename Algebra -> VariationalContext -> Schema
         -> m TypeEnv
typeProj oas rq ctx s =
  do t' <- typeOfVquery (thing rq) ctx s 
     if null oas 
     then throwM $ EmptyListOfAttr (thing rq)
     else do t <- typeOptAtts oas t'
             b <- typeSubsume t t'
             appFexpTableSch ctx t 

-- | Projects a list of optional attributes from a type env.
--   it updates included attribute's pres cond by the fexp
--   assigned to them in the list. it keeps the pres cond of
--   the whole table the same as before.
typeOptAtts :: MonadThrow m => OptAttributes -> TypeEnv -> m TypeEnv
typeOptAtts ((p,a):pas) env = undefined
--   | elem a as = 
--     do (f,at) <- lookupAttFexpTypeInRowType a $ getObj env
--        t <- typeOptAtts pas env
--        return $ mkOpt (getFexp env) $ M.union (M.singleton a (F.And p f,at)) $ getObj t
--   | otherwise = throwM $ AttributeNotInTypeEnv a env as
--     where as = getTableSchAtts env 
-- typeOptAtts [] env = return $ mkOpt (getFexp env) M.empty

-- | env is subsumed by env'.
typeSubsume :: MonadThrow m => TypeEnv -> TypeEnv -> m Bool
typeSubsume env env' = undefined
  -- | Set.null (Set.difference at at') && 
  --   (tautology $ F.imply (getFexp env) (getFexp env')) = M.foldr (&&) True res
  -- | otherwise = False
  --   where 
  --     res = M.intersectionWith implies envObj filteredt'
  --     -- implies :: (FeatureExpr,Type) -> (FeatureExpr,Type) -> FeatureExpr
  --     implies (f,_) (f',_) = tautology (F.imply f f')
  --     filteredt' = typeEnvPrj (M.map (\(f,t) -> (F.And f envFexp,t)) envObj) (M.map (\(f,t) -> (F.And f envFexp',t)) envObj')
  --     at  = getAttTypeFromRowType envObj
  --     at' = getAttTypeFromRowType envObj'
  --     envObj = getObj env
  --     envFexp = getFexp env
  --     envObj' = getObj env'
  --     envFexp' = getFexp env'

-- | projecting a row type onto another row type,
--   i.e. getting the attributes that exists in the first one from the 
--   second one. it'll check that all attributes in t exists in t'
--   in the typesubsume function. So we're not checking it here again!
typeEnvPrj :: RowType -> RowType -> RowType
typeEnvPrj t t' = M.restrictKeys t as 
  where
    as = M.keysSet $ M.intersection t t'


-- | Determines the type a set operation query.
typeSetOp :: MonadThrow m 
          => Algebra -> Algebra -> VariationalContext -> Schema 
          -> m TypeEnv
typeSetOp l r ctx s = 
  do tl <- typeOfVquery l ctx s
     tr <- typeOfVquery r ctx s 
     envl <- appFexpTableSch ctx tl 
     envr <- appFexpTableSch ctx tr
     if typeEq envl envr
     then return envr
     else throwM $ NotEquiveTypeEnv envl envr ctx

-- | Type enviornment equilvanecy, checks that the vCtxt are 
--   equivalent, both env have the same set of attributes,
--   and attributes fexp are equivalent
typeEq :: TypeEnv -> TypeEnv-> Bool
typeEq envl envr = equivalent (getFexp envl) (getFexp envr) 
  && getRowTypeAtts (getObj envl) == getRowTypeAtts (getObj envr) 
  && SM.isSubmapOfBy (\(o,t) (o',t') -> t == t' && equivalent o o') 
                     (getObj envl) 
                     (getObj envr) 


-- |


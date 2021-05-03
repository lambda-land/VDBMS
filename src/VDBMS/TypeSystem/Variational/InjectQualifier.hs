-- | Forces the qualifier names to attributes. 
--   note that if an attribute does a qualifier we don't 
--   change it but if it doesn't we add its qualifier and 
--   in this case the attribute must have only one 
--   qualifier in the type enviroment since it has
--   passed the type system (thus a projected attribute
--   isn't ambigious about its qualifier).
module VDBMS.TypeSystem.Variational.InjectQualifier () where

import VDBMS.QueryLang.RelAlg.Variational.Algebra 
import VDBMS.TypeSystem.Variational.TypeSystem
import VDBMS.VDB.Name 
-- import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
-- import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Variational.Schema
-- import VDBMS.Features.SAT (equivalent, satisfiable, unsatisfiable)
-- import VDBMS.DBMS.Value.Value

-- import qualified Data.Map as M 
import qualified Data.Map.Strict as SM
-- import qualified Data.Set as Set 
-- import Data.Set (Set)
-- import Data.List (intersect, nub, (\\))

import Data.Maybe (maybe, fromJust, isNothing, isJust)

import Data.Generics.Uniplate.Direct (transform)

-- import Data.Data (Data, Typeable)
-- import GHC.Generics (Generic)

import Control.Monad.Catch 

-- import Debug.Trace

-- | forces the qualifier to their projected attributes.
injectQualifier :: Algebra -> Schema -> PCatt -> Algebra
injectQualifier q s pc 
  | isJust tq = transform attrScopeInQ q
  | otherwise = error "the query is type-ill"
    where 
      tq :: MonadThrow m => m TypeEnv
      tq = runTypeQuery q s 
      attrScopeInQ :: Algebra -> Algebra 
      attrScopeInQ (Proj as q') 
        = Proj (updateAttsQual (flip (flip attrScope (extrctType tq)) pc) as) q'
      attrScopeInQ q' = q'

-- | updates the qualifier of an attribute based on a given type env.
--   note that if the env has more than one info it assumes that it 
--   doesn't have a differencce on which one is used. 
attrScope :: Attr -> TypeEnv -> PCatt -> Attr
attrScope a t pc
  | isPCAttr a pc = a
  | isNothing q && isJust a' = updateAttrQual a (attrQual $ head $ fromJust a')
  | isNothing q && isNothing a' 
    = error ("attrScope. ForceScope. should have had a in t!" ++ show a ++ show t)
  | otherwise = a 
    where 
      q = qualifier a 
      a' = SM.lookup (attribute a) (typeMap t)


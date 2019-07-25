-- | Statically syntesizes the types of vqs.
module VDBMS.TypeSystem.Variational.TypeSystem (

        TypeEnv
        , VariationalContext
        , typeOfQuery

) where 


import VDBMS.QueryLang.RelAlg.Variational.Algebra 
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.QueryLang.RelAlg.Variational.Condition 
import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.Features.SAT (equivalent, tautology, satisfiable)
import VDBMS.DBMS.Value.Value
-- import VDBMS.Features.Config

-- import Prelude hiding (EQ,LT , GT)
import qualified Data.Map as M 
import qualified Data.Map.Strict as SM
-- import qualified Data.Map.Merge.Strict as StrictM
import qualified Data.Set as Set 
import Data.Set (Set)
import Data.List (nub)

import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Control.Monad.Catch 

-- | Variational context that the query is living in at the moment.
type VariationalContext = F.FeatureExpr

-- | Variational attribute information for type env.
data AttrInfo 
  = AttrInfo {
      attrFexp :: F.FeatureExpr
    , attrType :: SqlType
    , attrQual :: Qualifier
    }
 deriving (Data,Ord,Eq,Show,Typeable)

-- | Comprehensive attribute information required for a variaitnoal
--   type env.
type AttrInformation = [AttrInfo]

-- | Variational type env.
-- type TypeEnv = TableSchema

-- | Variational type env.
type TypeEnv = Opt (M.Map Attribute AttrInformation)

-- | Possible typing errors.
data TypeError 
  = IncosistentCtxtWithEnv VariationalContext TypeEnv
  | NotUniqueRelAlias [Rename Relation]
  | InvalidRelRef Relation VariationalContext F.FeatureExpr
  | AttrNotSubsume (Opt (Rename Attr)) TypeEnv
  | EmptyAttrList Algebra 
  | NotEquiveTypeEnv TypeEnv TypeEnv VariationalContext
  | CompInvalid Atom Atom TypeEnv
  | IncompatibleTypes [TypeEnv]
  | NotDisjointTypes [TypeEnv]
  | EnvFexpUnsat F.FeatureExpr TypeEnv
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception TypeError  

-- | verifies and similifies the final type env return by the type system, i.e.,
--   checks the satisfiability of all attributes' pres conds conjoined
--   with table pres cond.
verifyTypeEnv :: MonadThrow m => TypeEnv -> m TypeEnv
verifyTypeEnv t = undefined
  -- | satisfiable (getFexp t) = return $ propagateFexpToTsch t
  -- | otherwise = throwM $ EnvFexpUnsat (getFexp t) t

-- 
-- Static semantics of a vquery that returns a table schema,
-- i.e. it includes the fexp of the whole table.
-- 
typeOfQuery :: MonadThrow m 
             => Algebra -> VariationalContext -> Schema 
             -> m TypeEnv
typeOfQuery (SetOp o l r)    ctx s = typeSetOp l r ctx s 
typeOfQuery (Proj oas rq)    ctx s = typeProj oas rq ctx s
typeOfQuery (Sel c rq)       ctx s = typeSel c rq ctx s
typeOfQuery (AChc f l r)     ctx s = 
  do tl <- typeOfQuery l (F.And ctx f) s 
     tr <- typeOfQuery r (F.And ctx (F.Not f)) s 
     return $ unionChoiceType tl tr
typeOfQuery (Join js)        ctx s = typeJoin js ctx s
typeOfQuery (Prod rl rr rrs) ctx s = typeProd (rl : rr : rrs) ctx s
typeOfQuery (TRef rr)        ctx s = typeRel rr ctx s 
typeOfQuery Empty            ctx s = 
  appCtxtToEnv ctx (mkOpt (F.Lit True) M.empty)

-- | Determines the type a set operation query.
typeSetOp :: MonadThrow m 
          => Algebra -> Algebra -> VariationalContext -> Schema 
          -> m TypeEnv
typeSetOp l r ctx s = 
  do tl <- typeOfQuery l ctx s
     tr <- typeOfQuery r ctx s 
     sameType tl tr 
     return tl

-- | Checks if two type are the same.
sameType :: MonadThrow m => TypeEnv -> TypeEnv -> m ()
sameType = undefined

-- | Type of a projection query.
typeProj :: MonadThrow m 
         => OptAttributes -> Rename Algebra -> VariationalContext -> Schema
         -> m TypeEnv
typeProj = undefined

-- | Type of a selection query.
typeSel :: MonadThrow m 
         => VsqlCond -> Rename Algebra -> VariationalContext -> Schema
         -> m TypeEnv
typeSel = undefined

-- | Type checks variational sql conditions.
typeVsqlCond :: MonadThrow m 
             => VsqlCond -> VariationalContext -> Schema -> TypeEnv 
             -> m ()
typeVsqlCond = undefined

-- | Type checks variational relational conditions.
typeCondition :: MonadThrow m 
              => Condition -> VariationalContext -> TypeEnv
              -> m ()
typeCondition = undefined

-- | Type checks a comparison.
typeComp :: MonadThrow m => Atom -> Atom -> TypeEnv -> m ()
typeComp = undefined

-- | Unions two type envs for a choice query.
unionChoiceType ::  TypeEnv -> TypeEnv -> TypeEnv
unionChoiceType = undefined

-- | Gives the type of rename joins.
typeJoin :: MonadThrow m 
         => Joins -> VariationalContext -> Schema
         -> m TypeEnv
typeJoin = undefined

-- | Gives the type of cross producting multiple rename relations.
typeProd :: MonadThrow m 
         => [Rename Relation] -> VariationalContext -> Schema
         -> m TypeEnv
typeProd rrs ctx s = 
  do uniqueRelAlias rrs 
     ts <- mapM (flip (flip typeRel ctx) s) rrs
     prodTypes ts

-- | Products a list of types.
prodTypes :: MonadThrow m => [TypeEnv] -> m TypeEnv
prodTypes ts = undefined

-- | Checks that table/alias are unique. The relation names or
--   their aliases must be unique.
uniqueRelAlias :: MonadThrow m => [Rename Relation] -> m ()
uniqueRelAlias rrs 
  | nub relNames == relNames = return ()
  | otherwise                = throwM $ NotUniqueRelAlias rrs
    where
      relNames  = fmap relName rrs
      relName r = maybe (thing r) Relation (name r)


-- | Returns the type of a rename relation.
typeRel :: MonadThrow m 
        => Rename Relation -> VariationalContext -> Schema
        -> m TypeEnv
typeRel rr ctx s = 
  do tsch <- lookupTableSch (thing rr) s 
     let t = tableSch2TypeEnv rr tsch 
     appCtxtToEnv ctx t

-- | Generates a type env from a table schema.
tableSch2TypeEnv :: Rename Relation -> TableSchema -> TypeEnv 
tableSch2TypeEnv rr tsch = 
  updateOptObj (SM.map (optSqlType2AttInfo rr) (getObj tsch)) tsch 
  where 
    optSqlType2AttInfo rr ot = pure $ AttrInfo (getFexp ot) (getObj ot) 
      $ maybe (RelQualifier (thing rr))
              (\n -> RelQualifier (Relation n)) 
              (name rr)

-- | Applies a variational ctxt to a type. 
--   Don't forget the empty env!!
appCtxtToEnv :: MonadThrow m => VariationalContext -> TypeEnv -> m TypeEnv
appCtxtToEnv ctx t 
    | satisfiable f = return $ mkOpt f $ appCtxtToMap f (getObj t)
    | otherwise = throwM $ IncosistentCtxtWithEnv ctx t
  where 
    f = F.shrinkFeatureExpr (F.And ctx $ getFexp t)
    appCtxtToMap fexp envMap = SM.filter null (SM.map (appCtxtToAttInfo fexp) envMap)
    appCtxtToAttInfo fexp is = filter (\i -> satisfiable (F.And fexp (attrFexp i))) is




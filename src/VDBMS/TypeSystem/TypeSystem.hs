-- | Statically syntesizes the types of vqs.
module VDBMS.TypeSystem.TypeSystem (

        TypeEnv
        , VariationalContext
        , typeOfVquery

) where 


import VDBMS.QueryLang.RelAlg.Variational.Algebra 
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.QueryLang.RelAlg.Variational.Condition 
import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Schema
import VDBMS.Features.SAT (equivalent, tautology)
import VDBMS.DBMS.Value.Value
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

-- | Variational context that the query is living in at the moment.
type VariationalContext = F.FeatureExpr

-- | Variational type env.
type TypeEnv = TableSchema

-- | Possible typing errors.
data TypeError 
  = InvalidRelRef Relation VariationalContext F.FeatureExpr
  | AttrNotSubsume (Opt (Rename Attr)) TypeEnv
  | EmptyAttrList Algebra 
  | NotEquiveTypeEnv TypeEnv TypeEnv VariationalContext
  | CompInvalid Atom Atom TypeEnv
  -- | EnvFexpUnsat F.FeatureExpr TypeEnv'
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception TypeError  

-- | verifies and similifies the final type env return by the type system, i.e.,
--   checks the satisfiability of all attributes' pres conds conjoined
--   with table pres cond.
-- SHRINK!!!
verifyTypeEnv :: MonadThrow m => TypeEnv -> m TypeEnv
verifyTypeEnv env = undefined
  -- | satisfiable (getFexp env) = return $ propagateFexpToTsch env
  -- | otherwise = throwM $ EnvFexpUnsat (getFexp env) env


-- 
-- Static semantics of a vquery that returns a table schema,
-- i.e. it includes the fexp of the whole table.
-- 
typeOfVquery :: MonadThrow m 
             => Algebra -> VariationalContext -> Schema 
             -> m TypeEnv
typeOfVquery (SetOp o l r)    ctx s = typeSetOp l r ctx s
typeOfVquery (Proj oas rq)    ctx s = typeProj oas rq ctx s
typeOfVquery (Sel c rq)       ctx s = 
  do t <- typeOfVquery (thing rq) ctx s
     typeVsqlCond c ctx s t 
     appFexpTableSch ctx t
typeOfVquery (AChc f l r)     ctx s = 
  do tl <- typeOfVquery l (F.And ctx f) s
     tr <- typeOfVquery r (F.And ctx (F.Not f)) s
     return $ mkOpt (F.Or (getFexp tl) (getFexp tr)) 
                  $ rowTypeUnion (getObj tl) (getObj tr)
typeOfVquery (Join js)        ctx s = typeJoin js ctx s
typeOfVquery (Prod rl rr rrs) ctx s = undefined
typeOfVquery (TRef rr)        ctx s = typeRel (thing rr) ctx s
typeOfVquery Empty            ctx s = 
  appFexpTableSch ctx $ mkOpt (F.Lit True) M.empty

-- | Statically type checks a relation reference.
typeRel :: MonadThrow m 
        => Relation -> VariationalContext -> Schema
        -> m TypeEnv
typeRel r ctx s = 
  do t <- lookupTableSch r s
     appFexpTableSch ctx t

-- | Statically type checks joins.
typeJoin :: MonadThrow m
         => Joins -> VariationalContext -> Schema 
         -> m TypeEnv
typeJoin (JoinTwoTables rl rr c) ctx s = 
  do tl <- typeRel (thing rl) ctx s
     tr <- typeRel (thing rr) ctx s
     let t = mkOpt (F.And (getFexp tl) (getFexp tr)) 
                   (SM.union (getObj tl) (getObj tr))
     typeCondition c ctx t
     return t
typeJoin (JoinMore js rr c)      ctx s = 
  do tj <- typeJoin js ctx s
     tr <- typeRel (thing rr) ctx s
     let t = mkOpt (F.And (getFexp tj) (getFexp tr))
                   (SM.union (getObj tj) (getObj tr))
     typeCondition c ctx t 
     return t 

-- | Statically type checks variational sql condiitons.
typeVsqlCond :: MonadThrow m 
             => VsqlCond -> VariationalContext -> Schema -> TypeEnv 
             -> m ()
typeVsqlCond (VsqlCond c)     ctx s t = typeCondition c ctx t 
typeVsqlCond (VsqlIn a q)     ctx s t = 
  do t <- typeOfVquery q ctx s 
     lookupAttFexpTypeInRowType (attribute a) (getObj t)
     return ()
typeVsqlCond (VsqlNot c)      ctx s t = typeVsqlCond c ctx s t 
typeVsqlCond (VsqlOr l r)     ctx s t = 
  do typeVsqlCond l ctx s t
     typeVsqlCond r ctx s t 
typeVsqlCond (VsqlAnd l r)    ctx s t = 
  do typeVsqlCond l ctx s t
     typeVsqlCond r ctx s t 
typeVsqlCond (VsqlCChc f l r) ctx s t = 
  do typeVsqlCond l (F.And ctx f) s t
     typeVsqlCond r (F.And ctx (F.Not f)) s t

-- | Statically type checks variational relational conditions.
typeCondition :: MonadThrow m 
              => Condition -> VariationalContext -> TypeEnv
              -> m ()
typeCondition (Lit b)      ctx t = return ()
typeCondition (Comp o l r) ctx t = typeComp l r t 
typeCondition (Not c)      ctx t = typeCondition c ctx t 
typeCondition (Or l r)     ctx t = 
  do typeCondition l ctx t
     typeCondition r ctx t
typeCondition (And l r)    ctx t = 
  do typeCondition l ctx t
     typeCondition r ctx t
typeCondition (CChc f l r) ctx t = 
  do typeCondition l (F.And ctx f) t
     typeCondition r (F.And ctx (F.Not f)) t

-- | Type checks a comparison.
typeComp :: MonadThrow m => Atom -> Atom -> TypeEnv -> m ()
typeComp a@(Val l)  a'@(Val r)  t 
  | typeOf l == typeOf r = return ()
  | otherwise = throwM $ CompInvalid a a' t 
typeComp a@(Val l)  a'@(Att r) t = 
  do (_,at) <- lookupAttFexpTypeInRowType (attribute r) (getObj t)
     if typeOf l == at 
     then return () 
     else throwM $ CompInvalid a a' t
typeComp a@(Att l) a'@(Val r)  t = 
  do (_,at) <- lookupAttFexpTypeInRowType (attribute l) (getObj t)
     if typeOf r == at 
     then return () 
     else throwM $ CompInvalid a a' t
typeComp a@(Att l) a'@(Att r) t = 
  do (_,lt) <- lookupAttFexpTypeInRowType (attribute l) (getObj t)
     (_,rt) <- lookupAttFexpTypeInRowType (attribute r) (getObj t)
     if lt == rt
     then return ()
     else throwM $ CompInvalid a a' t

-- | Determines the type of a projection query.
typeProj :: MonadThrow m 
         => OptAttributes -> Rename Algebra -> VariationalContext -> Schema
         -> m TypeEnv
typeProj oas rq ctx s =
  do t' <- typeOfVquery (thing rq) ctx s 
     if null oas 
     then throwM $ EmptyAttrList (thing rq)
     else do t <- typeOptAtts oas t'
             appFexpTableSch ctx t 

-- | Projects a list of optional attributes from a type env.
--   it updates included attribute's pres cond by the fexp
--   assigned to them in the list. it keeps the pres cond of
--   the whole table the same as before.
typeOptAtts :: MonadThrow m => OptAttributes -> TypeEnv -> m TypeEnv
typeOptAtts (ora:oras) env =
  do let a = attribute $ thing $ getObj ora 
         fa = getFexp ora
         newNameAtt = name $ getObj ora
         as = getTableSchAtts env
         fenv = getFexp env  
         newA = case newNameAtt of
                  Just s  -> Attribute s
                  Nothing -> a
     (fa',at) <- lookupAttFexpTypeInRowType a $ getObj env 
     if F.tautImplyFexps fa (F.And fenv fa')
     then do t <- typeOptAtts oras env
             return $ updateOptObj 
                       (M.union (M.singleton newA (F.And fa fa', at)) (getObj t))
                       env
     else throwM $ AttrNotSubsume ora env

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





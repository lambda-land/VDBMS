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
    , attrQuals :: [Qualifier]
    }
 deriving (Data,Ord,Eq,Show,Typeable)

-- | Variational type env.
-- type TypeEnv = TableSchema

-- | Variational type env.
type TypeEnv = M.Map Attribute AttrInfo

-- | Possible typing errors.
data TypeError 
  = InvalidRelRef Relation VariationalContext F.FeatureExpr
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
typeOfQuery = undefined
-- typeOfQuery (SetOp o l r)    ctx s = typeSetOp l r ctx s
-- typeOfQuery (Proj oas rq)    ctx s = typeProj oas rq ctx s
-- typeOfQuery (Sel c rq)       ctx s = 
--   do t <- typeOfQuery (thing rq) ctx s
--      typeVsqlCond c ctx s t 
--      appFexpTableSch ctx t
-- typeOfQuery (AChc f l r)     ctx s = 
--   do tl <- typeOfQuery l (F.And ctx f) s
--      tr <- typeOfQuery r (F.And ctx (F.Not f)) s
--      return $ mkOpt (F.Or (getFexp tl) (getFexp tr)) 
--                   $ rowTypeUnion (getObj tl) (getObj tr)
-- typeOfQuery (Join js)        ctx s = typeJoin js ctx s
-- typeOfQuery (Prod rl rr rrs) ctx s = 
--   typeProd (thing rl) (thing rr) (fmap thing rrs) ctx s
-- typeOfQuery (TRef rr)        ctx s = typeRel (thing rr) ctx s
-- typeOfQuery Empty            ctx s = 
--   appFexpTableSch ctx $ mkOpt (F.Lit True) M.empty

-- -- | Statically type chekcs a cross product query.
-- --   Note that it make sures that the two types are
-- --   disjoint.
-- typeProd :: MonadThrow m 
--          => Relation -> Relation -> [Relation] -> VariationalContext -> Schema
--          -> m TypeEnv
-- typeProd l r rs ctx s = 
--   do tl <- typeRel l ctx s 
--      tr <- typeRel r ctx s 
--      ts <- mapM (flip (flip typeRel ctx) s) rs 
--      compatibleTypes $ pure tl ++ pure tr ++ ts
--      disjointTypes tl tr ts 
--      return $ prodTypes $ pure tl ++ pure tr ++ ts

-- -- | Accumulates types for cross product.
-- prodTypes :: [TypeEnv] -> TypeEnv
-- prodTypes ts = mkOpt f r
--   where 
--     f = foldr F.And (F.Lit True) $ fmap getFexp ts
--     r = SM.unions $ fmap getObj ts

-- -- | Checks whether a list of type envs are disjoint or not.
-- disjointTypes :: MonadThrow m 
--                  => TypeEnv -> TypeEnv -> [TypeEnv] 
--                  -> m ()
-- disjointTypes l r ts 
--   | SM.keysSet (getObj l) `Set.disjoint` SM.keysSet (getObj r)
--     && disjointAll (l : r : ts) = return ()
--   | otherwise = throwM $ NotDisjointTypes (l : r : ts)
--     where
--       disjointAll (x : xs) = all (Set.disjoint (SM.keysSet (getObj x)))
--                                  (fmap (SM.keysSet . getObj) xs)
--                              && disjointAll xs
--       disjointAll [x]      = True
--       disjointAll []       = True

-- -- | Statically type checks a relation reference.
-- typeRel :: MonadThrow m 
--         => Relation -> VariationalContext -> Schema
--         -> m TypeEnv
-- typeRel r ctx s = 
--   do t <- lookupTableSch r s
--      appFexpTableSch ctx t

-- -- | Statically type checks joins.
-- typeJoin :: MonadThrow m
--          => Joins -> VariationalContext -> Schema 
--          -> m TypeEnv
-- typeJoin (JoinTwoTables rl rr c) ctx s = 
--   do tl <- typeRel (thing rl) ctx s
--      tr <- typeRel (thing rr) ctx s
--      compatibleTypes $ pure tl ++ pure tr
--      let t = mkOpt (F.And (getFexp tl) (getFexp tr)) 
--                    (SM.union (getObj tl) (getObj tr))
--      typeCondition c ctx t
--      return t
-- typeJoin (JoinMore js rr c)      ctx s = 
--   do tj <- typeJoin js ctx s
--      tr <- typeRel (thing rr) ctx s
--      compatibleTypes $ pure tj ++ pure tr
--      let t = mkOpt (F.And (getFexp tj) (getFexp tr))
--                    (SM.union (getObj tj) (getObj tr))
--      typeCondition c ctx t 
--      return t 

-- -- | Checks if two type envs are compatible with each other or not.
-- --   It assumes that the ctx has been applied to both of them already.
-- compatibleTypes :: MonadThrow m 
--                 => [TypeEnv] 
--                 -> m ()
-- compatibleTypes ts
--   | satisfiable (foldr F.And (F.Lit True) (fmap getFexp ts)) = return ()
--   | otherwise = throwM $ IncompatibleTypes ts

-- -- | Statically type checks variational sql condiitons.
-- typeVsqlCond :: MonadThrow m 
--              => VsqlCond -> VariationalContext -> Schema -> TypeEnv 
--              -> m ()
-- typeVsqlCond (VsqlCond c)     ctx s t = typeCondition c ctx t 
-- typeVsqlCond (VsqlIn a q)     ctx s t = 
--   do t <- typeOfQuery q ctx s 
--      lookupAttFexpTypeInRowType (attribute a) (getObj t)
--      return ()
-- typeVsqlCond (VsqlNot c)      ctx s t = typeVsqlCond c ctx s t 
-- typeVsqlCond (VsqlOr l r)     ctx s t = 
--   do typeVsqlCond l ctx s t
--      typeVsqlCond r ctx s t 
-- typeVsqlCond (VsqlAnd l r)    ctx s t = 
--   do typeVsqlCond l ctx s t
--      typeVsqlCond r ctx s t 
-- typeVsqlCond (VsqlCChc f l r) ctx s t = 
--   do typeVsqlCond l (F.And ctx f) s t
--      typeVsqlCond r (F.And ctx (F.Not f)) s t

-- -- | Statically type checks variational relational conditions.
-- typeCondition :: MonadThrow m 
--               => Condition -> VariationalContext -> TypeEnv
--               -> m ()
-- typeCondition (Lit b)      ctx t = return ()
-- typeCondition (Comp o l r) ctx t = typeComp l r t 
-- typeCondition (Not c)      ctx t = typeCondition c ctx t 
-- typeCondition (Or l r)     ctx t = 
--   do typeCondition l ctx t
--      typeCondition r ctx t
-- typeCondition (And l r)    ctx t = 
--   do typeCondition l ctx t
--      typeCondition r ctx t
-- typeCondition (CChc f l r) ctx t = 
--   do typeCondition l (F.And ctx f) t
--      typeCondition r (F.And ctx (F.Not f)) t

-- -- | Type checks a comparison.
-- typeComp :: MonadThrow m => Atom -> Atom -> TypeEnv -> m ()
-- typeComp a@(Val l)  a'@(Val r)  t 
--   | typeOf l == typeOf r = return ()
--   | otherwise = throwM $ CompInvalid a a' t 
-- typeComp a@(Val l)  a'@(Att r) t = 
--   do (_,at) <- lookupAttFexpTypeInRowType (attribute r) (getObj t)
--      if typeOf l == at 
--      then return () 
--      else throwM $ CompInvalid a a' t
-- typeComp a@(Att l) a'@(Val r)  t = 
--   do (_,at) <- lookupAttFexpTypeInRowType (attribute l) (getObj t)
--      if typeOf r == at 
--      then return () 
--      else throwM $ CompInvalid a a' t
-- typeComp a@(Att l) a'@(Att r) t = 
--   do (_,lt) <- lookupAttFexpTypeInRowType (attribute l) (getObj t)
--      (_,rt) <- lookupAttFexpTypeInRowType (attribute r) (getObj t)
--      if lt == rt
--      then return ()
--      else throwM $ CompInvalid a a' t

-- -- | Determines the type of a projection query.
-- typeProj :: MonadThrow m 
--          => OptAttributes -> Rename Algebra -> VariationalContext -> Schema
--          -> m TypeEnv
-- typeProj oas rq ctx s =
--   do t' <- typeOfQuery (thing rq) ctx s 
--      if null oas 
--      then throwM $ EmptyAttrList (thing rq)
--      else do t <- typeOptAtts oas t'
--              appFexpTableSch ctx t 

-- -- | Projects a list of optional attributes from a type env.
-- --   it updates included attribute's pres cond by the fexp
-- --   assigned to them in the list. it keeps the pres cond of
-- --   the whole table the same as before.
-- typeOptAtts :: MonadThrow m => OptAttributes -> TypeEnv -> m TypeEnv
-- typeOptAtts (ora:oras) env =
--   do let a = attribute $ thing $ getObj ora 
--          fa = getFexp ora
--          newNameAtt = name $ getObj ora
--          as = getTableSchAtts env
--          fenv = getFexp env  
--          newA = case newNameAtt of
--                   Just s  -> Attribute s
--                   Nothing -> a
--      (fa',at) <- lookupAttFexpTypeInRowType a $ getObj env 
--      if F.tautImplyFexps fa (F.And fenv fa')
--      then do t <- typeOptAtts oras env
--              return $ updateOptObj 
--                        (M.union (M.singleton newA (F.And fa fa', at)) (getObj t))
--                        env
--      else throwM $ AttrNotSubsume ora env

-- -- | Determines the type a set operation query.
-- typeSetOp :: MonadThrow m 
--           => Algebra -> Algebra -> VariationalContext -> Schema 
--           -> m TypeEnv
-- typeSetOp l r ctx s = 
--   do tl <- typeOfQuery l ctx s
--      tr <- typeOfQuery r ctx s 
--      envl <- appFexpTableSch ctx tl 
--      envr <- appFexpTableSch ctx tr
--      if typeEq envl envr
--      then return envr
--      else throwM $ NotEquiveTypeEnv envl envr ctx

-- -- | Type enviornment equilvanecy, checks that the vCtxt are 
-- --   equivalent, both env have the same set of attributes,
-- --   and attributes fexp are equivalent
-- typeEq :: TypeEnv -> TypeEnv-> Bool
-- typeEq envl envr = equivalent (getFexp envl) (getFexp envr) 
--   && getRowTypeAtts (getObj envl) == getRowTypeAtts (getObj envr) 
--   && SM.isSubmapOfBy (\(o,t) (o',t') -> t == t' && equivalent o o') 
--                      (getObj envl) 
--                      (getObj envr) 





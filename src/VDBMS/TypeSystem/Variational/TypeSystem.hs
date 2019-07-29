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
  = CtxUnsatOverEnv VariationalContext TypeEnv
  | NotUniqueRelAlias [Rename Relation]
  | UnsatFexpsInProduct F.FeatureExpr 
  | InOpMustContainOneClm TypeEnv
  | UnsatAttPCandEnv F.FeatureExpr TypeEnv
  | AttrQualNotInEnv Attr TypeEnv
  | AttrNotInEnv Attribute TypeEnv
  | AmbiguousAttr Attr TypeEnv
  | QualNotInInfo Qualifier AttrInformation
  -- | InvalidRelRef Relation VariationalContext F.FeatureExpr
  -- | AttrNotSubsume (Opt (Rename Attr)) TypeEnv
  -- | EmptyAttrList Algebra 
  -- | NotEquiveTypeEnv TypeEnv TypeEnv VariationalContext
  | CompInvalid Atom Atom TypeEnv
  -- | IncompatibleTypes [TypeEnv]
  -- | NotDisjointTypes [TypeEnv]
  -- | EnvFexpUnsat F.FeatureExpr TypeEnv
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception TypeError  

-- | looks up attr info for a qualifier.
lookupAttrInfo :: MonadThrow m => AttrInformation -> Qualifier -> m AttrInfo
lookupAttrInfo is q = 
  maybe 
    (throwM $ QualNotInInfo q is)
    (\(f,t) -> return $ AttrInfo f t q)
    (lookup q $ zip (fmap attrQual is) (zip (fmap attrFexp is) (fmap attrType is)))

-- | Returns all qualifiers for an attribute in a type.
lookupAttrQuals :: MonadThrow m => Attribute -> TypeEnv -> m [Qualifier]
lookupAttrQuals a t = 
  do i <- lookupAttr a t 
     return $ fmap attrQual i

-- | Looks up attribute information from the type.
lookupAttr :: MonadThrow m => Attribute -> TypeEnv -> m AttrInformation
lookupAttr a t = 
  maybe (throwM $ AttrNotInEnv a t)
        return
        (SM.lookup a (getObj t))

-- | Checks if an attribute (possibly with its qualifier) exists in a type env.
attrConsistentWithType :: MonadThrow m => Attr -> TypeEnv -> m ()
attrConsistentWithType a t = 
  do i <- nonAmbiguousAttr a t
     qs <- lookupAttrQuals (attribute a) t 
     pc <- lookupAttrFexpInEnv a t 
     maybe (return ())
           (\q -> if q `elem` qs
                  then if F.satAnds pc (getFexp t)
                       then return ()
                       else throwM $ UnsatAttPCandEnv pc t
                  else throwM $ AttrQualNotInEnv a t)
           (qualifier a)

-- | looks up the type of an attribute in the env.
lookupAttrTypeInEnv :: MonadThrow m => Attr -> TypeEnv -> m SqlType
lookupAttrTypeInEnv a t = 
  do i <- nonAmbiguousAttr a t 
     return $ attrType i 

-- | Looks up the presence condition of an attribute in the env.
lookupAttrFexpInEnv :: MonadThrow m => Attr -> TypeEnv -> m F.FeatureExpr
lookupAttrFexpInEnv a t = 
  do i <- nonAmbiguousAttr a t 
     return $ attrFexp i  

-- | checks if the attribute is ambigusous or not.
nonAmbiguousAttr :: MonadThrow m => Attr -> TypeEnv -> m AttrInfo
nonAmbiguousAttr a t = 
  do is <- lookupAttr (attribute a) t 
     qs <- lookupAttrQuals (attribute a) t
     if length qs > 1
     then maybe (throwM $ AmbiguousAttr a t) (lookupAttrInfo is) (qualifier a)
     else return $ head is


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
     return $ typeUnion tl tr
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
typeVsqlCond (VsqlCond c)     ctx s t = appCtxtToEnv ctx t 
  >>= typeCondition c ctx 
typeVsqlCond (VsqlIn a q)     ctx s t = typeOfQuery q ctx s 
  >>= onlyAttrInType a t
typeVsqlCond (VsqlNot c)      ctx s t = typeVsqlCond c ctx s t 
typeVsqlCond (VsqlOr l r)     ctx s t = typeVsqlCond l ctx s t 
  >> typeVsqlCond r ctx s t 
typeVsqlCond (VsqlAnd l r)    ctx s t = typeVsqlCond l ctx s t
  >> typeVsqlCond r ctx s t 
typeVsqlCond (VsqlCChc f l r) ctx s t = typeVsqlCond l (F.And ctx f) s t
  >> typeVsqlCond r (F.And ctx (F.Not f)) s t

-- | Checks if the attribute is the only attribute of a type env.
onlyAttrInType :: MonadThrow m 
               => Attr -> TypeEnv -> TypeEnv
               -> m ()
onlyAttrInType a tenv tq =
  do attrConsistentWithType a tenv
     if Set.null $ attribute a `Set.delete` SM.keysSet (getObj tq)
     then return ()
     else throwM $ InOpMustContainOneClm tq

-- | Type checks variational relational conditions.
typeCondition :: MonadThrow m 
              => Condition -> VariationalContext -> TypeEnv
              -> m ()
typeCondition (Lit b)      ctx t = return ()
typeCondition (Comp o l r) ctx t = typeComp l r t
typeCondition (Not c)      ctx t = typeCondition c ctx t
typeCondition (Or l r)     ctx t = typeCondition l ctx t >> typeCondition r ctx t
typeCondition (And l r)    ctx t = typeCondition l ctx t >> typeCondition r ctx t
typeCondition (CChc f l r) ctx t = 
  (appCtxtToEnv (F.And ctx f) t >>= typeCondition l (F.And ctx f))
  >> (appCtxtToEnv (F.And ctx (F.Not f)) t 
  >>= typeCondition r (F.And ctx (F.Not f)))

-- | Type checks a comparison.
typeComp :: MonadThrow m 
         => Atom -> Atom -> TypeEnv 
         -> m ()
typeComp a@(Val l)  a'@(Val r)  t 
  | typeOf l == typeOf r = return ()
  | otherwise = throwM $ CompInvalid a a' t 
typeComp a@(Val l)  a'@(Att r) t = 
  do at <- lookupAttrTypeInEnv r t
     if typeOf l == at 
     then return () 
     else throwM $ CompInvalid a a' t
typeComp a@(Att l) a'@(Val r)  t = 
  do at <- lookupAttrTypeInEnv l t
     if typeOf r == at 
     then return () 
     else throwM $ CompInvalid a a' t
typeComp a@(Att l) a'@(Att r) t = 
  do lt <- lookupAttrTypeInEnv l t
     lf <- lookupAttrFexpInEnv l t
     rt <- lookupAttrTypeInEnv r t
     rf <- lookupAttrFexpInEnv r t
     if lt == rt && satisfiable (F.And lf rf)
     then return ()
     else throwM $ CompInvalid a a' t

-- | Unions two type envs for a choice query.
typeUnion ::  TypeEnv -> TypeEnv -> TypeEnv
typeUnion t t' = 
  mkOpt (F.Or (getFexp t) (getFexp t'))
        (SM.unionWith (++) (getObj t) (getObj t'))

-- | Gives the type of rename joins.
typeJoin :: MonadThrow m 
         => Joins -> VariationalContext -> Schema
         -> m TypeEnv
typeJoin j@(JoinTwoTables rl rr c) ctx s = 
  do uniqueRelAlias $ relJoins j
     tl <- typeRel rl ctx s 
     tr <- typeRel rr ctx s 
     t <- prodTypes (pure tl ++ pure tr)
     typeCondition c ctx t 
     return t 
typeJoin j@(JoinMore js rr c)      ctx s = 
  do uniqueRelAlias $ relJoins j
     ts <- typeJoin js ctx s 
     tr <- typeRel rr ctx s 
     t <- prodTypes $ pure ts ++ pure tr 
     typeCondition c ctx t 
     return t

-- | Gets relation names/aliases from joins.
relJoins :: Joins -> [Rename Relation]
relJoins (JoinTwoTables rl rr c) = pure rl ++ pure rr
relJoins (JoinMore js rr c)      = relJoins js ++ pure rr 

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
prodTypes ts 
  | satisfiable f = appCtxtToEnv f prodTypeMaps
  | otherwise = throwM $ UnsatFexpsInProduct f
  where
    -- f = foldr F.And (F.Lit True) (map getFexp ts)
    f = foldr (F.And . getFexp) (F.Lit True) ts
    prodTypeMaps = mkOpt f (SM.unionsWith (++) (map getObj ts))

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
    | otherwise = throwM $ CtxUnsatOverEnv ctx t
  where 
    f = F.shrinkFeatureExpr (F.And ctx $ getFexp t)
    appCtxtToMap fexp envMap = SM.filter null (SM.map (appCtxtToAttInfo fexp) envMap)
    appCtxtToAttInfo fexp is = filter (\i -> satisfiable (F.And fexp (attrFexp i))) is




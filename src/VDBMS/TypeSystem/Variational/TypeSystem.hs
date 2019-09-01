-- | Statically syntesizes the types of vqs.
module VDBMS.TypeSystem.Variational.TypeSystem (

        TypeEnv
        , VariationalContext
        , typeOfQuery
        , AttrInfo(..)
        , updateType

) where 


import VDBMS.QueryLang.RelAlg.Variational.Algebra 
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.Features.SAT (equivalent, satisfiable)
import VDBMS.DBMS.Value.Value

import qualified Data.Map as M 
import qualified Data.Map.Strict as SM
import qualified Data.Set as Set 
-- import Data.Set (Set)
import Data.List (intersect, nub, (\\))

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
type TypeEnv = Opt (M.Map Attribute AttrInformation)

-- | Possible typing errors.
data TypeError 
  = CtxUnsatOverEnv VariationalContext TypeEnv
  | NotUniqueRelAlias TypeEnv TypeEnv
  | UnsatFexpsInProduct F.FeatureExpr 
  | InOpMustContainOneClm TypeEnv
  | UnsatAttPCandEnv OptAttribute TypeEnv
  | AttrQualNotInEnv Attr TypeEnv
  | AttrNotInEnv Attribute TypeEnv
  | AmbiguousAttr Attr TypeEnv
  | QualNotInInfo Qualifier AttrInformation
  | MissingAlias (Rename Algebra)
  | NotEquiveEnv TypeEnv TypeEnv
  | CompInvalid Atom Atom TypeEnv
  | EmptyAttrList OptAttributes (Rename Algebra)
    deriving (Data,Eq,Generic,Show,Typeable)

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
     -- pc <- lookupAttrFexpInEnv a t 
     maybe (return ())
           (\q -> if q == attrQual i
                  then return ()
                    -- if F.satAnds pc (getFexp t)
                       -- then return ()
                       -- else throwM $ UnsatAttPCandEnv pc t
                  else throwM $ AttrQualNotInEnv a t)
           (qualifier a)

-- | looks up the type of an attribute in the env.
lookupAttrTypeInEnv :: MonadThrow m => Attr -> TypeEnv -> m SqlType
lookupAttrTypeInEnv a t = 
  do i <- nonAmbiguousAttr a t 
     attrConsistentWithType a t
     return $ attrType i 

-- | Looks up the presence condition of an attribute in the env.
lookupAttrFexpInEnv :: MonadThrow m => Attr -> TypeEnv -> m F.FeatureExpr
lookupAttrFexpInEnv a t = 
  do i <- nonAmbiguousAttr a t 
     attrConsistentWithType a t
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
-- verifyTypeEnv :: MonadThrow m => TypeEnv -> m TypeEnv
-- verifyTypeEnv t = undefined
  -- | satisfiable (getFexp t) = return $ propagateFexpToTsch t
  -- | otherwise = throwM $ EnvFexpUnsat (getFexp t) t

-- 
-- Static semantics of a vquery that returns a table schema,
-- i.e. it includes the fexp of the whole table.
-- 
typeOfQuery :: MonadThrow m 
             => Algebra -> VariationalContext -> Schema 
             -> m TypeEnv
typeOfQuery (SetOp _ l r)    ctx s = typeSetOp l r ctx s 
typeOfQuery (Proj oas rq)    ctx s = typeProj oas rq ctx s
typeOfQuery (Sel c rq)       ctx s = typeSel c rq ctx s
typeOfQuery (AChc f l r)     ctx s = 
  do tl <- typeOfQuery l (F.And ctx f) s 
     tr <- typeOfQuery r (F.And ctx (F.Not f)) s 
     return $ typeUnion tl tr
typeOfQuery (Join rl rr c)   ctx s = typeJoin rl rr c ctx s 
typeOfQuery (Prod rl rr)     ctx s = typeProd rl rr ctx s 
typeOfQuery (TRef rr)        ctx s = typeRel rr ctx s 
typeOfQuery Empty            ctx _ = 
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
sameType lt rt 
  | compTypes equivalent (\_ _ -> True) (==) lt rt = return ()
  | otherwise = throwM $ NotEquiveEnv lt rt  

-- | compares two types with the given functions over each field of attr info.
compTypes :: (F.FeatureExpr -> F.FeatureExpr -> Bool)
          -> (SqlType -> SqlType -> Bool) 
          -> (Qualifier -> Qualifier -> Bool)
          -> TypeEnv -> TypeEnv -> Bool 
compTypes ff tf qf lt rt = SM.keysSet lObj == SM.keysSet rObj
  && tfexpEq
  && envsEq
  where
    rObj = getObj rt
    lObj = getObj lt
    tfexpEq = ff (getFexp lt) (getFexp rt)
    envsEq = SM.isSubmapOfBy (eqAttInfo ff tf qf) lObj rObj 
          && SM.isSubmapOfBy (eqAttInfo ff tf qf) rObj lObj
    -- eqAttInfo :: AttrInformation -> AttrInformation -> Bool
    eqAttInfo f t q lis ris = length lis == length ris 
      && null (lqs \\ rqs)
      && null (rqs \\ lqs)
      && and res
      where 
        lqs = fmap attrQual lis
        rqs = fmap attrQual ris
        res = [ t (attrType li) (attrType ri) && f (attrFexp li) (attrFexp ri) 
                | li <- lis, ri <- ris, q (attrQual li) (attrQual ri) ]

-- | Type of a projection query.
typeProj :: MonadThrow m 
         => OptAttributes -> Rename Algebra -> VariationalContext -> Schema
         -> m TypeEnv
typeProj oas rq ctx s 
  | null oas = throwM $ EmptyAttrList oas rq 
  | otherwise = 
    do t <- typeOfQuery (thing rq) ctx s 
       t' <- projOptAttrs oas t
       appCtxtToEnv ctx t' 

-- | Checks if an attribute (possibly with its qualifier) exists in a type env.
projOptAtt :: MonadThrow m => OptAttribute -> TypeEnv -> m TypeEnv
projOptAtt ora t = 
  do let aObj = getObj ora
         attr = thing aObj
         a = attribute attr
         aq = qualifier attr
         aName = name aObj
         aPC = getFexp ora
         tPC = getFexp t
     i <- nonAmbiguousAttr attr t
     let iQual = attrQual i
         iSqlT = attrType i
         iPC = attrFexp i
     pc <- lookupAttrFexpInEnv attr t 
     maybe (if F.satAnds (F.And pc aPC) tPC
            then return $ maybe
                            (attr2env tPC a iPC aPC iSqlT iQual)
                            (\n -> attr2env tPC (Attribute n) iPC aPC iSqlT iQual)
                            aName
            else throwM $ UnsatAttPCandEnv ora t)
           (\q -> if q == attrQual i
                  then if F.satAnds (F.And pc aPC) (getFexp t)
                       then return $ maybe
                                      (attr2env tPC a iPC aPC iSqlT iQual)
                                      (\n -> attr2env tPC (Attribute n) iPC aPC iSqlT iQual)
                                      aName
                       else throwM $ UnsatAttPCandEnv ora t
                  else throwM $ AttrQualNotInEnv attr t)
           aq

-- | constructs a new type env for one attribute.
attr2env :: F.FeatureExpr 
  -> Attribute 
  -> F.FeatureExpr -> F.FeatureExpr
  -> SqlType -> Qualifier
  -> TypeEnv
attr2env tPC a attEnvPC attrPC sqlt q =
  mkOpt tPC (SM.singleton a (pure $ AttrInfo (F.And attEnvPC attrPC) sqlt q))

-- | update the attribute names to their new name if possible.
projOptAttrs :: MonadThrow m => OptAttributes -> TypeEnv -> m TypeEnv
projOptAttrs oras t = 
  do ts <- mapM (flip projOptAtt t) oras
     return $ mkOpt (F.shrinkFeatureExpr $ F.disjFexp $ fmap getFexp ts)
                    (SM.unionsWith (++) $ fmap getObj ts)

-- | Type of a selection query.
typeSel :: MonadThrow m 
         => VsqlCond -> Rename Algebra -> VariationalContext -> Schema
         -> m TypeEnv
typeSel c rq ctx s =
  do validSubQ rq --ctx s 
     t <- typeOfQuery (thing rq) ctx s
     let t' = updateType (name rq) t 
     typeVsqlCond c ctx s t'
     appCtxtToEnv ctx t'

-- | Checks if a subquery is valid within a seleciton or projection.
--   Assumption: optimizations has applied before this.
-- TODO: Come back to this after opt rules are done!
validSubQ :: MonadThrow m => Rename Algebra -> m ()
validSubQ rq@(Rename a (SetOp _ _ _)) =
  maybe (throwM $ MissingAlias rq) (\_ -> return ()) a 
validSubQ _ = return ()

-- | updates a type env with a new name.
updateType :: Alias -> TypeEnv -> TypeEnv
updateType a t = updateOptObj updatedTypeObj t
  where
    tObj = getObj t
    updatedTypeObj = maybe tObj (\n -> SM.map (appName n) tObj) a 
    appName :: String -> AttrInformation -> AttrInformation
    appName n = fmap (updateQual (SubqueryQualifier n))
    updateQual q (AttrInfo af at _) = AttrInfo af at q 


-- | Type checks variational sql conditions.
typeVsqlCond :: MonadThrow m 
             => VsqlCond -> VariationalContext -> Schema -> TypeEnv 
             -> m ()
typeVsqlCond (VsqlCond c)     ctx _ t = appCtxtToEnv ctx t 
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
typeCondition (Lit _)      _   _ = return ()
typeCondition (Comp _ l r) _   t = typeComp l r t
typeCondition (Not c)      ctx t = typeCondition c ctx t
typeCondition (Or l r)     ctx t = typeCondition l ctx t >> typeCondition r ctx t
typeCondition (And l r)    ctx t = typeCondition l ctx t >> typeCondition r ctx t
typeCondition (CChc f l r) ctx t = 
  (appCtxtToEnv (F.And ctx f) t 
  >>= typeCondition l (F.And ctx f))
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
     if lt == rt && F.satAnds lf rf
     then return ()
     else throwM $ CompInvalid a a' t

-- | Unions two type envs for a choice query.
typeUnion ::  TypeEnv -> TypeEnv -> TypeEnv
typeUnion t t' = 
  mkOpt (F.Or (getFexp t) (getFexp t'))
        (SM.unionWith (++) (getObj t) (getObj t'))

-- | Gives the type of rename joins.
typeJoin :: MonadThrow m 
         => Rename Algebra -> Rename Algebra -> Condition
         -> VariationalContext -> Schema
         -> m TypeEnv
typeJoin rl rr c ctx s = 
  do t <- typeProd rl rr ctx s 
     typeCondition c ctx t 
     return t 

-- | Gives the type of cross producting multiple rename relations.
typeProd :: MonadThrow m 
         => Rename Algebra -> Rename Algebra 
         -> VariationalContext -> Schema
         -> m TypeEnv
typeProd rl rr ctx s = 
  do tl <- typeOfQuery (thing rl) ctx s 
     tr <- typeOfQuery (thing rr) ctx s 
     uniqueRelAlias tl tr 
     prodTypes tl tr 

-- | Products a list of types.
prodTypes :: MonadThrow m => TypeEnv -> TypeEnv -> m TypeEnv
prodTypes tl tr 
  | satisfiable f = appCtxtToEnv f prodTypeMaps
  | otherwise = throwM $ UnsatFexpsInProduct f
    where 
      f  = F.And fl fr 
      fl = getFexp tl
      fr = getFexp tr
      prodTypeMaps = mkOpt f (SM.unionWith (++) (getObj tl) (getObj tr))

-- | Checks that table/alias are unique. The relation names or
--   their aliases must be unique.
uniqueRelAlias :: MonadThrow m => TypeEnv -> TypeEnv -> m ()
uniqueRelAlias tl tr 
  | null relNs = return ()
  | otherwise  = throwM $ NotUniqueRelAlias tl tr 
    where 
      relNs = relNames (getObj tl) `intersect` relNames (getObj tr)
      relNames envObj = nub $ fmap (qualName . attrQual) $ concatMap snd $ SM.toList envObj


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
    optSqlType2AttInfo r ot = pure $ AttrInfo (getFexp ot) (getObj ot) 
      $ maybe (RelQualifier (thing r))
              (\n -> RelQualifier (Relation n)) 
              (name r)

-- | Applies a variational ctxt to a type. 
--   Don't forget the empty env!!
appCtxtToEnv :: MonadThrow m => VariationalContext -> TypeEnv -> m TypeEnv
appCtxtToEnv ctx t 
    | satisfiable f = return $ mkOpt f $ appCtxtToMap f (getObj t)
    | otherwise = throwM $ CtxUnsatOverEnv ctx t
  where 
    f = F.shrinkFeatureExpr (F.And ctx $ getFexp t)
    appCtxtToMap fexp envMap = SM.filter null (SM.map (appCtxtToAttInfo fexp) envMap)
    appCtxtToAttInfo fexp is = filter (\i -> F.satAnds fexp (attrFexp i)) is




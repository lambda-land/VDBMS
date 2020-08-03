-- | Statically syntesizes the types of vqs.
module VDBMS.TypeSystem.Variational.TypeSystem where
-- (

--         TypeEnv
--         , VariationalContext
--         , typeOfQuery
--         , runTypeQuery
--         , AttrInfo(..)
--         , updateType
--         , typePC
--         , typeEnv2tableSch
--         , typeEnve2OptAtts
--         , typeAtts
--         , tableSch2TypeEnv
--         , appCtxtToEnv

-- ) where 


-- Note: there's no need for renaming all over the place.
--       types have multiple qualifier per attribute
--       so they can recognize that a query is referring to 
--       two different attributes. you should change the 
--       qualifier of an attribute when you have renaming
--       and check that you don't have repeated qualifier names.
--       so you odn't need to change the qualifier for join or 
--       anything else. 

import VDBMS.QueryLang.RelAlg.Variational.Algebra 
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.Features.SAT (equivalent, satisfiable, unsatisfiable)
import VDBMS.DBMS.Value.Value

import qualified Data.Map as M 
import qualified Data.Map.Strict as SM
import qualified Data.Set as Set 
-- import Data.Set (Set)
import Data.List (intersect, nub, (\\))

import Data.Maybe (maybe, fromJust, isNothing)

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

-- | Variational type map and type env.
type TypeMap = M.Map Attribute AttrInformation
type TypeEnv = Opt TypeMap

-- | presence condition of type.
typePC :: TypeEnv -> F.FeatureExpr
typePC = getFexp

-- | applies func to pcs of atts.
applyFuncToAttFexp :: (F.FeatureExpr -> F.FeatureExpr)
                   -> AttrInformation 
                   -> AttrInformation
applyFuncToAttFexp f = map (\i -> AttrInfo (f (attrFexp i)) (attrType i) (attrQual i))

-- | updates attributes fexp.
updateAttFexp :: F.FeatureExpr -> AttrInformation -> AttrInformation
updateAttFexp f = map (\i -> AttrInfo (F.And f (attrFexp i)) (attrType i) (attrQual i))

-- | turns a type env to table schema.
typeEnv2tableSch :: TypeEnv -> TableSchema
typeEnv2tableSch t = mkOpt (typePC t) $ SM.fromList (concatMap attrinfo (SM.toList (getObj t)))
  where 
    attrinfo :: (Attribute, AttrInformation) -> [(Attribute, Opt SqlType)]
    attrinfo (a,ais) = map (\ai -> (Attribute $ (qualName . attrQual) ai ++ an, mkOpt (attrFexp ai) (attrType ai))) ais
      where an = "." ++ attributeName a

-- | transforms a type env to a list of opt attributes.
typeEnve2OptAtts :: TypeEnv -> OptAttributes
typeEnve2OptAtts env = concatMap attrTrans (M.toList (getObj env))
  where
    envPC = typePC env
    attrTrans :: (Attribute, AttrInformation) -> OptAttributes
    attrTrans (a, ais) = map (\ai -> mkOpt 
      (F.And envPC (attrFexp ai)) 
      (Attr a (Just $ attrQual ai))) ais 

-- | returns the attributes of type env. 
--   assumption: attributes are unique.
typeAtts :: TypeEnv -> [Attribute]
typeAtts = SM.keys . getObj

-- | Possible typing errors.
data TypeError 
  = 
  CtxUnsatOverEnv VariationalContext TypeEnv
  | NotUniqueRelAlias [Name] TypeEnv TypeEnv
  | UnsatFexpsInProduct F.FeatureExpr 
  | InOpMustContainOneClm TypeEnv
  | UnsatAttPCandEnv OptAttribute TypeEnv
  | AttrQualNotInEnv Attr [Qualifier]
  | AttrNotInEnv Attribute TypeEnv
  | AmbiguousAttr Attr AttrInformation
  -- | AmbiguousAttrInCtxt Attr AttrInformation VariationalContext
  | QualNotInInfo Attribute Qualifier AttrInformation
  | MissingAlias (Rename Algebra)
  | NotEquiveEnv TypeEnv TypeEnv
  | CompInvalid Atom Atom TypeEnv
  | EmptyAttrList OptAttributes Algebra
  | TypeEnvNotDisjoint TypeEnv TypeEnv
  | UnsatFexAppliedToTypeMap F.FeatureExpr TypeMap
  | EnvsMapNotEqDueToQualMismatch Attribute Qualifier Qualifier
  | EnvsMapNotEqDueToTypeMismatch Attribute SqlType SqlType
  | EnvsMapNotEqDueToUnequivFexp Attribute F.FeatureExpr F.FeatureExpr
  | EnvsFexpNotEq F.FeatureExpr F.FeatureExpr
  | EnvsKeySetsNotEq (Set.Set Attribute) (Set.Set Attribute)
  | ProjectingAttFromEmpty OptAttribute
  -- | UnsatFexpsTypeInetersect F.FeatureExpr
    deriving (Data,Eq,Generic,Show,Typeable)

instance Exception TypeError  

-- | looks up attr info for a qualifier.
lookupAttrInfo_ :: MonadThrow m 
                => Attribute -> AttrInformation -> Qualifier 
                -> m AttrInfo
lookupAttrInfo_ a is q = 
  maybe 
    (throwM $ QualNotInInfo a q is)
    (\(f,t) -> return $ AttrInfo f t q)
    (lookup q $ zip (fmap attrQual is) (zip (fmap attrFexp is) (fmap attrType is)))

-- TESTED
-- | Returns all qualifiers for an attribute in a type.
lookupAttrQuals :: MonadThrow m => Attribute -> TypeEnv -> m [Qualifier]
lookupAttrQuals a t = 
  do i <- lookupAttribute_ a t 
     return $ fmap attrQual i

-- TESTED
-- | Looks up attribute information from the type.
lookupAttribute_ :: MonadThrow m => Attribute -> TypeEnv -> m AttrInformation
lookupAttribute_ a t = 
  maybe (throwM $ AttrNotInEnv a t)
        return
        (SM.lookup a (getObj t))

-- | Looks up attribute information from the type and applies the type pc
--   to all attributes. 
lookupAttribute :: MonadThrow m => Attribute -> TypeEnv -> m AttrInformation
lookupAttribute a t =
  maybe (throwM $ AttrNotInEnv a t)
        (return . updateAttFexp (typePC t))
        (SM.lookup a (getObj t))

-- | Checks if an attribute (possibly with its qualifier) exists 
--   in a type env.
attrConsistentWithType :: MonadThrow m => Attr -> [Qualifier] -> m ()
attrConsistentWithType a qs = 
  maybe (return ())
    (\q -> if q `elem` qs
           then return ()
           else throwM $ AttrQualNotInEnv a qs)
    (qualifier a)
     -- pc <- lookupAttrFexpInEnv a t 
     -- maybe (return ())
     --       (\q -> if q == attrQual i
     --              then return ()
     --                -- if F.satAnds pc (getFexp t)
     --                   -- then return ()
     --                   -- else throwM $ UnsatAttPCandEnv pc t
     --              else throwM $ AttrQualNotInEnv a t)
     --       (qualifier a)

-- | looks up the type of an attribute in the env.
lookupAttrTypeFromEnv :: MonadThrow m 
                    => Attr -> TypeEnv 
                    -- -> VariationalContext 
                    -> m [SqlType]
lookupAttrTypeFromEnv a t = 
  do is <- lookupAttr a t
     -- attrConsistentWithType a t
     return $ map attrType is 

-- | Looks up the presence condition of an attribute in the env.
-- lookupAttrFexpFromEnv :: MonadThrow m 
--                            => Attr -> TypeEnv 
--                            -- -> VariationalContext 
--                            -> m [F.FeatureExpr]
-- lookupAttrFexpFromEnv a t = 
--   do is <- lookupAttr a t
--      -- attrConsistentWithType a t
--      return $ map attrFexp is

lookupAttr :: MonadThrow m => Attr -> TypeEnv -> m AttrInformation
lookupAttr a t = 
  do let at = attribute a
     is <- lookupAttribute at t 
     maybe (return is)
           (\q -> sequence (pure $ lookupAttrInfo_ at is q))
           (qualifier a)

-- | checks if the attribute is ambigusous or not.
-- note that it considers both the qualifier and the fexp.
-- i.e., if r.a has been repeated it checks for the fexps,
-- if their conjunction is satisfiable (there exists a config
-- under which both attributes could exists) then we have an
-- ambiuous attribute. however, if it is unsat then we're ok.
-- e.g. of this is the attribute salary in empvq2.
nonAmbiguousAttr :: MonadThrow m => Attr -> TypeEnv -> m AttrInformation
nonAmbiguousAttr a t = 
  do is <- lookupAttribute (attribute a) t 
     qs <- lookupAttrQuals (attribute a) t
     attrConsistentWithType a qs
     if length qs > 1
     then isAmbiguous a is
      -- maybe (throwM $ AmbiguousAttr a (map attrQual $ getObj t SM.! attribute a) t) 
      --           (lookupAttrInfo is) 
      --           (qualifier a)
     else return $ is

-- | helper for nonAmbiguousAttr. 
isAmbiguous :: MonadThrow m => Attr -> AttrInformation -> m AttrInformation
isAmbiguous a is 
  | isNothing q = if null [ (i,i') | i <- is, i' <- is, i /= i'
                                   , satisfiable (attrFexp i `F.And` attrFexp i')]
                  then return is
                  else throwM $ AmbiguousAttr a is
  | otherwise   = lookupAttrInfo_ (attribute a) is (fromJust q) >>= return . pure
    where
      q = qualifier a
  
-- | returns the attr information from the type env
--   for a given ctxt. Note that if the ctxt isn't given
--   the type env can have multiple instances of an attribute
--   but in a given ctxt only one instance of the given attr
--   should exists. 
-- attinfoFromTypeInCtxt :: MonadThrow m 
--                       => Attr -> TypeEnv -> VariationalContext 
--                       -> m AttrInfo
-- attinfoFromTypeInCtxt a t ctx =
--   do is <- nonAmbiguousAttr a t
--      let is' = filter (\i -> satisfiable (F.And ctx (attrFexp i))) is 
--      if length is' > 1
--      then throwM $ AmbiguousAttrInCtxt a is' ctx
--      else return $ head is'

-- | verifies and similifies the final type env return by the type system, i.e.,
--   checks the satisfiability of all attributes' pres conds conjoined
--   with table pres cond.
-- verifyTypeEnv :: MonadThrow m => TypeEnv -> m TypeEnv
-- verifyTypeEnv t = undefined
  -- | satisfiable (getFexp t) = return $ propagateFexpToTsch t
  -- | otherwise = throwM $ EnvFexpUnsat (getFexp t) t

-- | drops the monad throw from a type.
extrctType :: Maybe TypeEnv -> TypeEnv
extrctType = fromJust


-- | runs the typeofquery for a given query and schema,
--   initiating tbe context to the feature model.
runTypeQuery :: MonadThrow m => Algebra -> Schema -> m TypeEnv
runTypeQuery q s = typeOfQuery q (featureModel s) s

-- | Simplifies the type of a query.
simplType :: MonadThrow m => Algebra -> Schema -> m TypeEnv
simplType q s = 
  do t <- runTypeQuery q s
     let shrinkType :: TypeEnv -> TypeEnv
         shrinkType env = applyFuncFexp F.shrinkFeatureExpr 
           $ applyFuncObj (SM.map (applyFuncToAttFexp F.shrinkFeatureExpr)) env 
     return $ shrinkType t

-- |checks if a query is type correct or not. 
checkType :: MonadThrow m => Algebra -> Schema -> m ()
checkType q s = simplType q s >> return ()


-- sameType_ (extrctType $ simplType empVQ1_alt0 empVSchema) (extrctType $ simplType empVQ1_alt empVSchema)

-- 
-- Static semantics of a vquery that returns a table schema,
-- i.e. it includes the fexp of the whole table.
-- 
typeOfQuery :: MonadThrow m 
             => Algebra -> VariationalContext -> Schema 
             -> m TypeEnv
typeOfQuery (SetOp _ l r)    ctx s = typeSetOp l r ctx s 
typeOfQuery (Proj oas q)     ctx s = typeProj oas q ctx s
typeOfQuery (Sel c q)        ctx s = typeSel c q ctx s
-- note that achc doesn't need to app ctxt to type because
-- it's been applied already in tl and tr and the new pc is
-- more general. so if an attribute belongs to tl or tr it
-- also belongs to the final type.
typeOfQuery (AChc f l r)     ctx s = 
  do tl <- typeOfQuery l (F.And ctx f) s 
     tr <- typeOfQuery r (F.And ctx (F.Not f)) s 
     appCtxtToEnv (F.Or (F.And (getFexp tl) f) 
                        (F.And (getFexp tr) (F.Not f)))
      $ unionTypes (applyFuncFexp (F.And f) tl) (applyFuncFexp (F.And (F.Not f)) tr)
typeOfQuery (Join l r c)    ctx s = typeJoin l r c ctx s 
typeOfQuery (Prod l r)      ctx s = typeProd l r ctx s 
typeOfQuery (TRef r)        ctx s = typeRel r ctx s 
typeOfQuery (RenameAlg n q) ctx s = 
  typeOfQuery q ctx s
  >>= return . updateType n 
typeOfQuery Empty           ctx _ = 
  appCtxtToEnv ctx (mkOpt (F.Lit False) SM.empty)

-- | Determines the type a set operation query.
typeSetOp :: MonadThrow m 
          => Algebra -> Algebra -> VariationalContext -> Schema 
          -> m TypeEnv
typeSetOp l r ctx s = 
  do tl <- typeOfQuery l ctx s
     tr <- typeOfQuery r ctx s 
     sameType tl tr 
     return tl

-- TODO isn't working correctly or maybe the queries aren't equiv. come back to it
-- with a more elab error.
-- | Checks if two type are the same.
sameType_ :: MonadThrow m => TypeEnv -> TypeEnv -> m ()
sameType_ lt rt 
  | compTypes_ equivalent (\_ _ -> True) (==) lt rt = return ()
  | otherwise = throwM $ NotEquiveEnv lt rt  

-- TODO debug
-- | Checks if two type are the same with elaborate error.
sameType :: MonadThrow m => TypeEnv -> TypeEnv -> m ()
sameType lt rt = compTypes equivalent (\_ _ -> True) (==) lt rt >> return ()

-- TODO debug
-- | a more ellaborate error giving comp.
compTypes :: MonadThrow m
          => (F.FeatureExpr -> F.FeatureExpr -> Bool)
          -> (SqlType -> SqlType -> Bool) 
          -> (Qualifier -> Qualifier -> Bool)
          -> TypeEnv -> TypeEnv -> m Bool 
compTypes ff tf qf lt rt = undefined
  -- do let rObj = getObj rt
  --        lObj = getObj lt
  --        lfexp = getFexp lt 
  --        rfexp = getFexp rt 
  --        tfexpEq = ff lfexp rfexp
  --        -- envsEq = SM.isSubmapOfBy (eqAttInfo ff tf qf) lObj rObj 
  --        --   && SM.isSubmapOfBy (eqAttInfo ff tf qf) rObj lObj
  --        -- eqAttInfo :: AttrInformation -> AttrInformation -> Bool
  --        -- eqAttInfo f t q lis ris = length lis == length ris 
  --        --   && null (lqs \\ rqs)
  --        --   && null (rqs \\ lqs)
  --        --   && and res
  --        -- lqs = fmap attrQual lis
  --        -- rqs = fmap attrQual ris
  --        -- res = [ t (attrType li) (attrType ri) && f (F.And (attrFexp li) lfexp) (F.And (attrFexp ri) rfexp)
  --        --     | li <- lis, ri <- ris, q (attrQual li) (attrQual ri) ]
  --    if SM.keysSet lObj == SM.keysSet rObj
  --    then if tfexpEq 
  --         then if envsEq
  --              then return True
  --              else throwM $ 
  --         else throwM $ EnvsFexpNotEq (F.shrinkFeatureExpr lfexp) (F.shrinkFeatureExpr rfexp)
  --    else throwM $ EnvsKeySetsNotEq (SM.keysSet lObj) (SM.keysSet rObj)

-- TODO debug
-- | compares two types with the given functions over each field of attr info.
compTypes_ :: (F.FeatureExpr -> F.FeatureExpr -> Bool)
          -> (SqlType -> SqlType -> Bool) 
          -> (Qualifier -> Qualifier -> Bool)
          -> TypeEnv -> TypeEnv -> Bool 
compTypes_ ff tf qf lt rt = SM.keysSet lObj == SM.keysSet rObj
  && tfexpEq
  && envsEq
  where
    rObj = getObj rt
    lObj = getObj lt
    lfexp = getFexp lt 
    rfexp = getFexp rt 
    tfexpEq = ff lfexp rfexp
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
        res = [ t (attrType li) (attrType ri) && f (F.And (attrFexp li) lfexp) (F.And (attrFexp ri) rfexp)
                | li <- lis, ri <- ris, q (attrQual li) (attrQual ri) ]

-- | Type of a projection query.
typeProj :: MonadThrow m 
         => OptAttributes -> Algebra -> VariationalContext -> Schema 
         -> m TypeEnv
typeProj oas q ctx s 
  | null oas = throwM $ EmptyAttrList oas q 
  | otherwise = 
    do t <- typeOfQuery q ctx s 
       t' <- projOptAttrs oas t 
       appCtxtToEnv ctx t' 

-- | Checks if an attribute (possibly with its qualifier) exists in a type env.
-- note that it's checking subsumption too.
projOptAtt :: MonadThrow m 
           => OptAttribute -> TypeEnv 
           -- -> VariationalContext
           -> m TypeEnv
projOptAtt oa t = 
  do let attr = getObj oa
         -- attr = thing aObj
         a = attribute attr
         aq = qualifier attr
         -- aName = name aObj
         aPC = getFexp oa
         tPC = typePC t
     if SM.null (getObj t)
     then throwM $ ProjectingAttFromEmpty oa
     else do is <- nonAmbiguousAttr attr t 
             let validInfos = maybe 
                   (filter (satisfiable . (F.And aPC) . attrFexp) is)
                   (\q -> filter (satisfiable . (F.And aPC) . attrFexp) 
                      $ filter (((==) q) . attrQual) is)
                   aq
             if null validInfos
             then throwM $ UnsatAttPCandEnv oa t
             else return $ mkOpt tPC $ SM.singleton a 
                         $ updateAttFexp aPC validInfos
     -- -- pc <- lookupAttrFexpInEnv attr t 
     -- maybe (if F.satAnds iPC aPC
     --        then return $ attr2env tPC a iPC aPC iSqlT iQual
     --                        -- (\n -> attr2env tPC (Attribute n) iPC aPC iSqlT iQual)
     --                        -- aName
     --        else throwM $ UnsatAttPCandEnv oa t)
     --       (\q -> if q == attrQual i
     --              then if F.satAnds pc aPC
     --                   then return $ attr2env tPC a iPC aPC iSqlT iQual
     --                                  -- (\n -> attr2env tPC (Attribute n) iPC aPC iSqlT iQual)
     --                                  -- aName
     --                   else throwM $ UnsatAttPCandEnv oa t
     --              else throwM $ AttrQualNotInEnv attr t)
     --       aq

-- | constructs a new type env for one attribute.
-- attr2env :: F.FeatureExpr 
--   -> Attribute 
--   -> F.FeatureExpr -> F.FeatureExpr
--   -> SqlType -> Qualifier
--   -> TypeEnv
-- attr2env tPC a attEnvPC attrPC sqlt q =
--   mkOpt tPC (SM.singleton a (pure $ AttrInfo (F.And attEnvPC attrPC) sqlt q))

-- | update the attribute names to their new name if possible.
projOptAttrs :: MonadThrow m => OptAttributes -> TypeEnv -> m TypeEnv
projOptAttrs oras t = 
  do ts <- mapM (flip projOptAtt t) oras
     return $ mkOpt (F.shrinkFeatureExpr $ F.disjFexp $ fmap getFexp ts)
                    (SM.unionsWith (++) $ fmap getObj ts)

-- | Type of a selection query.
typeSel :: MonadThrow m 
         => VsqlCond -> Algebra -> VariationalContext -> Schema 
         -> m TypeEnv
typeSel c q ctx s =
  do 
     -- validSubQ rq --ctx s -- this was for checking renaming of subq in sql.
     t <- typeOfQuery q ctx s
     -- let t' = updateType (name rq) t -- this was for when we had attr 
     -- renaming in alg.
     typeVsqlCond c ctx s t
     -- appCtxtToEnv ctx t' -- you don't need this since you just need to 
     -- check consistency of ctxt with conditions and it shouldn't be 
     -- applied to the overal type env.
     return t

-- | Checks if a subquery is valid within a seleciton or projection.
--   Assumption: optimizations has applied before this.
-- NOTE: we don't need this since sql queries will be 
--       generated s.t. they don't violate this.
-- validSubQ :: MonadThrow m => Rename Algebra -> m ()
-- validSubQ rq@(Rename a (SetOp _ _ _)) =
--   maybe (throwM $ MissingAlias rq) (\_ -> return ()) a 
-- validSubQ _ = return ()

-- | updates a type env with a new name.
updateType :: Name -> TypeEnv -> TypeEnv
updateType n t = updateOptObj updatedTypeObj t
  where
    tObj = getObj t
    updatedTypeObj = SM.map (appName n) tObj 
    appName :: Name -> AttrInformation -> AttrInformation
    appName nm = fmap (updateQual (SubqueryQualifier nm))
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
typeVsqlCond (VsqlCChc f l r) ctx s t = 
  appCtxtToEnv (F.And ctx f) t
  >>= typeVsqlCond l (F.And ctx f) s 
  >> appCtxtToEnv (F.And ctx (F.Not f)) t
  >>= typeVsqlCond r (F.And ctx (F.Not f)) s 

-- | Checks if the attribute is the only attribute of a type env.
onlyAttrInType :: MonadThrow m 
               => Attr -> TypeEnv -> TypeEnv
               -> m ()
onlyAttrInType a tenv tq =
  do qs <- lookupAttrQuals (attribute a) tenv
     attrConsistentWithType a qs
     if Set.null $ attribute a `Set.delete` SM.keysSet (getObj tq)
     then return ()
     else throwM $ InOpMustContainOneClm tq

-- | Type checks variational relational conditions.
typeCondition :: MonadThrow m 
              => Condition -> VariationalContext -> TypeEnv
              -> m ()
typeCondition (Lit _)      _   _ = return ()
typeCondition (Comp _ l r) ctx t = typeComp l r ctx t
typeCondition (Not c)      ctx t = typeCondition c ctx t
typeCondition (Or l r)     ctx t = typeCondition l ctx t >> typeCondition r ctx t
typeCondition (And l r)    ctx t = typeCondition l ctx t >> typeCondition r ctx t
typeCondition (CChc f l r) ctx t = 
  (appCtxtToEnv (F.And ctx f) t 
  >>= typeCondition l (F.And ctx f))
  >> (appCtxtToEnv (F.And ctx (F.Not f)) t 
  >>= typeCondition r (F.And ctx (F.Not f)))

-- TODO have to complete the last three cases considering
-- that multiple instances of an attribute could exists
-- type env and we need to have a match with atom.
-- | Type checks a comparison.
typeComp :: MonadThrow m 
         => Atom -> Atom -> VariationalContext -> TypeEnv 
         -> m ()
typeComp a@(Val l)  a'@(Val r) _ t 
  | typeOf l == typeOf r = return ()
  | otherwise = throwM $ CompInvalid a a' t 
typeComp a@(Val l)  a'@(Att r) ctx t = 
  do is <- nonAmbiguousAttr r t 
     -- ats <- lookupAttrTypeFromEnv r t 
     -- afs <- lookupAttrFexpFromEnv r t 
     let validInfos = filter (\i -> F.tautImplyFexps (attrFexp i) ctx) 
                    $ filter (((==) (typeOf l)) . attrType) is 
     if null validInfos
      -- typeOf l `elem` (attrType is) && F.tautImplyFexps af ctx
     then throwM $ CompInvalid a a' t
     else return () 
typeComp a@(Att l) a'@(Val r)  ctx t = 
  do is <- nonAmbiguousAttr l t 
     let validInfos = filter (\i -> F.tautImplyFexps (attrFexp i) ctx) 
                    $ filter (((==) (typeOf r)) . attrType) is 
     if null validInfos
     then throwM $ CompInvalid a a' t
     else return ()  
    -- ats <- lookupAttrTypeFromEnv l t 
  --    afs <- lookupAttrFexpFromEnv l t 
  --    if typeOf r `elem` ats && F.tautImplyFexps af ctx
  --    then return () 
  --    else throwM $ CompInvalid a a' t
typeComp a@(Att l) a'@(Att r)  ctx t = 
  do lis <- nonAmbiguousAttr l t
     ris <- nonAmbiguousAttr r t 
     let validInfos = [ (li,ri) | li <- lis, ri <- ris
                      , attrType li == attrType ri
                      , F.tautImplyFexps (attrFexp li) ctx
                      , F.tautImplyFexps (attrFexp ri) ctx]
     if null validInfos 
     then throwM $ CompInvalid a a' t
     else return ()
  -- do lts <- lookupAttrTypeFromEnv l t 
  --    lfs <- lookupAttrFexpFromEnv l t 
  --    rts <- lookupAttrTypeFromEnv r t 
  --    rfs <- lookupAttrFexpFromEnv r t 
  --    if lt == rt && F.tautImplyFexps lf ctx && F.tautImplyFexps rf ctx
  --    then return ()
  --    else throwM $ CompInvalid a a' t

-- TESTED
-- | Unions two type envs for a choice query without checking the sat of 
--   fexps in the type map.
unionTypes_ :: TypeEnv -> TypeEnv -> TypeEnv
unionTypes_ t t' = 
  mkOpt (F.Or (getFexp t) (getFexp t'))
        (unionTypeMaps_ (getObj t) (getObj t'))

-- TESTED
-- | union type maps without checking the sat of fexps.
unionTypeMaps_ :: TypeMap -> TypeMap -> TypeMap
unionTypeMaps_ l r = SM.unionWith (appendAttrInfos_ F.Or) l r

-- TESTED
-- | Unions two type envs for a choice query and checks the sat of 
--   fexps in the type map.
unionTypes :: TypeEnv -> TypeEnv -> TypeEnv
unionTypes t t' = 
  mkOpt (F.Or (getFexp t) (getFexp t'))
        (unionTypeMaps (getObj t) (getObj t'))

-- TESTED
-- | union type maps without checking the sat of fexps.
unionTypeMaps :: TypeMap -> TypeMap -> TypeMap
unionTypeMaps l r = SM.unionWith (appendAttrInfos F.Or) l r

-- TODO check this
-- | intersects two types. 
intersectTypes :: MonadThrow m => TypeEnv -> TypeEnv -> m TypeEnv
intersectTypes l r = appCtxtToTypeMap f $ intersectTypeMaps (getObj l) (getObj r) 
  where
    f = F.And (getFexp l) (getFexp r)

-- | intersect type maps. 
intersectTypeMaps :: TypeMap -> TypeMap -> TypeMap
intersectTypeMaps l r = SM.intersectionWith (appendAttrInfos F.And) l r

-- | Gives the type of rename joins.
typeJoin :: MonadThrow m 
         => Algebra -> Algebra -> Condition
         -> VariationalContext -> Schema 
         -> m TypeEnv
typeJoin l r c ctx s = 
  do t <- typeProd l r ctx s 
     typeCondition c ctx t
     return t 

-- all helpers TESTED
-- | Gives the type of cross producting multiple rename relations.
typeProd :: MonadThrow m 
         => Algebra -> Algebra 
         -> VariationalContext -> Schema 
         -> m TypeEnv
typeProd l r ctx s = 
  do tl <- typeOfQuery l ctx s 
     tr <- typeOfQuery r ctx s 
     uniqueRelAlias tl tr 
     disjointTypes tl tr
     prodTypes tl tr 
     -- common <- intersectTypes tl tr
     -- if SM.null (getObj common)
     -- then prodTypes tl tr 
     -- else throwM $ TypeEnvIntersectNotEmpty tl tr

attinfo1 = [AttrInfo (F.Lit True) TString (RelQualifier (Relation "r1"))]
-- , 
     -- AttrInfo (F.Lit True) TString (RelQualifier (Relation "r2"))]
attinfo2 = [AttrInfo (F.Lit False) TString (RelQualifier (Relation "r2"))]
-- , 
--      AttrInfo (F.Lit True) TString (RelQualifier (Relation "r4"))]

typetst1 = ((F.Lit True), SM.fromList [(Attribute "a1"
  , [AttrInfo (F.Ref (F.Feature "f")) TString (RelQualifier (Relation "r1"))])])
-- , 
--      AttrInfo (F.Lit True) TString (RelQualifier (Relation "r2"))])
--   , (Attribute "a2"
--   , [AttrInfo (F.Lit True) TString (RelQualifier (Relation "r1")), 
--      AttrInfo (F.Lit True) TString (RelQualifier (Relation "r2"))])])
typetst2 = ((F.Lit True), SM.fromList [(Attribute "a1"
  , [AttrInfo (F.Not $ F.Ref (F.Feature "f")) TString (RelQualifier (Relation "r1"))])])
-- , 
--      AttrInfo (F.Lit True) TString (RelQualifier (Relation "r2"))])
--   , (Attribute "a2"
--   , [AttrInfo (F.Lit True) TString (RelQualifier (Relation "r3")), 
--      AttrInfo (F.Lit True) TString (RelQualifier (Relation "r4"))])])

-- TESTED
-- | checks if give type envs are disjoint w.r.t. relation.attribute.
-- the following is commented out. have to discuss it with Eric.
-- do we want to combine the naming scope with pcs?
--   and attriubtes pc. e.g. (π_{a^v_1} r × π_{a^¬v_1} r) shouldn't
--   return a disjoint error, it results in not having unique relation
--   names. 
disjointTypes :: MonadThrow m => TypeEnv -> TypeEnv -> m ()
disjointTypes l r 
  | null quals = return ()
  | otherwise = throwM $ TypeEnvNotDisjoint l r
    where 
      quals = [(a,rl,rr)| (a,(rinf,linf)) <- comb
        , rl <- map attrQual linf
        , rr <- map attrQual rinf
        , rr == rl]
        -- (rl,fl) <- map (\i -> (attrQual i, attrFexp i)) linf,
        -- (rr,fr) <- map (\i -> (attrQual i, attrFexp i)) rinf, 
        -- rl == rr, 
        -- satisfiable (F.And (F.And (typePC l) fl) (F.And (typePC r) fr))]
      comb = SM.toList $ SM.intersectionWith (,) (getObj l) (getObj r)

-- TESTED
-- | products two types, i.e., unions their map and 
--   then applies the conjunction of their fexps to them.
prodTypes :: MonadThrow m => TypeEnv -> TypeEnv -> m TypeEnv
prodTypes l r = appCtxtToTypeMap (F.And (getFexp l) (getFexp r)) 
                             (unionTypeMaps_ (getObj l) (getObj r))


-- | Products a list of types.
-- prodTypes :: MonadThrow m => TypeEnv -> TypeEnv -> m TypeEnv
-- prodTypes tl tr 
--   | satisfiable f = appCtxtToEnv f prodTypeMaps
--   | otherwise = throwM $ UnsatFexpsInProduct f
--     where 
--       f  = F.And fl fr 
--       fl = getFexp tl
--       fr = getFexp tr
--       prodTypeMaps = mkOpt f (SM.unionWith (++) (getObj tl) (getObj tr))

-- TESTED
-- | Checks that table/alias are unique. The relation names or
--   their aliases must be unique.
-- discuss with Eric: should we consider uniqueness w.r.t. pcs?
uniqueRelAlias :: MonadThrow m => TypeEnv -> TypeEnv -> m ()
uniqueRelAlias tl tr 
  | null relNs = return ()
  | otherwise  = throwM $ NotUniqueRelAlias relNs tl tr 
    where 
      relNs = relNames (getObj tl) `intersect` relNames (getObj tr)
      relNames envObj = nub $ fmap (qualName . attrQual) $ concatMap snd $ SM.toList envObj

-- TESTED
-- | appends two attr informations based on equality of quals.
--   if they're the same attr  
--   a given function is used to combine their fexps.
--   checks for satisfiability of generated
--   fexps in order to include the element in attr information.
appendAttrInfos :: (F.FeatureExpr -> F.FeatureExpr -> F.FeatureExpr)
                -- -> (SqlType -> SqlType -> Bool)
                -- -> (Qualifier -> Qualifier -> Bool)
                -> AttrInformation -> AttrInformation 
                -> AttrInformation
appendAttrInfos ff l r = shared ++ unshared
  where 
    shared = [AttrInfo f (attrType al) (attrQual al) 
            | al <- l, ar <- r, attrQual al == attrQual ar, 
              let f = ff (attrFexp al) (attrFexp ar), satisfiable f]
    sharedQuals = [ attrQual al | al<-l, ar<- r, attrQual al == attrQual ar]
    unshared = filter (\inf -> not $ (elem . attrQual) inf sharedQuals) l 
             ++ filter (\inf -> not $ (elem . attrQual) inf sharedQuals) r

-- TESTED
-- | appends two attr infor without checking for satisfiability.
--   because the ff function used already knows the result is 
--   satisfiable.
appendAttrInfos_ :: (F.FeatureExpr -> F.FeatureExpr -> F.FeatureExpr)
                 -- -> (SqlType -> SqlType -> Bool)
                 -- -> (Qualifier -> Qualifier -> Bool)
                 -> AttrInformation -> AttrInformation 
                 -> AttrInformation
appendAttrInfos_ ff l r = shared ++ unshared
  where 
    shared = [AttrInfo (ff (attrFexp al) (attrFexp ar)) (attrType al) (attrQual al) 
            | al <- l, ar <- r, attrQual al == attrQual ar]
    sharedQuals = [ attrQual al | al<-l, ar<- r, attrQual al == attrQual ar]
    unshared = filter (\inf -> not $ (elem . attrQual) inf sharedQuals) l 
             ++ filter (\inf -> not $ (elem . attrQual) inf sharedQuals) r

-- TESTED
-- | Returns the type of a rename relation.
typeRel :: MonadThrow m 
        => Relation -> VariationalContext -> Schema 
        -> m TypeEnv
typeRel r ctx s = 
  do tsch <- lookupTableSch r s 
     let t = tableSch2TypeEnv r tsch s
     appCtxtToEnv ctx t

-- TESTED
-- TODO: revise this. doesn't need to take the tableschema since
-- it can get it from the schema. if you're tableschema differs
-- then you need to have another function but if every time
-- you're callind this function you're looking up the tableschema
-- from the schema you should refactor.
-- | Generates a type env from a table schema and updates the pc
--   of the table by conjuncting it with schema's feature model.
tableSch2TypeEnv :: Relation -> TableSchema -> Schema -> TypeEnv 
tableSch2TypeEnv r tsch s = 
  updateOptObj (SM.map (optSqlType2AttInfo r) (getObj tsch)) 
             $ applyFuncFexp (F.And (featureModel s)) tsch 
  where 
    optSqlType2AttInfo rel ot = pure $ AttrInfo (getFexp ot) (getObj ot) 
      $ RelQualifier rel
              -- (\n -> RelQualifier (Relation n)) 
              -- (name r)

-- | Applies a variational ctxt to a type and drops the elements 
--   that their pc is unsatisfiable. This is based on theory that
--   applying a ctxt to env if f is unsat results in an empty env.
--   However, in practice, this should be distinguishable from
--   the case where env is empty itself and it exists. so when
--   the pc of env is false we preferably return an error.
-- appCtxtToEnv_ :: VariationalContext -> TypeEnv -> TypeEnv
-- appCtxtToEnv_ ctx t 
--     | satisfiable f = mkOpt f $ appCtxtToMap f (getObj t)
--     | otherwise = mkOpt (F.Lit False) SM.empty
--   where 
--     f = F.shrinkFeatureExpr (F.And ctx $ getFexp t)
--     appCtxtToMap fexp envMap = SM.filter null (SM.map (appCtxtToAttInfo fexp) envMap)
--     appCtxtToAttInfo fexp is = filter (\i -> F.satAnds fexp (attrFexp i)) is


-- | Applies a variational ctxt to a type.
appCtxtToEnv :: MonadThrow m => VariationalContext -> TypeEnv -> m TypeEnv
appCtxtToEnv ctx t 
    | satisfiable f = appCtxtToTypeMap f (getObj t) >>= return . updateFexp (F.shrinkFeatureExpr f) 
    | otherwise = throwM $ CtxUnsatOverEnv ctx t
  where 
    f = F.And ctx $ getFexp t
    -- appCtxtToMap fexp envMap = SM.filter null (SM.map (appCtxtToAttInfo fexp) envMap)
    -- appCtxtToAttInfo fexp is = filter (\i -> F.satAnds fexp (attrFexp i)) is

-- TESTED
-- | applies a fexp to type map.
appCtxtToTypeMap :: MonadThrow m => F.FeatureExpr -> TypeMap -> m TypeEnv
appCtxtToTypeMap f m 
  | satisfiable f = return $ mkOpt f $ SM.filter (not . null) (SM.map (appCtxtToAttInfo f) m)
  | otherwise = throwM $ UnsatFexAppliedToTypeMap f m
  where 
    -- appCtxtToMap fexp envMap = SM.filter null (SM.map (appCtxtToAttInfo fexp) envMap)
    appCtxtToAttInfo fexp is = filter (satisfiable . attrFexp ) $ applyFuncToAttFexp (F.And fexp) is



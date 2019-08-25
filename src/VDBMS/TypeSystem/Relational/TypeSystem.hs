-- | Statically syntesizes the types of relational queries.
module VDBMS.TypeSystem.Relational.TypeSystem 
(

        RTypeEnv
        , RAttrInfo(..)
        , typeOfRQuery
        , updateType

) where 

import qualified Data.Map as M 
import qualified Data.Map.Strict as SM
import qualified Data.Set as Set 
import Data.Set (Set)
import Data.List (intersect, nub, (\\))

import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Control.Monad.Catch 

import VDBMS.VDB.Schema.Relational.Types
import VDBMS.VDB.Schema.Relational.Lookups
import VDBMS.QueryLang.SQL.Condition
import VDBMS.QueryLang.RelAlg.Relational.Algebra
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Value (typeOf,SqlType)

-- | Attribute information for relational type env.
data RAttrInfo 
  = RAttrInfo {
      rAttrType :: SqlType
    , rAttrQual :: Qualifier
    }
 deriving (Data,Ord,Eq,Show,Typeable)

-- | Comprehensive attribute information required for 
--   relational type env.
type RAttrInformation = [RAttrInfo]

-- | Relational type env.
type RTypeEnv = M.Map Attribute RAttrInformation

-- | Type enviornment errors.
data RTypeError = 
    RCompInvalid Atom Atom RTypeEnv
  | RNotEquiveTypeEnv RTypeEnv RTypeEnv 
  | RQualNotInInfo Qualifier RAttrInformation
  | RAttrQualNotInTypeEnv Attr RTypeEnv
  | RAttrNotInTypeEnv Attribute RTypeEnv
  | REmptyAttrList Attributes (Rename RAlgebra)
  | RAmbiguousAttr Attr RTypeEnv
  | RNotUniqueRelAlias RTypeEnv RTypeEnv
  | RInOpMustContainOneClm RTypeEnv
  | RMissingAlias (Rename RAlgebra)
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception RTypeError 

-- | static semantics that returns a relational table schema.
typeOfRQuery :: MonadThrow m => RAlgebra -> RSchema -> m RTypeEnv
typeOfRQuery (RSetOp o l r)    s = 
  do tl <- typeOfRQuery l s
     tr <- typeOfRQuery r s
     sameRType tl tr 
     return tl
typeOfRQuery q@(RProj as rq)     s = validSubQ rq >> typeRProj as rq s 
typeOfRQuery q@(RSel c rq)       s = 
  do validSubQ rq
     t  <- typeOfRQuery (thing rq) s
     let t' = updateType (name rq) t
     typeSqlCond c t' s
     return t'
typeOfRQuery (RJoin rl rr c)   s = typeJoin rl rr c s 
typeOfRQuery (RProd rl rr )    s = typeRProd rl rr s
typeOfRQuery (RTRef rr)        s = typeRRel rr s 
typeOfRQuery REmpty            _ = return M.empty

-- | Checks if two type are the same.
sameRType :: MonadThrow m 
           => RTypeEnv -> RTypeEnv 
           -> m ()
sameRType lt rt 
  | compRTypes (\_ _ -> True) (==) lt rt = return ()
  | otherwise = throwM $ RNotEquiveTypeEnv lt rt

compRTypes :: (SqlType -> SqlType -> Bool)
           -> (Qualifier -> Qualifier -> Bool)
           -> RTypeEnv -> RTypeEnv -> Bool 
compRTypes tf qf lt rt = SM.keysSet lt == SM.keysSet rt
  && envsEq
  where
    envsEq = SM.isSubmapOfBy (eqRAttInfo tf qf) lt rt 
          && SM.isSubmapOfBy (eqRAttInfo tf qf) rt lt 
    eqRAttInfo t q lis ris = length lis == length ris
      && null (lqs \\ rqs)
      && null (rqs \\ lqs)
      && and res 
      where
        lqs = fmap rAttrQual lis
        rqs = fmap rAttrQual ris 
        res = [ t (rAttrType li) (rAttrType ri) 
                | li <- lis, ri <- ris, q (rAttrQual li) (rAttrQual ri) ]

-- | Determines the type of a relational projection.
typeRProj :: MonadThrow m 
          => Attributes -> Rename RAlgebra -> RSchema
          -> m RTypeEnv
typeRProj as rq s 
  | null as = throwM $ REmptyAttrList as rq
  | otherwise =
    do t   <- typeOfRQuery (thing rq) s
       let t'  = updateType (name rq) t 
       updateAttrs as t'

-- | Checks if a subquery is valid within a selection or projection.
--   Assumption: optimization has already been done. so we don't have 
--   an unncessary combination of selections and projections in a query.
-- TODO: You may need to add more cases to this! Come back to this after
--       opt rules.
validSubQ :: MonadThrow m => Rename RAlgebra -> m ()
validSubQ rq@(Rename a (RSetOp _ _ _)) = 
  maybe (throwM $ RMissingAlias rq) (\_ -> return ()) a 
validSubQ _ = return ()

-- | Adjusts a relational type env with a new name.
--   Ie. it adds the name, if possible, to all 
--   attributes qualifiers.
updateType :: Alias -> RTypeEnv -> RTypeEnv
updateType a t = maybe t (\n -> SM.map (appName n) t) a
  where
    appName :: String -> RAttrInformation -> RAttrInformation
    appName n = fmap (updateQual (SubqueryQualifier n))
    updateQual q (RAttrInfo at aq) = RAttrInfo at q

-- | Projects one attribute from a type.
projAtt :: MonadThrow m => Attr -> RTypeEnv -> m RTypeEnv
projAtt a t = 
  do i <- nonAmbiguousAttr a t
     return $ SM.singleton (attribute a) (pure i)

-- | Update the attribute names to their new name if available.
updateAttrs :: MonadThrow m => Attributes -> RTypeEnv -> m RTypeEnv
updateAttrs as t = 
  do ts <- mapM (flip updateAtt t) as
     return $ SM.unionsWith (++) ts

-- | Gives a type env of only the given attribute.
updateAtt :: MonadThrow m => Rename Attr -> RTypeEnv -> m RTypeEnv
updateAtt ra t =
  do tOfa <- projAtt (thing ra) t 
     return $ maybe tOfa (\n -> SM.mapKeys (\_ -> Attribute n) tOfa) (name ra)

-- | checks if an attribute used in conditions etc is ambiguous or not
--   wrt the type env.
nonAmbiguousAttr :: MonadThrow m => Attr -> RTypeEnv -> m RAttrInfo
nonAmbiguousAttr a t = 
  do i <- lookupAttr (attribute a) t 
     qs <- lookupAttrQuals (attribute a) t
     if length qs > 1 
     then maybe (throwM $ RAmbiguousAttr a t) (lookupAttrInfo i) (qualifier a)
     else return $ head i

-- | looks up attr info for a qualifier.
lookupAttrInfo  ::  MonadThrow m
                => RAttrInformation -> Qualifier
                -> m RAttrInfo
lookupAttrInfo i q = 
  maybe 
    (throwM $ RQualNotInInfo q i)
    (\t -> return $ RAttrInfo t q)
    (lookup q $ zip (fmap rAttrQual i) (fmap rAttrType i))

-- | Returns all qualifiers for an attribute in a type.
lookupAttrQuals :: MonadThrow m => Attribute -> RTypeEnv -> m [Qualifier]
lookupAttrQuals a t = 
  do i <- lookupAttr a t 
     return $ fmap rAttrQual i

-- | Looks up attribute information from the type.
lookupAttr :: MonadThrow m => Attribute -> RTypeEnv -> m RAttrInformation
lookupAttr a t = 
  maybe 
  (throwM $ RAttrNotInTypeEnv a t)
  return
  (SM.lookup a t)

-- | Checks if an attribute (possibly with its qualifier) exists in a type env.
attrInType :: MonadThrow m 
           => Attr -> RTypeEnv
           -> m ()
attrInType a t = 
  do i <- nonAmbiguousAttr a t
     maybe (return ()) 
           (\q -> if q == rAttrQual i 
                  then return () 
                  else throwM $ RAttrQualNotInTypeEnv a t)
           (qualifier a) 

-- | looks up the type of an attribute in the env.
lookupAttrTypeInEnv :: MonadThrow m
                    => Attr -> RTypeEnv
                    -> m SqlType
lookupAttrTypeInEnv a t = 
  do i <- nonAmbiguousAttr a t
     return $ rAttrType i

-- | Checks if the sql condition is consistent with 
--   the relational type env and schema.
typeSqlCond :: MonadThrow m 
            => SqlCond RAlgebra -> RTypeEnv -> RSchema
            -> m ()
typeSqlCond (SqlCond c)  t s = typeRCondition c t
typeSqlCond (SqlIn a q)  t s = typeOfRQuery q s >>= onlyAttrInType a t
typeSqlCond (SqlNot c)   t s = typeSqlCond c t s 
typeSqlCond (SqlOr l r)  t s = typeSqlCond l t s >> typeSqlCond r t s
typeSqlCond (SqlAnd l r) t s = typeSqlCond l t s >> typeSqlCond r t s
 
-- | Checks if the attribute is the only attribute of a type env.
--   Helper for the In queries.
onlyAttrInType :: MonadThrow m 
               => Attr -> RTypeEnv -> RTypeEnv
               -> m ()
onlyAttrInType a tenv tq = 
  do attrInType a tenv
     if Set.null $ attribute a `Set.delete` SM.keysSet tq 
     then return ()
     else throwM $ RInOpMustContainOneClm tq

-- | Checks if the relational condition is consistent 
--   with the relational type env.
typeRCondition :: MonadThrow m
               => RCondition -> RTypeEnv
               -> m ()
typeRCondition (RLit b)      t = return () 
typeRCondition (RComp _ l r) t = typeComp l r t 
typeRCondition (RNot c)      t = typeRCondition c t
typeRCondition (ROr l r)     t = typeRCondition l t >> typeRCondition r t
typeRCondition (RAnd l r)    t = typeRCondition l t >> typeRCondition r t

-- | Checks if the comparison is consistent with 
--   relational type env.
typeComp :: MonadThrow m
         => Atom -> Atom -> RTypeEnv
         -> m ()
typeComp a@(Val l)  a'@(Val r)  t 
  | typeOf l == typeOf r = return ()
  | otherwise = throwM $ RCompInvalid a a' t 
typeComp a@(Val l)  a'@(Att r) t = 
  do at <- lookupAttrTypeInEnv r t
     if typeOf l == at 
     then return ()
     else throwM $ RCompInvalid a a' t
typeComp a@(Att l) a'@(Val r)  t = 
  do at <- lookupAttrTypeInEnv l t
     if typeOf r == at 
     then return ()
     else throwM $ RCompInvalid a a' t
typeComp a@(Att l) a'@(Att r) t = 
  do at  <- lookupAttrTypeInEnv l t
     at' <- lookupAttrTypeInEnv r t
     if at == at'
     then return ()
     else throwM $ RCompInvalid a a' t

-- | Gives the type of rename joins.
typeJoin :: MonadThrow m 
         => Rename RAlgebra -> Rename RAlgebra -> RCondition -> RSchema
         -> m RTypeEnv
typeJoin rl rr c s = 
  do t <- typeRProd rl rr s 
     typeRCondition c t 
     return t 

-- | Gives the type of cross producting multiple rename relations.
typeRProd :: MonadThrow m 
          => Rename RAlgebra -> Rename RAlgebra -> RSchema
          -> m RTypeEnv
typeRProd rl rr s = 
  do tl <- typeOfRQuery (thing rl) s
     tr <- typeOfRQuery (thing rr) s
     uniqueRelAlias tl tr
     return $ prodRTypes (pure tl ++ pure tr)

-- | Gets a list of relational type env and product them.
--   i.e., for repeated attributes accumulates the qualifiers.
--   Note that it's ok if the same attributes with different 
--   qualifiers have different types. 
--   You need to make sure that types are disjoint, i.e., you 
--   can't have: t.A and t.A but you can have t.A and r.A.
--   uniqueRelAlias in typeRProd is taking care of this.
--   So while combining lists of attr info for a given attr
--   we don't need to check this anymore.
prodRTypes :: [RTypeEnv] -> RTypeEnv
prodRTypes ts = SM.unionsWith combAttInfos ts

-- | Combines attr informations. 
combAttInfos = (++) 

-- | Checks that table/alias are unique. The relation names or
--   their aliases must be unique.
uniqueRelAlias :: MonadThrow m => RTypeEnv -> RTypeEnv -> m ()
uniqueRelAlias lt rt 
  | null (relNames lt `intersect` relNames rt) = return ()
  | otherwise = throwM $ RNotUniqueRelAlias lt rt 
    where
      relNames :: RTypeEnv -> [String]
      relNames t = nub $ fmap (qualName . rAttrQual) 
                            $ concatMap snd $ SM.toList t 

-- | Returns the type of a rename relation.
typeRRel :: MonadThrow m 
          => Rename Relation -> RSchema
          -> m RTypeEnv
typeRRel rr s = 
  do r <- rlookupRelation (thing rr) s
     return $ SM.map (sqlType2RAttrInfo rr) r 

-- | Generates a relational attr info from a rename relation and sql type.
--   If a name alias exists for the relation it considers it as the new 
--   name for the sql type, otherwise it attaches the relation name itself
--   to the sqltype.
sqlType2RAttrInfo :: Rename Relation -> SqlType -> RAttrInformation
sqlType2RAttrInfo rel at = pure $ 
  RAttrInfo at 
          $ maybe (RelQualifier (Relation relName))
                  (\n -> RelQualifier (Relation n)) 
                  newName
  where 
    relName = relationName $ thing rel 
    newName = name rel 
  



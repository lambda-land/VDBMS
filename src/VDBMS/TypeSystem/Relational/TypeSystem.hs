-- | Statically syntesizes the types of relational queries.
module VDBMS.TypeSystem.Relational.TypeSystem 
(

        RTypeEnv
        , typeOfRQuery

) where 

import qualified Data.Map as M 
import qualified Data.Map.Strict as SM
import qualified Data.Set as Set 
import Data.Set (Set)
import Data.List (nub)

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
type RTypeEnv = SM.Map Attribute RAttrInformation

-- | Type enviornment errors.
data RTypeError = 
    RCompInvalid Atom Atom RTypeEnv
  | RNotEquiveTypeEnv RTypeEnv RTypeEnv 
  | RQualNotInInfo Qualifier RAttrInformation
  | RAttrQualNotInTypeEnv Attr RTypeEnv
  | RAttrNotInTypeEnv Attribute RTypeEnv
  | REmptyAttrList RAlgebra
  | RAmbiguousAttr Attr RTypeEnv
  | RNotUniqueRelAlias [Rename Relation]
  | RInOpMustContainOneClm RTypeEnv
  | RMissingAlias (Rename RAlgebra)
    deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception RTypeError 

-- | static semantics that returns a relational table schema.
typeOfRQuery :: MonadThrow m => RAlgebra -> RSchema -> m RTypeEnv
typeOfRQuery (RSetOp o l r)    s = 
  do tl <- typeOfRQuery l s
     tr <- typeOfRQuery r s
     sameType tl tr 
     return tl
typeOfRQuery q@(RProj as rq)     s = validSubQ rq >> typeRProj as rq s 
typeOfRQuery q@(RSel c rq)       s = 
  do validSubQ rq
     t  <- typeOfRQuery (thing rq) s
     let t' = updateType (name rq) t
     typeSqlCond c t' s
     return t'
typeOfRQuery (RJoin js)        s = typeJoins js s 
typeOfRQuery (RProd rl rr rrs) s = typeRProd (rl : rr : rrs) s
typeOfRQuery (RTRef rr)        s = typeRRel rr s 
typeOfRQuery REmpty            _ = return M.empty

-- | Determines the type of set operations.
sameType :: MonadThrow m 
           => RTypeEnv -> RTypeEnv 
           -> m ()
sameType tl tr 
  | SM.keysSet tl == SM.keysSet tr = return ()
  | otherwise = throwM $ RNotEquiveTypeEnv tl tr

-- | Determines the type of a relational projection.
typeRProj :: MonadThrow m 
          => Attributes -> Rename RAlgebra -> RSchema
          -> m RTypeEnv
typeRProj as rq s = 
  do t   <- typeOfRQuery (thing rq) s
     let t'  = updateType (name rq) t 
     -- t'' <- projAtts (fmap thing as) t
     updateAttrs as t'

-- | Checks if a subquery is valid within a selection or projection.
--   Assumption: optimization has already been done. so we don't have 
--   an unncessary combination of selections and projections in a query.
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

-- | Projects a list of attributes from the type.
-- projAtts :: MonadThrow m => [Attr] -> RTypeEnv -> m RTypeEnv
-- projAtts as t = 
--   do mapM_ (flip attrInType t) as
--      ts <- mapM (flip projAtt t) as 
--      return $ SM.unionsWith (++) ts 

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
  (\i -> return i)
  (SM.lookup a t)

-- | Checks if an attribute (possibly with its qualifier) exists in a type env.
attrInType :: MonadThrow m 
           => Attr -> RTypeEnv
           -> m ()
attrInType a t = 
  do qs <- lookupAttrQuals (attribute a) t
     maybe (return ()) 
           (\q -> if q `elem` qs 
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
typeJoins :: MonadThrow m 
          => RJoins -> RSchema
          -> m RTypeEnv
typeJoins j@(RJoinTwoTable rl rr c) s = 
  do uniqueRelAlias $ relJoins j
     tl <- typeRRel rl s 
     tr <- typeRRel rr s 
     t <- prodRTypes (pure tl ++ pure tr)
     typeRCondition c t
     return t
typeJoins j@(RJoinMore js rr c)     s = 
  do uniqueRelAlias $ relJoins j
     ts <- typeJoins js s
     tr <- typeRRel rr s
     t <- prodRTypes $ pure ts ++ pure tr
     typeRCondition c t
     return t

-- | Gets the relations/aliases from the joins.
relJoins :: RJoins -> [Rename Relation]
relJoins (RJoinTwoTable rl rr c) = pure rl ++ pure rr 
relJoins (RJoinMore js rr c)     = relJoins js ++ pure rr

-- | Gives the type of cross producting multiple rename relations.
typeRProd :: MonadThrow m 
          => [Rename Relation] -> RSchema
          -> m RTypeEnv
typeRProd rrs s = 
  do uniqueRelAlias rrs 
     ts <- mapM (flip typeRRel s) rrs
     t <- prodRTypes ts
     return $ t

-- | Gets a list of relational type env and product them.
--   i.e., for repeated attributes accumulates the qualifiers.
--   Note that it's ok if the same attributes with different 
--   qualifiers have different types. 
--   You need to make sure that types are disjoint, i.e., you 
--   can't have: t.A and t.A but you can have t.A and r.A.
--   uniqueRelAlias in typeRProd is taking care of this.
--   So while combining lists of attr info for a given attr
--   we don't need to check this anymore.
prodRTypes :: MonadThrow m => [RTypeEnv] -> m RTypeEnv
prodRTypes ts = return $ SM.unionsWith combAttInfos ts

-- | combinees attr informations. 
combAttInfos = (++) 

-- | Checks that table/alias are unique. The relation names or
--   their aliases must be unique.
uniqueRelAlias :: MonadThrow m => [Rename Relation] -> m ()
uniqueRelAlias rrs 
  | nub relNames == relNames = return ()
  | otherwise                = throwM $ RNotUniqueRelAlias rrs
    where
      relNames  = fmap relName rrs
      relName r = maybe (thing r) Relation (name r)

-- | Returns the type of a rename relation.
typeRRel :: MonadThrow m 
          => Rename Relation -> RSchema
          -> m RTypeEnv
typeRRel rr s = 
  do r <- lookupRelation (thing rr) s
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
  



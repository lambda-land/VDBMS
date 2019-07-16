-- | Variational database schema core operations.
module VDBMS.VDB.Schema.Variational.Core (

        relArity,
        getRowTypeAtts,
        getTableSchAtts,
        getAttTypeFromRowType,
        getRels,
        propagateFexpToTsch,
        shrinkFexRowType,
        combineTableSchema,
        rowTypeUnion

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Merge.Strict as StrictM
import Data.List 

import VDBMS.VDB.Schema.Variational.Types
import VDBMS.VDB.Schema.Variational.Lookups
import VDBMS.VDB.Schema.Variational.ApplyFexp
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Name
import VDBMS.Variational.Opt
import VDBMS.DBMS.Value.Value (SqlType)

-- | returns a relation arity.
relArity :: Relation -> Schema -> Int 
relArity r s = case rt of 
                 Just rowType -> M.size rowType
                 _ -> 0
  where 
    rt = lookupRel r s

-- | get attributes of a rowtype.
getRowTypeAtts :: RowType -> Set Attribute
getRowTypeAtts = M.keysSet

-- | get attributes of a table schema.
getTableSchAtts :: TableSchema -> Set Attribute
getTableSchAtts t = getRowTypeAtts $ getObj t

-- | Get attribute type pairs in a rowtype
getAttTypeFromRowType :: RowType -> Set (Attribute, SqlType)
getAttTypeFromRowType r = dropFexp rowSet
  where
    rowSet = Set.fromList $ M.assocs r
    dropFexp :: (Ord a, Ord t) => Set (a,(o,t)) -> Set (a,t)
    dropFexp = Set.map (\(a,(_,t)) -> (a,t)) 

-- | gets valid relations of a schema. i.e. relations that
--   their fexp isn't false.
getRels :: Schema -> Set Relation
getRels s = Set.filter (flip validRel $ s) rels
  where 
    rels = M.keysSet $ schemaStrct s
    validRel :: Relation -> Schema -> Bool
    validRel r s 
      | lookupRelationFexp r s == Just (Lit False) = False
      | lookupRelationFexp r s == Nothing = False
      | otherwise = True

-- | propagates the table pres cond to its attributes.
propagateFexpToTsch :: TableSchema -> TableSchema 
propagateFexpToTsch t = mkOpt (shrinkFeatureExpr tf) $ shrinkFexRowType $ appFexpRowType tf t
  where
    tf = getFexp t

-- | shrinks the feature expression of all attributes in a row type
shrinkFexRowType :: RowType -> RowType
shrinkFexRowType = M.map (\(f,t) -> (shrinkFeatureExpr f,t))

------------- constructing table schema (opt rowtype) ----------

-- | constructs a table schema from a list of them
combineTableSchema :: [TableSchema] -> TableSchema
combineTableSchema tss = mkOpt fexp rowType
  where
    fexp = disjFexp $ map getFexp tss
    rowType = foldl' rowTypeUnion M.empty $ map getObj tss

rowTypeUnion :: RowType -> RowType -> RowType
rowTypeUnion e e' = StrictM.merge 
                   StrictM.preserveMissing 
                   StrictM.preserveMissing 
                   matched e e'
  where 
    matched = StrictM.zipWithMaybeMatched (\_ (o,t) (o',t') -> 
      case t==t' of
        True -> Just ((Or o o'),t)
        _    -> Nothing)

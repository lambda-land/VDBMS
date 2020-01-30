-- | Variational database schema core operations.
module VDBMS.VDB.Schema.Variational.Core (

        relArity
        , filterRowType
        , filterTSch
        -- , filterSchema
        , getRowTypeAtts
        , getTableSchAtts
        , getTableSchAttsList
        , getAttTypeFromRowType
        , getRels
        , propagateFexpToTsch
        , shrinkFexRowType
        , combineTableSchema
        , rowTypeUnion
        , dropAttTypeFromRowType

) where

-- import Data.Map.Strict (Map)
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
import VDBMS.Features.SAT (satisfiable)

-- | drops the attribute with unsat fexp.
filterRowType :: RowType -> RowType
filterRowType = M.filter (satisfiable . fst) 

-- | drops the attribute that their fexp conjuncted with 
--   the table schema fexp isn't satisfiable.
filterTSch :: TableSchema -> TableSchema
filterTSch t = updateOptObj (M.filter (\v -> satAnds f (fst v)) rt) t
  where
    f = tschFexp t
    rt = tschRowType t 

-- | drops the attribute that their fexp conjuncted with 
--   the table schema fexp and a given fexp isn't satisfiable.
-- filterTSch' :: FeatureExpr -> TableSchema -> TableSchema
-- filterTSch' p t 
--   = updateOptObj (M.filter (\v -> satAnds (And f p) (fst v)) rt) t
--   where
--     f = tschFexp t
--     rt = tschRowType t 

-- | drops the objects that their fexp conjuncted with the 
--   higher level fexp isn't satisfiable.
-- filterSchema :: Schema -> Schema
-- filterSchema = undefined
-- filterSchema s = undefined
  -- updateOptObj (mapSnd (M.filter M.null)
  -- (mapSnd (M.map (filterTSch' f)) ss)) s
  -- where
    -- f = featureModel s 
    -- ss = schemaStrct s 

-- | returns a relation arity.
relArity :: Relation -> Schema -> Int 
relArity r s = case rt of 
                 Just rowType -> M.size rowType
                 _ -> 0
  where 
    rt = lookupRel r s

-- | get attributes of a rowtype.
getRowTypeAtts :: RowType -> Set Attribute
getRowTypeAtts = M.keysSet . filterRowType

-- | get attributes of a table schema.
getTableSchAtts :: TableSchema -> Set Attribute
getTableSchAtts t = getRowTypeAtts $ getObj t

-- | gives the list of attributes.
getTableSchAttsList :: TableSchema -> [Attribute]
getTableSchAttsList t = Set.toList $ getTableSchAtts t

-- | Get attribute type pairs in a rowtype
getAttTypeFromRowType :: RowType -> Set (Attribute, SqlType)
getAttTypeFromRowType r = dropFexp rowSet
  where
    rowSet = Set.fromList $ M.assocs (filterRowType r)
    dropFexp :: (Ord a, Ord t) => Set (a,(o,t)) -> Set (a,t)
    dropFexp = Set.map (\(a,(_,t)) -> (a,t)) 

-- | gets valid relations of a schema. i.e. relations that
--   their fexp isn't false.
getRels :: Schema -> Set Relation
getRels s = Set.filter (flip validRel $ s) rels
  where 
    rels = M.keysSet $ schemaStrct s
    validRel :: Relation -> Schema -> Bool
    validRel r sch 
      | lookupRelationFexp r sch == Just (Lit False) = False
      | lookupRelationFexp r sch == Nothing = False
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

-- | takes a rowtype and drops sqltype and returns a list of opt att.
dropAttTypeFromRowType :: RowType -> [Opt Attribute]
dropAttTypeFromRowType r = map (\(l,r) -> (r,l)) $ M.toList $ M.map getFexp r 

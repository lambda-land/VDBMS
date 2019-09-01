-- | Consistency checks of VTables.
-- TODO: write the checks according to the new data type.
module VDBMS.VDB.Table.Checks where 

-- import VDBMS.VDB.Table.Core 

{--
-- | A database is a mapping from relations to tables.
type Database = (Schema, Map Relation Table)

-- | A table is a list of vtuples.
type Table = [VTuple]

-- | A table with an assigned feature exp for when 
--   you're returning a table without an assigned name
--   (relation) to it. 
type VTable = Opt Table

-- | A vtuple is an optional map between attributes 
--   and their sqlvalues, where each value may be 
--   Nothing if the corresponding attribute is not 
--   present in a configuration.
type VTuple = Opt (Map Attribute (Maybe SqlValue))



-- | Check a value against the attribute-type pair in a row type.
checkValue :: FeatureExpr -> Attribute -> Opt SqlType -> Maybe SqlValue -> Bool
checkValue ctx a (p,t) Nothing  = unsatisfiable (And ctx p)
checkValue ctx a (p,t) (Just v) = satisfiable (And ctx p) 
  -- && (t == typeOf v || typeOf v == TNull) -- need to be added
  -- for sqltype and sqlvalue

-- | Check a vtuple against a row type. Ensures that the list of 
--   attributes in rowtype and vtuples are the same. checks sat
--   of attPrescond and vtuplePresCond
checkVTuple :: FeatureExpr -> PresCondAtt -> RowType -> VTuple -> Bool
checkVTuple ctx p row t = getVTupleAtts t p == getRowTypeAtts row
  && and (M.elems checkValues) 
  where 
    checkValues :: Map Attribute Bool
    checkValues = M.intersectionWithKey (checkValue attPresCondAndVTuplePresCond) 
                                      row (snd t)
    attPresCondAndVTuplePresCond = And ctx (fst t)

-- | Validate a table against its row type. When checking
--   the initialized VDB ctx will be the rowtype fexp.
checkTable :: FeatureExpr -> PresCondAtt -> RowType -> Table -> Bool
checkTable ctx p row ts = all (checkVTuple ctx p row) ts

-- | Validate a database against its schema. Have to check
--   the VDB after instantiate it.
checkDatabase :: Database -> PresCondAtt -> Bool
checkDatabase db p = and (M.mapWithKey checkRelation dbData)
  where 
    schema = getSchema db 
    dbData = getData db
    checkRelation relation table
      | Just row <- lookupRel relation (schema)
        = case lookupRelationFexp relation schema of
            Just fexp -> checkTable (And (featureModel schema) fexp) p row table
            _ -> False
      | otherwise = False

-- checkDatabase (fm,rows) db = M.size rows == M.size db
--     && and (M.mapWithKey checkRelation rows)
--   where
--     checkRelation name (p,row)
--       | Just table <- M.lookup name db = checkTable (And fm p) row table
--       | otherwise = False
--}

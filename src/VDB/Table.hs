-- | Representation of tuples and tables for interpreting variational queries.
module VDB.Table where

import VDB.FeatureExpr
import VDB.Name
import VDB.SAT
import VDB.Variational
import VDB.Value


-- | A tuple is an optional list of values, where each value may be Nothing if
--   the corresponding attribute is not present in the schema.
type Tuple = Opt [Maybe Value]

-- | The schema of a single relation. Contains its name and a variational
--   list of attribute-type pairs.
type Schema = (Relation, [Opt (Attribute,Type)])

-- | A table encodes a relation. It contains the schemas and a list of tuples.
type Table = (Schema, [Tuple])

-- | Check a value in a tuple against an attribute entry in a schema.
checkValue :: FeatureExpr -> Opt (Attribute,Type) -> Maybe Value -> Bool
checkValue pv (pa,_)     Nothing  = unsatisfiable (And pv pa)
checkValue pv (pa,(_,t)) (Just v) = satisfiable (And pv pa) && t == typeOf v

-- | Check a tuple against a schema.
checkTuple :: Schema -> Tuple -> Bool
checkTuple (_,attrs) (pv,vs) = length attrs == length vs
                                 && and (zipWith (checkValue pv) attrs vs)

-- | Validate a table against its schema.
checkTable :: Table -> Bool
checkTable (schema,tuples) = all (checkTuple schema) tuples

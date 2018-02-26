-- | Representation of tuples and tables for interpreting variational queries.
module VDB.Table where

import VDB.Config
import VDB.Name
import VDB.Variational
import VDB.Value


-- | A tuple is a variational list of values.
type Tuple = [Opt Value]

-- | The schema of a single relation. Contains its name and a variational
--   list of attribute-type pairs.
type Schema = (Relation, [Opt (Attribute,Type)])

-- | A table encodes a relation. It contains the schemas and a list of tuples.
type Table = (Schema, [Tuple])

-- | Validate a table against its schema for a particular configuration.
checkTable :: Config Bool -> Table -> Bool
checkTable c ((_,attrs), tuples) = all check (map (configureOptList c) tuples)
  where
    types = map snd (configureOptList c attrs)
    arity = length types
    check vs = arity == length vs && and (zipWith (==) types (map typeOf vs))

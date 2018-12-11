-- | Data types needed for specific variants of a database.
module VDB.Variant where

import VDB.Schema
import VDB.Table
import VDB.Config
import VDB.Name


-- | A variant of a variational thing tagged by its configuration.
type Variant a b = (Config a, b)

-- | A variant table. All fexp must be true or false!
--   TODO: write func to check this!!
type VariantTable = Variant Bool Table

-- | A variant schema. All fexp must be true or false!
--   TODO: write func to check this!!
type VariantSchema = Variant Bool Schema

-- | A varaint database. All fexp must be true or false!
--   TODO: write func to check this!!
type VariantDatabase = Variant Bool Database
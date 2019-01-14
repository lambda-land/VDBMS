-- | Data types needed for specific variants of a database.
module VDB.Variant where

import VDB.Schema
import VDB.Table
import VDB.Config
-- import VDB.Name

-- | A variant of a variational thing tagged by its configuration.
type Variant a b = (a, Config b)

-- | returns the obj of a variant.
getVariant :: Variant a b -> a
getVariant = fst

-- | returns the config of a variant.
getConfig :: Variant a b -> Config b 
getConfig = snd

-- | constructs a variant.
mkVariant :: a -> Config b -> Variant a b
mkVariant = (,)

-- | A variant table. All fexp must be true or false!
--   TODO: write func to check this!!
type VariantTable = Variant Table Bool

-- | A variant schema. All fexp must be true or false!
--   TODO: write func to check this!!
type VariantSchema = Variant Schema Bool

-- | A variant database. All fexp must be true or false!
--   TODO: write func to check this!!
type VariantDatabase = Variant Database Bool

-- | A variant HDBC database. Doesn't have fexp.
-- type VariantHDBC = Variant Bool (IConnection conn)
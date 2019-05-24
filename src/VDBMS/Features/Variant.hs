-- | Data types needed for specific variants of a database.
module VDBMS.Features.Variant (

        Variant,
        getVariant,
        getConfig,
        mkVariant,
        updateVariant,
        updateConfig,

) where

-- import VDBMS.VDB.Schema
-- import VDBMS.VDB.Table
import VDBMS.Features.Config (Config)
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

-- | update variant. keeps the config the same.
updateVariant :: a -> Variant a b -> Variant a b
updateVariant v (_,c) = (v,c)

-- | update config. keeps the variant the same.
updateConfig :: Config b -> Variant a b -> Variant a b
updateConfig c (v,_) = (v,c)

-- | A variant table. All fexp must be true or false!
--   TODO: write func to check this!!
-- type VariantTable = Variant Table Bool

-- | A variant schema. All fexp must be true or false!
--   TODO: write func to check this!!
-- type VariantSchema = Variant Schema Bool

-- | A variant database. All fexp must be true or false!
--   TODO: write func to check this!!
-- type VariantDatabase = Variant Database Bool

-- | A variant HDBC database. Doesn't have fexp.
-- type VariantHDBC = Variant Bool (IConnection conn)
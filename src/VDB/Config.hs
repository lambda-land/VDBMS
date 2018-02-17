module VDB.Config where

import Data.SBV (Boolean(..))

import VDB.Name


-- | A configuration is a function that indicates whether each feature is
--   enabled ('true') or disabled ('false'). The boolean return value is
--   parameterized to admit alternative logics or symbolic values.
type Config b = Feature -> b

-- | A configuration that enables all features.
enableAll :: Boolean b => Config b
enableAll _ = true

-- | A configuration that disables all features.
disableAll :: Boolean b => Config b
disableAll _ = false

-- | Override a configuration to enable an option.
enable :: Boolean b => Feature -> Config b -> Config b
enable this c f
    | f == this = true
    | otherwise = c f

-- | Override a configuration to disable an option.
disable :: Boolean b => Feature -> Config b -> Config b
disable this c f
    | f == this = false
    | otherwise = c f

-- | Override a configuration to enable the indicated features.
enableMany :: Boolean b => [Feature] -> Config b -> Config b
enableMany fs c f
    | elem f fs = true
    | otherwise = c f

-- | Override a configuration to disable all except the indicated features.
disableMany :: Boolean b => [Feature] -> Config b -> Config b
disableMany fs c f
    | elem f fs = false
    | otherwise = c f

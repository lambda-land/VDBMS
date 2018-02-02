module VDB.Config where

import VDB.Feature


-- | A configuration is a function that indicates whether each feature
--   is enabled ('True') or disabled ('False').
type Config = Feature -> Bool

-- | A configuration that enables all features.
enableAll :: Config
enableAll _ = True

-- | A configuration that disables all features.
disableAll :: Config
disableAll _ = False

-- | Override a configuration to enable an option.
enable :: Feature -> Config -> Config
enable this c o
    | o == this = True
    | otherwise = c o

-- | Override a configuration to disable an option.
disable :: Feature -> Config -> Config
disable this c o
    | o == this = False
    | otherwise = c o

-- | Override a configuration to enable the indicated features.
enableMany :: [Feature] -> Config -> Config
enableMany os c o
    | elem o os = True
    | otherwise = c o

-- | Override a configuration to disable all except the indicated features.
disableMany :: [Feature] -> Config -> Config
disableMany os c o
    | elem o os = False
    | otherwise = c o

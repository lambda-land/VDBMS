-- | A generic interface for variational things.
module VDB.Variational where

import Data.Maybe (catMaybes)

import VDB.Config
import VDB.FeatureExpr
import VDB.Name

--
-- * Optional values
--

-- | An optionally included value. Whether it is included is determined by
--   a presence condition.
type Opt a = (FeatureExpr, a)

-- | gets the object of Opt a.
getObj :: Opt a -> a
getObj = snd

-- | gets the fexp assigned to object.
getFexp :: Opt a -> FeatureExpr
getFexp = fst

-- | makes an obj optional.
mkOpt :: FeatureExpr -> a -> Opt a
mkOpt = (,)

-- | updates obj.
updateOptObj :: a -> Opt a -> Opt a 
updateOptObj o (f,_) = mkOpt f o 

-- | updates fexp.
updateFexp :: FeatureExpr -> Opt a -> Opt a 
updateFexp f (_,o) = mkOpt f o

-- | Apply a selection to an optional value.
selectOpt :: Feature -> Bool -> Opt a -> Opt a
selectOpt f b (e,a) = (selectFeatureExpr f b e, a)

-- | Apply a configuration to an optional value.
configureOpt :: Config Bool -> Opt a -> Maybe a
configureOpt c (e,a)
    | evalFeatureExpr c e = Just a
    | otherwise           = Nothing

-- | Configure a list of optional values.
configureOptList :: Config Bool -> [Opt a] -> [a]
configureOptList c os = catMaybes (map (configureOpt c) os)

-- | Apply a configuration to an optional value
--   and return an optional value with fexp being True.
configureOptRetOpt :: Config Bool -> Opt a -> Maybe (Opt a)
configureOptRetOpt c (e,a)
  | evalFeatureExpr c e = Just (Lit True, a)
  | otherwise           = Nothing

-- | Configure a list of optional values and return 
--   a list of optional values with fexp being True.
configureOptListRetOpt :: Config Bool -> [Opt a] -> [Opt a]
configureOptListRetOpt c os = catMaybes (map (configureOptRetOpt c) os)


-- | A type class for variational things.
class Variational a where

  -- | Create a choice.
  choice :: FeatureExpr -> a -> a -> a

  -- | Map a function over all choices.
  choiceMap :: (FeatureExpr -> a -> a -> a) -> a -> a

  -- | Partially configure a variational thing.
  select :: Feature -> Bool -> a -> a
  select f b = choiceMap (selectHelper f b)

  -- | Fully configure a variational thing.
  configure :: Config Bool -> a -> a
  configure c = choiceMap (configureHelper c)


-- | A helper function to implement select for data types with simple choices.
selectHelper :: Variational a => Feature -> Bool -> FeatureExpr -> a -> a -> a
selectHelper f b e l r = case selectFeatureExpr f b e of
    Lit b -> if b then l else r
    e'    -> choice e' l r

-- | original: Lit b -> if b then l else r
-- | A helper function to implement configure for data types with simple choices.
configureHelper :: Config Bool -> FeatureExpr -> a -> a -> a
configureHelper c f l r = if evalFeatureExpr c f then l else r


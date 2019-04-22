-- | A generic interface for variational things.
module VDB.Variational where

import Data.Maybe (catMaybes)

import VDB.Config
import VDB.FeatureExpr
import VDB.Name

import Control.Arrow

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
updateOptObj :: b -> Opt a -> Opt b
updateOptObj o (f,_) = mkOpt f o 

-- | updates fexp.
updateFexp :: FeatureExpr -> Opt a -> Opt a 
updateFexp f (_,o) = mkOpt f o

-- | maps a function to the fexp of an opt a.
mapFst :: (FeatureExpr -> FeatureExpr) 
  -> [Opt a] -> [Opt a]
mapFst f = fmap (first f)

-- | maps a function to the second of an opt a.
mapSnd :: (a -> b) -> [Opt a] -> [Opt b]
mapSnd f = fmap (second f)

-- | maps first and second at the same time.
mapFstSnd :: (FeatureExpr -> FeatureExpr)
  -> (a -> b) -> [Opt a] -> [Opt b]
mapFstSnd f g = fmap (f *** g)
-- mapFst f . mapSnd g

-- | combines two opts together s.t. every two second
--   elements will be combined with g and then their
--   appropriate fexps will be combined with f.
combOpts :: (FeatureExpr -> FeatureExpr -> FeatureExpr)
  -> (a -> b -> b) 
  -> [Opt a] -> [Opt b]
  -> [Opt b]
combOpts f g os1 os2 = 
  [(f f1 f2, g o1 o2) | (f1, o1) <- os1, (f2,o2) <- os2]
  -- (f *** g) <$> os1 <*> os2 -- this aint working!!

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


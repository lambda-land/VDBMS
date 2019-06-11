-- | A generic interface for optional things.
module VDBMS.Variational.Opt (
        
        Opt,
        getObj,
        getFexp,
        mkOpt,
        updateOptObj,
        updateFexp,
        mapFst,
        mapSnd,
        mapFstSnd,
        combOpts,
        selectOpt,
        configureOpt,
        configureOptList,
        configureOptListRetOpt,
        groupOpts,
        validifyOpts

) where

import Data.Maybe (catMaybes)
import Data.List (groupBy)

import VDBMS.Features.Config
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.Features.SAT (equivalent,satisfiable)
import VDBMS.Variational.Variational
-- import VDBMS.Features.FeatureExpr.Types (FeatureExpr(..))
-- import VDBMS.Features.FeatureExpr.Core (evalFeatureExpr)
-- import VDBMS.Features.FeatureExpr.Ops (selectFeatureExpr)
-- import VDBMS.Features.Feature

import Control.Arrow (first, second, (***))


-- | Optional type class. 
-- NOTE: we're not using it for now since we only have
--       opt in one place (attributes of queries).
-- class Variational a => Optional a where
  
--   -- | Create an opt.
--   opt :: a -> a 

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
  -> (a -> b -> c) 
  -> [Opt a] -> [Opt b]
  -> [Opt c]
combOpts f g os1 os2 = 
  [(f f1 f2, g o1 o2) | (f1, o1) <- os1, (f2,o2) <- os2]
  -- (f *** g) <$> os1 <*> os2 -- this aint working!!

-- | helper for groupOpts.
--   pushes down the list and picks the first of head.
pushDown :: [(a,b)] -> (a,[b])
-- pushDown [] = error "got an empty list of opts!!!"
pushDown [(a,b)] = (a,[b])
pushDown ((a,b):l) = (a,b:snd (pushDown l))

-- | groups objects of opt that their fexp are equiv together. 
groupOpts :: [Opt a] -> [Opt [a]]
groupOpts os = fmap pushDown groupOs
  where
    groupOs = groupBy (\x y -> equivalent (fst x) (fst y)) os

-- | checks to see if elements of the list are satisfiable.
--   if so keeps them, if not drops them.
validifyOpts :: [Opt a] -> [Opt a]
validifyOpts os = filter (satisfiable . fst) os

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



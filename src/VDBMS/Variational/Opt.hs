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
        groupOn,
        pushDownFst,
        validifyOpts,
        applyFuncObj,
        applyFuncFexp

) where

import Data.Maybe (catMaybes)
import Data.List (groupBy)

import VDBMS.Features.Config
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.Features.SAT (equivalent,satisfiable)
-- import VDBMS.Variational.Variational
-- import VDBMS.Features.FeatureExpr.Types (FeatureExpr(..))
-- import VDBMS.Features.FeatureExpr.Core (evalFeatureExpr)
-- import VDBMS.Features.FeatureExpr.Ops (selectFeatureExpr)
-- import VDBMS.Features.Feature

import Control.Arrow (first, second, (***))

import qualified Data.Map as M

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

-- | Applies a function to the object of Opt.
applyFuncObj :: (a -> b) -> Opt a -> Opt b
applyFuncObj f (fexp, a) = (fexp , f a)

-- | updates fexp.
updateFexp :: FeatureExpr -> Opt a -> Opt a 
updateFexp f (_,o) = mkOpt f o

-- | Applies a function to the feature expression of opt.
applyFuncFexp :: (FeatureExpr -> FeatureExpr) -> Opt a -> Opt a 
applyFuncFexp f (fexp, a) = (f fexp, a)

-- | maps a function to the fexp of an opt a.
mapFst :: Traversable t => (FeatureExpr -> FeatureExpr) 
  -> t (Opt a) -> t (Opt a)
mapFst = fmap . first 

-- | maps a function to the second of an opt a.
mapSnd :: Traversable t => (a -> b) -> t (Opt a) -> t (Opt b)
mapSnd = fmap . second

-- | maps first and second at the same time.
mapFstSnd :: Traversable t 
  => (FeatureExpr -> FeatureExpr)
  -> (a -> b) -> t (Opt a) -> t (Opt b)
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
pushDown [(a,b)] = (a,[b])
pushDown ((a,b):l) = (a,b:snd (pushDown l))
pushDown [] = error "got an empty list of opts!!!"

-- | push down the list for the first element.
pushDownFst :: [(a,b)] -> ([a],b)
pushDownFst [(a,b)] = ([a],b)
pushDownFst ((a,b):l) = (a:fst (pushDownFst l),b)
pushDownFst [] = error "got an empty list of opts!!!"

-- | groups elements of a list based on a given function.
groupOn :: (Ord b) => (a -> b) -> [a] -> [[a]]
groupOn f =
  let unpack = fmap snd . M.toList
      fld m a = case M.lookup (f a) m of
        Nothing -> M.insert (f a) [a] m
        Just as -> M.insert (f a) (a:as) m
  in unpack . foldl fld M.empty

-- | groups objects of opt that their fexp are equiv together. 
groupOpts :: [Opt a] -> [Opt [a]]
groupOpts os = fmap pushDown $ groupOn fst os
  -- where
  --   -- groupOs = groupBy (\x y -> equivalent (fst x) (fst y)) os
  --   groupOs = 

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



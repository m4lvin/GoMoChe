module Gossip.Internal where

import Data.Maybe
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set

at :: IntMap b -> Int -> b
at m k = fromJust $ IntMap.lookup k m

lfp :: Eq a => (a -> a) -> a -> a
lfp f x | f x == x  = x
        | otherwise = lfp f (f x)

takeFrom :: Int -> [a] -> [a]
takeFrom _ []     = []
takeFrom 0 xs     = xs
takeFrom k (_:xs) = takeFrom (k-1) xs

finiteIterate :: Int -> (a -> a) -> a -> a
finiteIterate 0 _ x = x
finiteIterate k f x = finiteIterate (k-1) f (f x)

splitWhere :: Eq a => a -> [a] -> [[a]]
splitWhere a str = case break (== a) str of
  (xs,[])    -> [xs]
  (xs,[_a])  -> [xs]
  (xs,_a:ys) -> xs : splitWhere a ys

setUnion :: Ord a => Set (Set a) -> Set a
setUnion = Set.unions . Set.toList

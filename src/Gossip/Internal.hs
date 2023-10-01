module Gossip.Internal where

import Data.List (isPrefixOf)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set

at :: IntMap b -> Int -> b
at m k = x where x = case IntMap.lookup k m of
                       Just this -> this
                       Nothing -> error "at failed"

lfp :: Eq a => (a -> a) -> a -> a
lfp f x = if f x == x then x else lfp f (f x)

-- | Transitive Closure
tcl :: Eq a => [a] -> (a -> a -> Bool) -> (a -> a -> Bool)
tcl domain r x y = y `elem` lfp extend [x] where
  extend zs = zs ++ [ newZ | z <- zs, newZ <- domain, r z newZ, newZ `notElem` zs ]

finiteIterate :: Int -> (a -> a) -> a -> a
finiteIterate 0 _ x = x
finiteIterate k f x = finiteIterate (k-1) f (f x)

splitWhere :: Eq a => a -> [a] -> [[a]]
splitWhere a str = case break (== a) str of
  (xs,[])    -> [xs]
  (xs,[_a])  -> [xs]
  (xs,_a:ys) -> xs : splitWhere a ys

splitWhereAny :: Eq a => [a] -> [a] -> [[a]]
splitWhereAny as str = case break (`elem` as) str of
  (xs,[])    -> [xs]
  (xs,[_a])  -> [xs]
  (xs,_a:ys) -> xs : splitWhereAny as ys

addAt :: [a] -> a -> Int -> [a]
addAt xs     y 0 = y : xs
addAt (x:xs) y k = x : addAt xs y (k-1)
addAt []     _ _ = error "cannot add within an empty list!"

setUnion :: Ord a => Set (Set a) -> Set a
setUnion = Set.unions . Set.toList

prefixElem :: Eq a => [a] -> [[a]] -> Bool
prefixElem xs = any (\ys -> xs `isPrefixOf` ys)

-- string replace, see https://stackoverflow.com/a/14908602
rep :: Eq a => [a] -> [a] -> [a] -> [a]
rep _ _ []         = []
rep a b s@(x:xs)
  | a `isPrefixOf` s = b ++ rep a b (drop (length a) s)
  | otherwise        = x  : rep a b xs

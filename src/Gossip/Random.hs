module Gossip.Random where

import Gossip
import Gossip.General
import Test.QuickCheck

import Data.List
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap

newtype ArbitraryInitialGG = ArbIGG Graph

instance Show ArbitraryInitialGG where
  show (ArbIGG g) = "ArbIGG (parseGraph \"" ++ ppGraph g ++ "\")"

instance Arbitrary ArbitraryInitialGG where
  arbitrary = do
    -- n <- choose (3,4::Int)
    n <- choose (3,3::Int)
    let ags = [(0::Int)..(n-1)]
    phonebooks <- mapM (\i -> sublistOf ags >>= \rest -> return $ (sort.nub) (i : rest)) ags
    let nRel = IntMap.fromList [ (k, IntSet.fromList $ phonebooks !! k ) | k <- [0..(n-1)] ]
    let sRel = ident n
    return $ ArbIGG (nRel,sRel)
  -- shrinking by deleting N-edges:
  shrink (ArbIGG (nRel,sRel)) = [ArbIGG (newNrel,sRel) | newNrel <- map convertBack newNs] where
    nList = (map (fmap IntSet.toList) . IntMap.toList) nRel
    newNs = [ update x (delete n ns) nList | (x,ns) <- nList, n <- ns, n /= x ]
    update k newval = map (\(x,oldval) -> if x == k then (x,newval) else (x,oldval))
    convertBack = IntMap.fromList . map (fmap IntSet.fromList)

newtype ArbitraryPointAgent = ArbPA (State, Agent)

instance Show ArbitraryPointAgent where
  show (ArbPA ((mode,g,h),a)) = concat [ "ArbPA ((", show mode, ","
                                       , "parseGraph \"", ppGraph g
                                       , "\", parseSequence \"", ppSequence h
                                       , "\"),", show a, ")" ]

instance Arbitrary ArbitraryPointAgent where
  arbitrary = do
    (ArbIGG g) <- arbitrary
    sequ <- elements (sequences lns (Sync,g,[]))
    time <- choose (0,length sequ)
    let sigma = take time sequ
    let agent = 0
    return $ ArbPA ((Sync, g, sigma), agent)

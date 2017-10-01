
module Gossip.Random where

import Gossip
import Gossip.General
import Test.QuickCheck

import Data.List
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap

newtype ArbitraryInitialState = ArbIS State deriving (Eq,Ord)

instance Show ArbitraryInitialState where
  show (ArbIS s) = ppState s

instance Arbitrary ArbitraryInitialState where
  arbitrary = do
    n <- choose (3,4::Int)
    let ags = [(0::Int)..(n-1)]
    phonebooks <- mapM (\i -> sublistOf ags >>= \rest -> fmap (sort.nub) (return $ i : rest)) ags
    let nRel = IntMap.fromList [ (k, IntSet.fromList $ phonebooks !! k ) | k <- [0..(n-1)] ]
    let sRel = ident n
    return $ ArbIS (nRel,sRel)

newtype ArbitraryPointAgent = ArbPA (Point, Agent) deriving (Eq,Ord)

instance Show ArbitraryPointAgent where
  show (ArbPA ((s,h),a)) = ppState s ++ " " ++ show h ++ " " ++ show a

instance Arbitrary ArbitraryPointAgent where
  arbitrary = do
    (ArbIS state) <- arbitrary
    sequ <- elements (sequences lnsCK (state,[]) lns)
    time <- choose (0,length sequ)
    let history = take time sequ
    let agent = 0
    return $ ArbPA ((state, history), agent)

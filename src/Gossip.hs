{-# LANGUAGE FlexibleInstances #-}

module Gossip where

import Gossip.Internal

import Data.List
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap


-- Agents, Relations, States, Calls, Sequences, Histories --

type Agent = Int

type Relation = IntMap IntSet

type State = (Relation, Relation)

class ProvidesAgentSet a where agentsOf :: a -> [Agent]
instance ProvidesAgentSet Relation where agentsOf r = [0..(length r - 1)]
instance ProvidesAgentSet State where agentsOf = agentsOf . fst

type Call = (Agent,Agent)
type Sequence = [Call]

ppCall :: Call -> String
ppCall (x,y) = show x ++ "→" ++ show y

ppSequence :: Sequence -> String
ppSequence = intercalate ";" . map ppCall

-- | Is this agent involved in this call?
isin :: Agent -> Call -> Bool
isin a (x,y) = a `elem` [x,y]


-- Examples of relations and initial graphs --

ident :: Int -> Relation
ident k = IntMap.fromList [ (i,IntSet.singleton i) | i <- [0..(k-1)] ]

total :: Int -> Relation
total k = IntMap.fromList [ (i, IntSet.fromList [0..(k-1)]) | i <- [0..(k-1)] ]

isTotal :: Relation -> Bool
isTotal r = r == total (IntMap.size r)

isIdent :: Relation -> Bool
isIdent r = r == ident (IntMap.size r)

totalInit :: Int -> State
totalInit k = (total k, ident k)

lineInit :: Int -> State
lineInit k = (IntMap.fromList $ [ (a,IntSet.fromList [a,a+1]) | a <- [0..(k-2)] ] ++ [ (k-1,IntSet.singleton (k-1)) ], ident k)

-- | given a list of phonebooks, generate an initial state
exampleFromList :: [[Agent]] -> State
exampleFromList phonebooks = (nRel, sRel) where
  n = length phonebooks
  nRel = IntMap.fromList [ (k, IntSet.fromList $ phonebooks !! k ) | k <- [0..(n-1)] ]
  sRel = ident n

relFromList :: [[Agent]] -> Relation
relFromList phonebooks =
  IntMap.fromList [ (k, IntSet.fromList $ phonebooks !! k ) | k <- [0..(length phonebooks-1)] ]

-- | All initial graphs for k agents
allInits :: Int -> [State]
allInits k = [ (fromListEnum $ map IntSet.fromList n, ident k) | n <- allNs ] where
  allNs = choices $ map (\a -> map (sort.(a:)) (subsfor a)) [0..(k-1)]
  subsfor a = subsequences (delete a [0..(k-1)])
  fromListEnum :: [a] -> IntMap a
  fromListEnum xs = IntMap.fromList [ (i,xs !! i) | i <- [0..(length xs -1)] ]
  choices :: [[a]] -> [[a]]
  choices []        = [ [] ]
  choices (xs:rest) = [ x:rc | x <- xs, rc <- choices rest ]

isSolved :: State -> Bool
isSolved state = all (== IntSet.fromList (agentsOf state)) (snd state)

-- | make a call
call :: State -> Call -> State
call (n, s) (a,b)
  | b `IntSet.notMember` (n `at` a) = error $ "impossible call: " ++ ppCall (a,b)
  | otherwise = (newN, newS) where
      newN = IntMap.adjust (IntSet.union (n `at` b)) a $ IntMap.adjust (IntSet.union (n `at` a)) b n
      newS = IntMap.adjust (IntSet.union (s `at` b)) a $ IntMap.adjust (IntSet.union (s `at` a)) b s

-- \ make a sequence of calls
calls :: State -> Sequence -> State
calls = foldl' call


-- pretty printing and parsing of relations and states for up to 10 agents

ppRel :: Relation -> String
ppRel r
  | isTotal r = "T" ++ show (length r)
  | isIdent r = "I" ++ show (length r)
  | otherwise = intercalate "-" . map (concatMap show . IntSet.toList) . IntMap.elems $ r

parseRel :: String -> Relation
parseRel ('T':nStr) = total (read nStr)
parseRel ('I':nStr) = ident (read nStr)
parseRel relStr1 = relFromList $ resultRel relStr1 where
  resultRel = map (map (read.return)) . splitWhere '-'

ppState :: State -> String
ppState (n,s)
  | isTotal s = "★" ++ show (length s)
  | otherwise = concat [ ppRel n, " ", ppRel s ]

ppStateShort :: State -> String
ppStateShort (n,s)
  | isTotal s = "★" ++ show (length s)
  | otherwise = intercalate "." $ map stringFor is where
      is = agentsOf (n,s)
      stringFor i = concatMap (stringForFor i) (agentsOf (n,s))
      stringForFor i j | j `IntSet.member` (s `at` i) = [['A'..] !! j]
                       | j `IntSet.member` (n `at` i) = [['a'..] !! j]
                       | otherwise                    = []

parseState :: String -> State
parseState ('★':kchar) = totalInit (read kchar)
parseState stateStr =  (parseRel nStr, parseRel sStr) where
  [nStr, sStr] = splitWhere ' ' stateStr

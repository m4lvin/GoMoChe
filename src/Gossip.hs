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

type Graph = (Relation, Relation)

class ProvidesAgentSet a where agentsOf :: a -> [Agent]
instance ProvidesAgentSet Relation where agentsOf r = [0..(length r - 1)]
instance ProvidesAgentSet Graph where agentsOf = agentsOf . fst

type Call = (Agent,Agent)
type Sequence = [Call]

ppCall :: Call -> String
ppCall (x,y) = show x ++ show y

parseCall :: String -> Call
parseCall [x,y] = (read [x], read [y])
parseCall foo   = error $ "This is not a call: " ++ show foo

ppSequence :: Sequence -> String
ppSequence = intercalate ";" . map ppCall

charAgent :: Int -> Char
charAgent = (!!) ['a'..]

charCall :: Call -> String
charCall = (\(x,y) -> charAgent x : charAgent y : [])

charSequence :: [(Int, Int)] -> [Char]
charSequence = intercalate ";" . map charCall where

parseSequence :: String -> Sequence
parseSequence = map parseCall . splitWhere ';'

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

isInitial :: Graph -> Bool
isInitial = isIdent . snd

totalInit :: Int -> Graph
totalInit k = (total k, ident k)

lineInit :: Int -> Graph
lineInit k = (IntMap.fromList $ [ (a,IntSet.fromList [a,a+1]) | a <- [0..(k-2)] ] ++ [ (k-1,IntSet.singleton (k-1)) ], ident k)

-- | given a list of phonebooks, generate an initial state
exampleFromList :: [[Agent]] -> Graph
exampleFromList phonebooks = (nRel, sRel) where
  n = length phonebooks
  nRel = relFromList phonebooks
  sRel = ident n

relFromList :: [[Agent]] -> Relation
relFromList phonebooks =
  IntMap.fromList [ (k, IntSet.fromList $ phonebooks !! k ) | k <- [0..(length phonebooks-1)] ]

relToPairs :: Relation -> [(Agent,Agent)]
relToPairs rel = [ (x,y) | x <- IntMap.keys rel, y <- IntSet.elems (rel IntMap.! x) ]

sizeOfGraph :: Graph -> Int
sizeOfGraph (nRel,_) = numAg + numN  where
  numAg = length nRel
  numN = IntMap.foldrWithKey (\x ys -> (+) $ IntSet.size (IntSet.delete x ys)) 0 nRel

-- | All initial graphs for k agents
allInits :: Int -> [Graph]
allInits k = [ (fromListEnum $ map IntSet.fromList n, ident k) | n <- allNs ] where
  allNs = choices $ map (\a -> map (sort.(a:)) (subsfor a)) [0..(k-1)]
  subsfor a = subsequences (delete a [0..(k-1)])
  fromListEnum :: [a] -> IntMap a
  fromListEnum xs = IntMap.fromList [ (i,xs !! i) | i <- [0..(length xs -1)] ]
  choices :: [[a]] -> [[a]]
  choices []        = [ [] ]
  choices (xs:rest) = [ x:rc | x <- xs, rc <- choices rest ]

isSolved :: Graph -> Bool
isSolved g = all (== IntSet.fromList (agentsOf g)) (snd g)

-- | make a call
call :: Graph -> Call -> Graph
call (n, s) (a,b)
  | b `IntSet.notMember` (n `at` a) = error $ "impossible call: " ++ ppCall (a,b)
  | otherwise = (newN, newS) where
      newN = IntMap.adjust (IntSet.union (n `at` b)) a $ IntMap.adjust (IntSet.union (n `at` a)) b n
      newS = IntMap.adjust (IntSet.union (s `at` b)) a $ IntMap.adjust (IntSet.union (s `at` a)) b s

-- \ make a sequence of calls
calls :: Graph -> Sequence -> Graph
calls = foldl' call


-- pretty printing and parsing of relations and graphs for up to 10 agents

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

ppGraph :: Graph -> String
ppGraph (n,s)
  | isTotal s = "★" ++ show (length s)
  | otherwise = concat [ ppRel n, " ", ppRel s ]

ppGraphShort :: Graph -> String
ppGraphShort (n,s)
  | isTotal s = "★" ++ show (length s)
  | otherwise = intercalate "." $ map stringFor is where
      is = agentsOf (n,s)
      stringFor i = concatMap (stringForFor i) (agentsOf (n,s))
      stringForFor i j | j `IntSet.member` (s `at` i) = [['A'..] !! j]
                       | j `IntSet.member` (n `at` i) = [['a'..] !! j]
                       | otherwise                    = []

parseGraph :: String -> Graph
parseGraph ('★':kchar) = totalInit (read kchar)
parseGraph graphStr = (parseRel nStr, parseRel sStr) where
  [nStr, sStr] = splitWhere ' ' graphStr

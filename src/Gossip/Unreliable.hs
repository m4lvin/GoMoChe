{-# LANGUAGE FlexibleInstances #-}

module Gossip.Unreliable where

import Data.Bifunctor (bimap)
import Data.Char (toUpper)
import Data.List (intercalate,(\\),foldl')
import Data.Set (Set,isSubsetOf,singleton)
import qualified Data.Set as Set
--import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Data.Either (isRight)


import Gossip (Agent,Relation,ProvidesAgentSet,agentsOf,charAgent,total,relFromList,ppRel)
import Gossip.Internal (at)

-- * Unreliable Gossip Graphs

type Secret = (Agent,Bool)

type URelation = IntMap (Set Secret)

-- | An unreliable gossip graph: N relation, S relation, reliable set
newtype UGraph = UG (Relation, URelation, [Agent])
  deriving (Eq,Ord,Show)

instance ProvidesAgentSet UGraph where agentsOf (UG ug) = agentsOf . (\(r,_,_) -> r) $ ug

-- * Making Graphs

identU :: Int -> URelation
identU k = IntMap.fromList [ (i,singleton (i,True)) | i <- [0..(k-1)] ]

totalInit :: Int -> [Agent] -> UGraph
totalInit k unrels = UG (total k, identU k, unrels)

-- | Given a list of phonebooks and unreliables, generate an initial state.
exampleFromList :: [[Agent]] -> [Agent] -> UGraph
exampleFromList phonebooks rels = UG (nRel, sRel, rels) where
  n = length phonebooks
  nRel = relFromList phonebooks
  sRel = identU n


-- | PrettyPrinting UGRaphs
ppGraph :: UGraph -> String
ppGraph (UG (n,s,rels)) = concat [ ppRel n, " ", ppSets s ] ++ " R=" ++ show rels

ppSets :: IntMap (Set Secret) -> String
ppSets s = concatMap (\(a,set) -> show a ++ ":[" ++ showSet set ++ "] ") $ IntMap.toAscList s where
  showSet set = intercalate "," (ppSec (IntMap.keys s :: [Agent]) (Set.toAscList set))

ppSec :: [Agent] -> [Secret] -> [String]
ppSec agents set = [ c | a <- agents, let c = charFor $ Prelude.map snd $ Prelude.filter ((== a). fst) set ] where
  charFor [True]  = "1"
  charFor [False] = "0"
  charFor []      = "∅"
  charFor _       = "⊥"

-- * Calls

-- | Calls in which the agents may lie.
-- `Left` means truthful, `Right` means lying.
type Call = (Either Agent Agent, Either Agent Agent)

agOf :: Either Agent Agent -> Agent
agOf (Left  a) = a
agOf (Right a) = a

-- FIXME: agents should be characters to make this easier?
ppCall :: Call -> String
ppCall (x,y) = showAg x ++ showAg y where
  showAg (Left a) = show a
  showAg (Right a) = show a ++ "*"

charCall :: Call -> String
charCall (x,y) = [charAgentU x, charAgentU y] where
  charAgentU (Left z) = charAgent z
  charAgentU (Right z) = toUpper $ charAgent z

tweakedBy :: Agent -> Set Secret -> Set Secret
tweakedBy i set | (i,True ) `elem` set = Set.insert (i,False) $ Set.delete (i,True ) set
                | (i,False) `elem` set = Set.insert (i,True ) $ Set.delete (i,False) set
                | otherwise = error "This is weird."

-- | Execute a given call.
call :: UGraph -> Call -> UGraph
call (UG (n, s, rels)) c@(aU, bU)
  | agOf bU `IntSet.notMember` (n `at` agOf aU) = error $ "impossible call: " ++ ppCall c ++ " is not in N."
  | isRight bU && agOf bU `elem` rels = error $ "impossible call: " ++ ppCall c ++ " but agent " ++ show b ++ " is reliable."
  | isRight aU && agOf aU `elem` rels = error $ "impossible call: " ++ ppCall c ++ " but agent " ++ show b ++ " is reliable."
  | otherwise = UG (newN, newS, rels) where
      a = agOf aU
      b = agOf bU
      aTweak = if isRight aU then tweakedBy a else id
      bTweak = if isRight bU then tweakedBy b else id
      newN = IntMap.adjust (IntSet.union (n `at` b)) a
           $ IntMap.adjust (IntSet.union (n `at` a)) b n
      newS :: URelation
      newS = IntMap.adjust (Set.union (bTweak $ s `at` b)) a
           $ IntMap.adjust (Set.union (aTweak $ s `at` a)) b s

-- | Execute a sequence of calls.
calls :: UGraph -> Sequence -> UGraph
calls = foldl' call

-- | A total UGraph with two agents 0 and 1 where 1 is reliable.
smallExample :: UGraph
smallExample = totalInit 2 [1]

-- | A total UGraph with four agents where 2 and 3 are reliable.
paperExample :: UGraph
paperExample = totalInit 4 [2,3]

-- | The call sequence AB; ac; Ad; cd; bc.
-- Note that this is an LNS sequence. It is successful but not reliably successful.
paperSequence :: [Call]
paperSequence =
  [ (Right 0, Right 1)
  , (Left  0, Left  2)
  , (Right 0, Left  3)
  , (Left  2, Left  3)
  , (Left  1, Left  2) ]


-- | Properties of UGraphs

isComplete :: UGraph -> Bool
isComplete ug@(UG (_,s,_)) = all (\set -> all (`elem` Set.map fst set) (agentsOf ug)) s

isRelComplete :: UGraph -> Bool
isRelComplete ug@(UG (_,s,rels)) = isComplete ug -- TODO!!!
  && all (\a -> all (\x -> Set.fromList [(x,True),(x,False)] `isSubsetOf` (s `at` a)) (agentsOf ug \\ rels)) rels

-- | All possible calls.
possibleCalls :: UGraph -> [Call]
possibleCalls ug@(UG (_,_,rels)) = [ (iU i, jU j) | i <- agentsOf ug
                                                  , j <- agentsOf ug
                                                  , i /= j
                                                  , iU <- Left : [ Right | i `notElem` rels ]
                                                  , jU <- Left : [ Right | j `notElem` rels ]
                                                  ]

-- | Sequences and States.
type Sequence = [Call]
type State = (UGraph,Sequence)

-- * Protocols

type Protocol = State -> Call -> Bool

-- | Learn New Secrets.
lns :: Protocol
lns (ug, sigma) (iU, jU) =  agOf jU `notElem` Set.map fst (s `at` agOf iU) where
  UG (_,s,_) = calls ug sigma

-- | Call Me Once.
cmo :: Protocol
cmo (_,history) (iU, jU) =
  (agOf jU, agOf iU) `notElem` map (bimap agOf agOf) history

-- | Any Call. NOTE: Will generate infinite sequences!
any :: Protocol
any = const . const $ True


-- | All sequences for a given graph and protocol.

sequences :: Protocol -> State -> [Sequence]
sequences proto s@(ug,sigma) = case filter (proto s) (possibleCalls ug) of
  [] -> [ [] ]
  cs -> [ c : rest | c <- cs
                   , rest <- sequences proto (ug,sigma++[c]) ]

-- | Weak and strong Success.

isWeaklySuccessfulOn :: Protocol -> State -> Bool
isWeaklySuccessfulOn proto s@(ug,sigma) =
  Prelude.any (isComplete . (\tau -> calls ug (sigma++tau))) (sequences proto s)

isStronglySuccessfulOn :: Protocol -> State -> Bool
isStronglySuccessfulOn proto s@(ug,sigma) =
  all (isComplete . (\tau -> calls ug (sigma++tau))) (sequences proto s)

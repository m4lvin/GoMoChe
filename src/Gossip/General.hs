{-# LANGUAGE FlexibleInstances #-}

module Gossip.General where

import Gossip
import Gossip.Internal

import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap

-- This is the full language, protocols should only use a subset.

-- NOTE this will eq/show/compare formulas with variables in a misleading way!

type FormWithAgentVar = Agent -> Form
instance Eq FormWithAgentVar where
  (==) f g = f 0 == g 0
instance Show FormWithAgentVar where
  show f = show (f (-1))
instance Ord FormWithAgentVar where
  compare f g = compare (f 0) (g 0)

type ProgWithAgentVar = Agent -> Prog
instance Eq ProgWithAgentVar where
  (==) p q = p 0 == q 0
instance Show ProgWithAgentVar where
  show p = show (p (-1))
instance Ord ProgWithAgentVar where
  compare p q = compare (p 0) (q 0)

-- | Formulas
data Form = N Agent Agent
          | S Agent Agent
          | C Agent Agent
          | Top
          | Bot
          | Neg Form
          | Conj [Form]
          | Disj [Form]
          | Impl Form Form
          | K Agent Protocol Form
          | HatK Agent Protocol Form
          | Box Prog Form
          | Dia Prog Form
          | ExistsAg FormWithAgentVar
          | ForallAg FormWithAgentVar
          deriving (Eq,Ord,Show)

-- | Programs
data Prog = Test Form
          | Call Agent Agent
          | Seq [Prog]
          | Cup [Prog]
          | CupAg ProgWithAgentVar
          | Star Prog
          deriving (Eq,Ord,Show)


-- useful abbreviations --

-- biimplication
equi :: Form -> Form -> Form
equi f g = Conj [f `Impl` g, g `Impl` f]

-- agent a is an expert
expert :: Agent -> Form
expert a = ForallAg (S a)

-- all agents are experts
allExperts :: Form
allExperts = ForallAg expert

superExpert :: Agent -> Protocol -> Form
superExpert a proto = K a proto allExperts

allSuperExperts :: Protocol -> Form
allSuperExperts proto = ForallAg (flip superExpert proto)

-- agent knows no other secrets than their own
knowsOnlyOwn :: Agent -> Form
knowsOnlyOwn x = ForallAg (\y -> if x == y then Top else Neg $ S x y)

type Info = ([Agent],[Agent])

allInfos :: [Agent] -> [Info]
allInfos [] = [([],[])]
allInfos (x:xs) = concat [ [(x:ns,x:ss), (x:ns,ss), (ns,ss) ]
                         | (ns,ss) <- allInfos xs ]

knowsExactly :: Agent -> Info -> Form
knowsExactly a (nums,secs) =
  ForallAg (\y -> Conj [ if y `elem` nums then N a y else Neg $ N a y
                       , if y `elem` secs then S a y else Neg $ S a y
                       ] )

-- retricted quantifiers
forallAgWith :: (Agent -> Bool) -> (Agent -> Form) -> Form
forallAgWith cond form = ForallAg (\x -> if cond x then form x else Top)

existsAgWith :: (Agent -> Bool) -> (Agent -> Form) -> Form
existsAgWith cond form = ExistsAg (\x -> if cond x then form x else Bot)

-- General Protocols --
type Protocol = (Agent,Agent) -> Form

instance Eq Protocol where
  p1 == p2 = p1 (0,1) == p2 (0,1)

instance Ord Protocol where
  compare p1 p2 = compare (p1 (0,1)) (p2 (0,1))

instance Show Protocol where
  show p = show $ p (0,1)

lns :: Protocol
lns (x, y) = Neg $ S x y

cmo :: Protocol
cmo (x, y) = Conj [ Neg (C x y), Neg (C y x) ]

anyCall,noCall :: Protocol
anyCall = const Top
noCall = const Bot

type State = (Graph,Sequence)

currentGraph :: State -> Graph
currentGraph = uncurry calls

pointCall :: State -> Call -> State
pointCall (beginState,hist) c = (beginState, hist ++ [c])

-- | pretty print a state: initial graph, history, resulting state
ppState :: State -> String
ppState (g,h) = ppRel (fst g)
  ++ if null h then [] else " " ++ ppSequence h ++ "  " ++ ppGraph (calls g h)

possibleCalls :: State -> [Call]
possibleCalls state =
  [ (x,y) | (x,setYs) <- IntMap.toList (fst $ currentGraph state)
          , y <- IntSet.toList setYs
          , x /= y ]

allowedCalls :: Protocol -> State -> [Call]
allowedCalls proto state = filter (eval state . proto) (possibleCalls state)

localSameFor :: Agent -> Graph -> Graph -> Bool
localSameFor a s s' = (fst s `at` a) == (fst s' `at` a) && (snd s `at` a) == (snd s' `at` a)

-- Epistemic Alternatives: Points that an agent confuses with the given one.
-- Depends on the protocol. Note: synchronous, with initCK
-- TODO use Set Point instead?
epistAlt :: Agent -> Protocol -> State -> [State]
epistAlt _ _     (g, []     ) = [ (g, []) ] -- initial graph is common knowledge!
epistAlt a proto (g, history) =
  let
    (prev, lastevent) = (init history, last history)
    lastcall@(x,y)    = lastevent -- this pattern match might fail, but laziness saves us
  in sort $
    if a `isin` lastevent
       -- if a was in the last call, consider all allowed histories
       -- before, then restrict to localSameFor x and y, because a is
       -- one of them and observes both their local states.
       -- (This means we do inspect-then-merge!)
       then [ (g',althist ++ [lastcall])
              | (g',althist) <- epistAlt a proto (g,prev)
              , eval (g',prev) (proto lastcall)
              , eval (g',althist) (proto lastcall)
              , localSameFor x (calls g' althist) (calls g prev)
              , localSameFor y (calls g' althist) (calls g prev) ]
       -- if a was NOT in the last event, consider all non-a events possible
       -- which are allowed according to the protocol that is CK
       else [ (g',cs'++[altevent])
              | (g',cs') <- epistAlt a proto (g,prev)
              , altevent <- allowedCalls proto (g',cs')
              , not $ a `isin` altevent ]

-- Semantics --

-- evaluate formulas
eval :: State -> Form -> Bool
eval state (N a b  )    = b `IntSet.member` (fst (uncurry calls state) `at` a)
eval state (S a b  )    = b `IntSet.member` (snd (uncurry calls state) `at` a)
eval state (C a b  )    = (a,b) `elem` (snd state)
eval _     Top          = True
eval _     Bot          = False
eval state (Neg f  )    = not $ eval state f
eval state (Conj fs)    = all (eval state) fs
eval state (Disj fs)    = any (eval state) fs
eval state (Impl f1 f2) = not (eval state f1) || eval state f2
eval state (K    a p f) = all (`eval` f) (epistAlt a p state)
eval state (HatK a p f) = any (`eval` f) (epistAlt a p state)
eval state (Box p f)    = all (`eval` f) (Set.toList $ runs state p)
eval state (Dia p f)    = any (`eval` f) (Set.toList $ runs state p)
eval state (ExistsAg f) = any (eval state . f) (agentsOf $ fst state)
eval state (ForallAg f) = all (eval state . f) (agentsOf $ fst state)

(|=) :: State -> Form -> Bool
(|=) = eval

-- evaluate programs
runs :: State -> Prog -> Set State
runs state     (Test f)     | eval state f = Set.singleton state
                            | otherwise    = Set.empty
-- we always evaluate calls, ignoring protocol and whether it is ck:
runs (g,sigma) (Call a b)   | eval (g,sigma) (N a b) = Set.singleton (g,sigma++[(a,b)])
                            | otherwise              = Set.empty
runs state     (Seq []    ) = Set.singleton state
runs state     (Seq (p:ps)) = setUnion $ Set.map (\state' -> runs state' (Seq ps)) (runs state p)
runs state     (Cup ps)     = setUnion $ Set.map (runs state) (Set.fromList ps)
runs state     (CupAg p)    = Set.unions $ map (runs state . p) (agentsOf $ fst state)
runs state     (Star p)     = lfp loop $ Set.singleton state where
  loop states = Set.union states (setUnion $ Set.map (`runs` p) states)


-- Abbreviations to run protocols and describe success in formulas --

protoCanGoOn, protoFinished :: Protocol -> Form
protoCanGoOn  proto = ExistsAg (\x -> ExistsAg (\y -> if x /= y then Conj [       N x y,       proto (x,y) ] else Bot))
protoFinished proto = ForallAg (\x -> ForallAg (\y -> if x /= y then Disj [ Neg $ N x y, Neg $ proto (x,y) ] else Top))

protoTerm :: Protocol -> Prog
protoTerm proto = Seq [Star (protoStep proto), Test (protoFinished proto)]

protoStep :: Protocol -> Prog
protoStep proto =
  CupAg (\x -> CupAg (\y ->
    if x /= y
      then Seq [ Test (Conj [N x y, proto (x,y)]), Call x y ]
      else Test Bot
  ))

isWeaklySuccForm :: Protocol -> Form
isWeaklySuccForm proto = Dia (protoTerm proto) allExperts

isStronglySuccForm :: Protocol -> Form
isStronglySuccForm proto = Box (protoTerm proto) allExperts

isStronglyUnsuccForm :: Protocol -> Form
isStronglyUnsuccForm proto = Box (protoTerm proto) (Neg allExperts)

sequences :: Protocol -> State -> [Sequence]
sequences proto (g,sigma)
  | null (allowedCalls proto (g,sigma)) = [ [] ]
  | otherwise = [ c : rest | c <- allowedCalls proto (g,sigma)
                           , rest <- sequences proto (g,sigma++[c]) ]

isSuccSequence :: State -> Sequence -> Bool
isSuccSequence (g,sigma) cs =  isSolved (calls g (sigma ++ cs))

isSuperSuccSequence :: Protocol -> State -> Sequence -> Bool
isSuperSuccSequence proto (g,sigma) cs = (g, (sigma ++ cs)) |= ForallAg (\a -> superExpert a proto)

compareSequences :: State -> [Protocol] -> [(Sequence,[Bool])]
compareSequences s protos =
  [ (sequ, [ sequ `elem` sequences p s | p <- protos ]) | sequ <- allsequs ] where
    allsequs = sort $ nub $ concat [sequences p s | p <- protos]

isSequenceOf :: Protocol -> State -> Sequence -> Bool
isSequenceOf _     _       []       = True
isSequenceOf proto current (c:rest) = eval current (proto c) && isSequenceOf proto (pointCall current c) rest

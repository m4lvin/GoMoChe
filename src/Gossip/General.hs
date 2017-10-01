{-# LANGUAGE FlexibleInstances #-}

module Gossip.General where

import Gossip
import Gossip.Internal
import Data.Function
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap

-- This is the full language, protocols should only use a subset.

-- | Formulas
data Form = N Agent Agent
          | S Agent Agent
          | Top
          | Bot
          | Neg Form
          | Conj [Form]
          | Disj [Form]
          | Impl Form Form
          | K Agent Form
          | HatK Agent Form
          | Kp Protocol Agent Form
          | HatKp Protocol Agent Form
          | Box Prog Form
          | Dia Prog Form
          deriving (Eq,Ord,Show)

-- | Programs
data Prog = Test Form
          | Call Agent Agent
          | Seq [Prog]
          | Cup [Prog]
          | Star Prog
          deriving (Eq,Ord,Show)


-- useful abbreviations --

-- knowing whether
kw :: Agent -> Form -> Form
kw a f = Conj [f `Impl` K a f, Neg f `Impl` K a (Neg f)]

-- agent a is an expert among k agents
expert :: Int -> Agent -> Form
expert k a = Conj [ S a b | b <- [0..(k-1)] ]

-- all k agents are experts-- Syntax of formulas and programs --
allExperts :: Int -> Form
allExperts k = Conj [ expert k a | a <- [0..(k-1)] ]

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

anyCall,noCall :: Protocol
anyCall = const Top
noCall = const Bot

-- | Gossip models with a protocol that is common knowledge
data GossipModel = GoMo {
  name    :: String,      -- unique identifier
  protoCK :: Protocol     -- Which protocol is CK?
  -- -- the following parameters are fixed to keep it simple
  -- dynamic :: Bool      -- Exchange phone numers?   (Currently: True)
  -- initCK :: Bool,      -- Is the initial graph CK? (Currently: True)
  -- ckNumAgents :: Bool, -- Is |A| CK?               (Currently: True)
  -- obs :: Observability -- What do agents observe?  (Currently: Sync)
  --                      -- needs Observability = Async | Sync | TotalObs
  }

instance Eq GossipModel where (==) = (==) `on` name
instance Ord GossipModel where compare = compare `on` name
instance Show GossipModel where show = name

lnsCK :: GossipModel
lnsCK = GoMo { name="lnsCK", protoCK = lns }

anyCK :: GossipModel
anyCK = GoMo { name="anyCK", protoCK = anyCall }

type Point = (State,Sequence)

currentGraph :: Point -> State
currentGraph = uncurry calls

pointCall :: Point -> Call -> Point
pointCall (beginState,hist) c = (beginState, hist ++ [c])

-- | pretty print a point: initial graph, history, resulting state
ppPoint :: Point -> String
ppPoint (g,h) = ppRel (fst g)
  ++ if null h then [] else " " ++ ppSequence h ++ "  " ++ ppState (calls g h)

allCalls :: Point -> [Call]
allCalls point = [ (x,y) | x <- agentsOf (fst point), y <- agentsOf (fst point), x /= y ]

possibleCalls :: Point -> [Call]
possibleCalls (g,sigma) =
  [ (x,y) | (x,setYs) <- IntMap.toList (fst $ calls g sigma)
          , y <- IntSet.toList setYs
          , x /= y ]

consideredCalls :: GossipModel -> Point -> [Call]
consideredCalls gomo point@(_,_) = concatMap
  (\(x,y) -> [ (x,y) | eval gomo point (protoCK gomo (x,y)) ]) (possibleCalls point)

allowedCalls :: Protocol -> GossipModel -> Point -> [Call]
allowedCalls proto gomo point = concatMap
  (\(x,y) -> [ (x,y) | eval gomo point (proto (x,y)) ]) (possibleCalls point)

localSameFor :: Agent -> State -> State -> Bool
localSameFor a s s' = (fst s `at` a) == (fst s' `at` a) && (snd s `at` a) == (snd s' `at` a)

-- Epistemic Alternatives: Points that an agent confuses with the given one.
-- This uses the gomo parameters. Note: we do SYNCHRONOUS and initCK=True only.
-- TODO use Set Point instead?
epistAlt :: Agent -> GossipModel -> Point -> [Point]
epistAlt _ _    (g, []) = [ (g, []) ] -- initial graph is common knowledge!
epistAlt a gomo (g, history) =
  let
    (prev, lastevent) = (init history, last history)
    (lastcall@(x,y)) = lastevent -- this pattern match might fail, but laziness saves us
  in sort $
    if a `isin` lastevent
       -- if a was in the last call, consider all allowed histories
       -- before, then restrict to localSameFor x and y, because a is
       -- one of them and observes their local states.
       -- (This means we do merge-then-inspect.)
       then [ (g',althist ++ [lastcall])
              | (g',althist) <- epistAlt a gomo (g,prev)
              , eval gomo (g',althist) (protoCK gomo lastcall)
              , localSameFor x (calls g' althist) (calls g prev)
              , localSameFor y (calls g' althist) (calls g prev) ]
       -- if a was NOT in the last event, consider all non-a events possible
       -- which are allowed according to the protocol that is CK
       else [ (g',cs'++[altevent])
              | (g',cs') <- epistAlt a gomo (g,prev)
              , altevent <- consideredCalls gomo (g',cs')
              , not $ a `isin` altevent ]

-- Semantics --

-- evaluate formulas
eval :: GossipModel -> Point -> Form -> Bool
eval _    point (N a b  )      = b `IntSet.member` (fst (uncurry calls point) `at` a)
eval _    point (S a b  )      = b `IntSet.member` (snd (uncurry calls point) `at` a)
eval _    _     Top            = True
eval _    _     Bot            = False
eval gomo point (Neg f  )      = not $ eval gomo point f
eval gomo point (Conj fs)      = all (eval gomo point) fs
eval gomo point (Disj fs)      = any (eval gomo point) fs
eval gomo point (Impl f1 f2)   = not (eval gomo point f1) || eval gomo point f2
eval gomo point (K    a f)     = all (\p -> eval gomo p f) (epistAlt a gomo point)
eval gomo point (HatK a f)     = any (\q -> eval gomo q f) (epistAlt a gomo point)
eval gomo point (Kp    pr a f) = all (\p -> eval gomo p f) (epistAlt a gomo {protoCK = pr} point)
eval gomo point (HatKp pr a f) = any (\p -> eval gomo p f) (epistAlt a gomo {protoCK = pr} point)
eval gomo point (Box p f)      = all (\q -> eval gomo q f) (Set.toList $ runs gomo point p)
eval gomo point (Dia p f)      = any (\q -> eval gomo q f) (Set.toList $ runs gomo point p)

-- evaluate programs
runs :: GossipModel -> Point -> Prog -> Set Point
runs gomo point     (Test   f) | eval gomo point f = Set.singleton point
                               | otherwise         = Set.empty
-- we always evaluate calls, ignoring protocol and whether it is ck:
runs gomo (g,sigma) (Call a b) | eval gomo (g,sigma) (N a b) = Set.singleton (g,sigma++[(a,b)])
                               | otherwise                   = Set.empty
runs _    point     (Seq []  ) = Set.singleton point
runs gomo point     (Seq (p:ps)) = setUnion $ Set.map (\point' -> runs gomo point' (Seq ps)) (runs gomo point p) -- TODO meh
runs gomo point     (Cup ps  ) = setUnion $ Set.map (runs gomo point) (Set.fromList ps)
runs gomo point     (Star p  ) = lfp loop $ Set.singleton point where
  loop states = Set.union states (setUnion $ Set.map (\point' -> runs gomo point' p) states)



-- Abbreviations to run protocols and describe success in formulas --

protoCanGoOn, protoFinished :: Int -> Protocol -> Form
protoCanGoOn  k proto = Disj [ Conj [      N x y,       proto (x,y) ] | x <- allAgents, y <- allAgents, x/=y ] where allAgents = [0..(k-1)]
protoFinished k proto = Conj [ Disj [Neg $ N x y, Neg $ proto (x,y) ] | x <- allAgents, y <- allAgents, x/=y ] where allAgents = [0..(k-1)]

protoTerm :: Int -> Protocol -> Prog
protoTerm k proto = Seq [Star (protoStep k proto), Test (protoFinished k proto)]

protoStep :: Int -> Protocol -> Prog
protoStep k proto = Cup [Seq [ Test (Conj [N x y, proto (x,y)]), Call x y ]
                      | x <- allAgents, y <- allAgents, x/=y ] where allAgents = [0..(k-1)]

isStronglySuccForm :: Protocol -> Int -> Form
isStronglySuccForm proto k = Box (protoTerm k proto) (allExperts k)

isStronglyUnsucFor :: Protocol -> Int -> Form
isStronglyUnsucFor proto k = Box (protoTerm k proto) (Neg $ allExperts k)


sequences :: GossipModel -> Point -> Protocol -> [Sequence]
sequences gomo (g,sigma) proto
  | null (allowedCalls proto gomo (g,sigma)) = [ [] ]
  | otherwise = [ c : rest | c <- allowedCalls proto gomo (g,sigma)
                           , rest <- sequences gomo (g,sigma++[c]) proto ]

isSuccSequence :: Point -> Sequence -> Bool
isSuccSequence (g,sigma) cs =  isSolved (calls g (sigma ++ cs))

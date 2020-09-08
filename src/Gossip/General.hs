{-# LANGUAGE FlexibleInstances #-}

module Gossip.General where

import Data.Char (toUpper)
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap

import Gossip
import Gossip.Internal

-- This is the full language, protocols should only use a subset.

-- | Formulas
data Form = N Agent Agent
          | S Agent Agent
          | C Agent Agent
          | Same Agent Agent
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

-- NOTE Showing and comparing nested formulas with "\x ->" agent variables is tricky.
-- Our solution for now is to string-replace agents by variables, depending on nesting level.

variables :: String
variables = "zyxwvutsZYXWVUTS"

type FormWithAgentVar = Agent -> Form
instance Eq FormWithAgentVar where
  (==) f g = f 0 == g 0 && f 1 == g 1 && f 999 == g 999
instance Show FormWithAgentVar where
  show f = ("(\\" ++ [c] ++ " -> " ++ rep (show n) [c] (show (f n))) ++ ")" where
    c = variables !! n
    n = varLevel (f 1)
instance Ord FormWithAgentVar where
  compare f g = compare (f 0) (g 0)

type ProgWithAgentVar = Agent -> Prog
instance Eq ProgWithAgentVar where
  (==) p q = p 0 == q 0
instance Show ProgWithAgentVar where
  show p = ("(\\" ++ [c] ++ " -> " ++ rep (show n) [c] (show (p n))) ++ ")" where
    c = variables !! n
    n = varLevelP (p 1)
instance Ord ProgWithAgentVar where
  compare p q = compare (p 0) (q 0)

varLevel :: Form -> Int
varLevel Top          = 0
varLevel Bot          = 0
varLevel (N _ _)      = 0
varLevel (S _ _)      = 0
varLevel (C _ _)      = 0
varLevel (Same _ _)   = 0
varLevel (Neg f)      = varLevel f
varLevel (Conj fs)    = maximum (map varLevel fs)
varLevel (Disj fs)    = maximum (map varLevel fs)
varLevel (Impl f g)   = maximum (map varLevel [f,g])
varLevel (K _ p f)    = max (2 + varLevelP (protoTerm p)) (varLevel f)
varLevel (HatK _ p f) = max (2 + varLevelP (protoTerm p)) (varLevel f)
varLevel (Box _ f)    = varLevel f
varLevel (Dia _ f)    = varLevel f
varLevel (ExistsAg varf) = 1 + varLevel (varf 999)
varLevel (ForallAg varf) = 1 + varLevel (varf 999)

varLevelP :: Prog -> Int
varLevelP (Test f) = varLevel f
varLevelP (Call _ _) = 0
varLevelP (Seq ps) = maximum (map varLevelP ps)
varLevelP (Cup ps) = maximum (map varLevelP ps)
varLevelP (CupAg varp) = 1 + varLevelP (varp 999)
varLevelP (Star p) = varLevelP p

-- useful abbreviations --

-- binary conjunction
con :: Form -> Form -> Form
con f g = Conj [f,g]

-- binary disjunctions
dis :: Form -> Form -> Form
dis f g = Disj [f,g]

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
allSuperExperts proto = ForallAg (`superExpert` proto)

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

-- PDL style programming
ifthenelse :: Form -> Prog -> Prog -> Prog
ifthenelse f p q = Cup [Seq [Test f, p], Seq [Test (Neg f), q]]

-- | Repeat a program exactly k many times:
iter :: Int -> Prog -> Prog
iter k p = Seq (take k $ repeat p)

-- | Repeat a program up to k many times:
iterUpTo :: Int -> Prog -> Prog
iterUpTo k p = Cup [ iter j p | j <- [0..k] ]

-- General Protocols --
type Protocol = (Agent,Agent) -> Form

instance Eq Protocol where
  p1 == p2 = p1 (0,1) == p2 (0,1)  &&  p1 (1,0) == p2 (1,0)

instance Ord Protocol where
  compare p1 p2 = compare (p1 (0,1)) (p2 (0,1))

instance Show Protocol where
  show p = "(\\("++[c]++","++[d]++") -> " ++ rep (show n) [c] (rep (show (n + 1)) [d] $ show (p (n,n+1))) ++ ")" where
    n = varLevel (p (1,2))
    c = variables !! n
    d = variables !! (n + 1)

anyCall,noCall :: Protocol
anyCall = const Top
noCall = const Bot

-- | Learn New Secrets
lns :: Protocol
lns (x, y) = Neg $ S x y

-- | Call Me Once
cmo :: Protocol
cmo (x, y) = Conj [ Neg (C x y), Neg (C y x) ]

-- | Possible Information Growth
pig :: Protocol
pig (x,y) = HatK x anyCall $
  ExistsAg (\z -> (S x z `con` Neg (S y z))  `dis` (Neg (S x z) `con` S y z))

data Mode = Sync | ASync deriving (Eq,Ord,Show)

type State = (Mode,Graph,Sequence)

currentGraph :: State -> Graph
currentGraph (_,beginState,history) = calls beginState history

historyOf :: State -> Sequence
historyOf (_,_,history) = history

pointCall :: State -> Call -> State
pointCall (mode,beginState,hist) c = (mode, beginState, hist ++ [c])

-- | pretty print a state: initial graph, history, resulting state
ppState :: State -> String
ppState (mode,g,h) = ppRel (fst g)
  ++ if null h then [] else " " ++ ppSequence h ++ "  " ++ ppGraph (calls g h)
  ++ if mode == ASync then " (Async)" else []

possibleCalls :: State -> [Call]
possibleCalls state =
  [ (x,y) | (x,setYs) <- IntMap.toList (fst $ currentGraph state)
          , y <- IntSet.toList setYs
          , x /= y ]

allowedCalls :: Protocol -> State -> [Call]
allowedCalls proto state = filter (eval state . proto) (possibleCalls state)

-- | Do the two given graphs look the same for the given agent?
localSameFor :: Agent -> Graph -> Graph -> Bool
localSameFor a s s' = (fst s `at` a) == (fst s' `at` a) && (snd s `at` a) == (snd s' `at` a)

-- Epistemic Alternatives: Points that an agent confuses with the given one.
-- Depends on the protocol. Note: synchronous, with initCK
-- TODO use Set Point instead?
epistAlt :: Agent -> Protocol -> State -> [State]
epistAlt _ _     (Sync, g, []     ) = [ (Sync, g, []) ] -- initial graph is common knowledge!
epistAlt a proto (Sync, g, history) =
  let
    (prev, lastevent) = (init history, last history)
    lastcall@(x,y)    = lastevent -- this pattern match might fail, but laziness saves us
  in sort $
    if a `isin` lastevent
       -- if a was in the last call, consider all allowed histories
       -- before, then restrict to localSameFor x and y, because a is
       -- one of them and observes both their local states.
       -- (This means we do inspect-then-merge!)
       then [ (Sync,g',althist ++ [lastcall])
              | (_,g',althist) <- epistAlt a proto (Sync,g,prev)
              , eval (Sync,g',prev) (proto lastcall)
              , eval (Sync,g',althist) (proto lastcall)
              , localSameFor x (calls g' althist) (calls g prev)
              , localSameFor y (calls g' althist) (calls g prev) ]
       -- if a was NOT in the last event, consider all non-a events possible
       -- which are allowed according to the protocol that is CK
       else [ (Sync,g',cs'++[altevent])
              | (_,g',cs') <- epistAlt a proto (Sync,g,prev)
              , altevent <- allowedCalls proto (Sync,g',cs')
              , not $ a `isin` altevent ]
-- | A first try to compute the asynchronous epistemic alternatives.
-- NOTE: we assume for now that the async relation extends the sync relation.
-- This seems true for ANY, but there are protocol (conditions) where this is wrong!?
epistAlt a proto (ASync,g,history) =
  [ (ASync,g,altHistory)
  | k <- [(length (a `reduction` history)) .. totalBound]
  , altHistory <- sequencesUpTo proto (ASync, g, []) k
  , a `reduction` history == a `reduction` altHistory
  , alwaysLocalSameFor g a history altHistory
  ]

-- | Check localSameFor for caller and callee after all calls where a was involved.
-- Precondition: history and altHistory have the same a-reduction.
alwaysLocalSameFor :: Graph -> Agent -> Sequence -> Sequence -> Bool
alwaysLocalSameFor g a history altHistory =
  and [ localSameFor i (calls g s1) (calls g s2)
      | (k1,k2) <- callMap a history altHistory
      , let s1 = take (k1+1) history
      , let s2 = take (k2+1) altHistory
      , if last s1 /= last s2 then error "this should not happen" else True
      , i <- let (x,y) = last s1 in [x,y] -- NOTE: crucial, use s1 or s2, but not history here!!!
      ]

totalBound :: Int
totalBound = 7

-- | Given two sequences which have the same a-reduction, return pairs of indices for the same calls.
-- Example: callMap 3 [(0,1),(2,3),(0,3),(0,2)] [(2,3),(0,1),(0,3)] == [(1,0),(2,2)]
callMap :: Agent -> Sequence -> Sequence -> [(Int,Int)]
callMap = callMap' 0 0 where
  callMap' :: Int -> Int -> Agent -> Sequence -> Sequence -> [(Int,Int)]
  callMap' _  _  _ []     _      = [ ]
  callMap' nc nd a (c:cs) []     | a `isin` c = error "sequences do not have the same reduction!"
                                 | otherwise = callMap' (nc+1) nd a cs []
  callMap' nc nd a (c:cs) (d:ds) | a `isin` c =
                                     if c == d
                                       then [(nc,nd)] ++ callMap' (nc+1) (nd+1) a cs     ds
                                       else              callMap' nc     (nd+1) a (c:cs) ds
                                 | otherwise =           callMap' (nc+1) nd     a cs     (d:ds)

-- Semantics --

-- evaluate formulas
eval :: State -> Form -> Bool
eval state (N a b  )    = b `IntSet.member` (fst (currentGraph state) `at` a)
eval state (S a b  )    = b `IntSet.member` (snd (currentGraph state) `at` a)
eval (_,_,history) (C a b  ) = (a,b) `elem` history
eval _     (Same a b)   = a == b
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
eval state (ExistsAg f) = any (eval state . f) (agentsOf state)
eval state (ForallAg f) = all (eval state . f) (agentsOf state)

(|=) :: State -> Form -> Bool
(|=) = eval

-- evaluate programs
runs :: State -> Prog -> Set State
runs state     (Test f)     | eval state f = Set.singleton state
                            | otherwise    = Set.empty
-- we always evaluate calls, ignoring protocol and whether it is ck:
runs (m,g,sigma) (Call a b) | eval (m,g,sigma) (N a b) = Set.singleton (m,g,sigma++[(a,b)])
                            | otherwise              = Set.empty
runs state     (Seq []    ) = Set.singleton state
runs state     (Seq (p:ps)) = setUnion $ Set.map (\state' -> runs state' (Seq ps)) (runs state p)
runs state     (Cup ps)     = setUnion $ Set.map (runs state) (Set.fromList ps)
runs state     (CupAg p)    = Set.unions $ map (runs state . p) (agentsOf state)
runs state     (Star p)     = lfp loop $ Set.singleton state where
  loop states = Set.union states (setUnion $ Set.map (`runs` p) states)


-- Abbreviations to run protocols and describe success in formulas --

protoCanGoOn, protoFinished :: Protocol -> Form
protoCanGoOn  proto = ExistsAg (\x -> ExistsAg (\y -> Neg (Same x y) `con` Conj [       N x y,       proto (x,y) ]))
protoFinished proto = ForallAg (\x -> ForallAg (\y -> Same x y `dis` Disj [ Neg $ N x y, Neg $ proto (x,y) ]))

protoTerm :: Protocol -> Prog
protoTerm proto = Seq [Star (protoStep proto), Test (protoFinished proto)]

protoStep :: Protocol -> Prog
protoStep proto =
  CupAg (\x -> CupAg (\y ->
    ifthenelse (Neg (Same x y))
               (Seq [ Test (Conj [N x y, proto (x,y)]), Call x y])
               (Test Bot)
  ))

isWeaklySuccForm :: Protocol -> Form
isWeaklySuccForm proto = Dia (protoTerm proto) allExperts

isStronglySuccForm :: Protocol -> Form
isStronglySuccForm proto = Box (protoTerm proto) allExperts

isStronglyUnsuccForm :: Protocol -> Form
isStronglyUnsuccForm proto = Box (protoTerm proto) (Neg allExperts)

isStronglySuperSuccForm :: Protocol -> Protocol -> Form
isStronglySuperSuccForm knownProto proto = Box (protoTerm proto) (allSuperExperts knownProto)

sequences :: Protocol -> State -> [Sequence]
sequences proto (m,g,sigma)
  | null (allowedCalls proto (m,g,sigma)) = [ [] ]
  | otherwise = [ c : rest | c <- allowedCalls proto (m,g,sigma)
                           , rest <- sequences proto (m,g,sigma++[c]) ]

-- | All maximal sequences of up to n calls after the given state.
sequencesUpTo :: Protocol -> State -> Int -> [Sequence]
sequencesUpTo _     (_,_,_    ) 0 = [ [] ]
sequencesUpTo proto (m,g,sigma) n
  | null (allowedCalls proto (m,g,sigma)) = [ [] ]
  | otherwise = [ c : rest | c <- allowedCalls proto (m,g,sigma)
                           , rest <- sequencesUpTo proto (m,g,sigma++[c]) (n-1) ]

isSuccSequence :: State -> Sequence -> Bool
isSuccSequence (_,g,sigma) cs = isSolved (calls g (sigma ++ cs))

isSuperSuccSequence :: Protocol -> State -> Sequence -> Bool
isSuperSuccSequence proto (m,g,sigma) cs = (m, g, sigma ++ cs) |= ForallAg (`superExpert` proto)

compareSequences :: State -> [Protocol] -> [(Sequence,[Bool])]
compareSequences s protos =
  [ (sequ, [ sequ `elem` sequences p s | p <- protos ]) | sequ <- allsequs ] where
    allsequs = sort $ nub $ concat [sequences p s | p <- protos]

isSequenceOf :: Protocol -> State -> Sequence -> Bool
isSequenceOf _     _       []       = True
isSequenceOf proto current (c:rest) = eval current (proto c) && isSequenceOf proto (pointCall current c) rest

knowledgeOfIn :: Agent -> State -> [Char]
knowledgeOfIn a s = [ if s |= S a b then charAgent b else ' ' | b <- agentsOf s ]

metaKnowledgeOfIn :: Agent -> Protocol -> State -> [Char]
metaKnowledgeOfIn a proto s = [ charFor b | b <- agentsOf s ] where
  charFor b
    | s |= Neg (expert b)       = ' '
    | s |= K a proto Bot        = '_'
    | s |= K a proto (expert b) = toUpper (charAgent b)
    | otherwise                 = ' '

knowledgeLine :: State -> Protocol -> String
knowledgeLine s proto = concat
  [ "  " ++ knowledgeOfIn a s ++ " " ++ metaKnowledgeOfIn a proto s
  | a <- agentsOf s ]

knowledgeOverview :: State -> Protocol -> IO ()
knowledgeOverview (m,g,sigma) proto = do
  putStr "  "
  putStrLn $ knowledgeLine (m,g,[]) proto
  mapM_ (\n -> do
            let s@(_,_,history) = (m, g, take n sigma)
            putStr (charCall (last history))
            putStrLn $ knowledgeLine s proto
        ) [1 .. length sigma]

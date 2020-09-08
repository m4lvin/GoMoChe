module Gossip.Examples where

import Gossip
import Gossip.General
import Gossip.Strengthening

-- | execution tree example, three agents:  a -> b <--> c
threeExample :: Graph
threeExample = exampleFromList [[0,1],[1,2],[1,2]]

-- | a three agent example where LNS is strongly successful
easyExample :: Graph
easyExample = exampleFromList [[0,1,2],[1],[2]]

-- | Square with one diagonal, four agents
squareExample :: Graph
squareExample = exampleFromList [[0,1,2],[1],[2],[0,1,2,3]]

-- | Spaceship, four agents
-- a and d know b's number,
-- b knows c's number.
-- c knows no numbers
spaceshipExample :: Graph --         a     b     c   d
spaceshipExample = exampleFromList [[0,1],[1,2],[2],[1,3]]

-- | N example. four agents
nExample :: Graph
nExample = exampleFromList [[0],[1],[0,2],[0,1,3]]

-- | Diamond, four agents
diamondExample :: Graph
diamondExample = exampleFromList [[0],[1],[0,1,2],[0,1,3]]

diamondSolvers :: [Sequence]
diamondSolvers =
  [ [(2,0),(3,0),(3,1),(2,1),(0,1)]
  , [(2,0),(3,1),(3,0),(2,1)]
  , [(2,1),(3,0),(3,1),(2,0)]
  , [(2,1),(3,1),(3,0),(2,0),(1,0)]
  , [(3,0),(2,0),(2,1),(3,1),(0,1)]
  , [(3,0),(2,1),(2,0),(3,1)]
  , [(3,1),(2,0),(2,1),(3,0)]
  , [(3,1),(2,1),(2,0),(3,0),(1,0)] ]

-- | Diamond with arms, six agents, for the main impossibility result
lemmaExample :: Graph
lemmaExample = exampleFromList [[0,2,3],[1,2],[2],[3],[3,4],[2,3,5]]

-- | Triangle, six agents
triangleExample :: Graph
triangleExample = exampleFromList [[0],[1,4,5],[2,4,0],[3,5,0],[4],[5]]

sixteenLns :: Sequence
sixteenLns =
  [ (1,2), (3,4), (5,6), (7,8), (a,b), (c,d), (e,f), (g,h)
  , (2,3), (4,5), (6,7), (8,1), (b,c), (d,e), (f,g), (h,a)
  , (1,a), (4,c), (7,h), (6,f)
  ] where [a,b,c,d,e,f,g,h] = 0:[9..15]

-- NOTE: only the last cal (6,f) here is not spider permitted!
sixteenAlmostSpi :: Sequence
sixteenAlmostSpi =
  [ (1,2), (3,4), (5,6), (7,8), (a,b), (c,d), (e,f), (g,h)
  , (3,2), (5,4), (7,6), (1,8), (c,b), (e,d), (g,f), (a,h)
  , (1,a), (c,4), (7,h), (6,f)
  ] where [a,b,c,d,e,f,g,h] = 0:[9..15]

-- | Sync, five agents:: This list is empty, hence at least 7 calls are needed to make someone a super expert.
syncFiveAgentsSequencesReachingAsuperExpertUpToSixCalls :: [Sequence]
syncFiveAgentsSequencesReachingAsuperExpertUpToSixCalls = filter reachesAsuperExpert toCheck where
  toCheck = sequencesUpTo (wlog anyCall) (Sync, totalInit 5, [(0,1)]) 5 -- wlog we fix the first call
  reachesAsuperExpert sigma = (Sync, totalInit 6, [(0,1),(2,3)] ++ sigma) |= Conj [ allExperts, ExistsAg (\i -> superExpert i (wlog anyCall)) ]

-- | ASync, four agents: there is no  sequence with up to 5 calls not everyone is a super expert.
-- Note: this takes around 10 minutes.
asyncFiveCallsNoSuperSucc :: Bool
asyncFiveCallsNoSuperSucc = and [ s |= f | s <- states ] where
  -- wlog fix first two calls to be one of two sequences:
  states = [ (ASync, totalInit 4, parseSequence sigma) | sigma <- ["ab;cd", "ab;bc"] ]
  f = Box
    (iterUpTo 5 $ protoStep (wlog anyCall))
    (Neg allExperts `dis` (Neg $ allSuperExperts (wlog anyCall)))

-- The same, but show each result while running and stop if there is a counterexample.
asyncFiveCallsNoSuperSucc' :: IO ()
asyncFiveCallsNoSuperSucc' = mapM_ (print . (\s -> (s,if isGood s then error ("\n\nfound!\n" ++ ppSequence s ++ "\n\n") else False))) (tries 5) where
  -- sigma = parseSequence "ab;cd" -- start with two non-overlapping calls
  sigma = parseSequence "ab;bc" -- start with two overlapping calls
  tries = sequencesUpTo (wlog anyCall) (ASync, totalInit 4, sigma)
  isGood s = (ASync, totalInit 4, sigma ++ s) |=
    (allExperts `con` allSuperExperts (wlog anyCall))

-- | ASync, four agents: The given sequence cannot be extended to super success within three calls.
-- Note: this takes around 1.5 minutes.
exampleNotSupSuccInThree :: Bool
exampleNotSupSuccInThree =
  (ASync, totalInit 4, parseSequence "ac;ad;ac;bc;ac") |=
    Box (iterUpTo 3 $ protoStep (wlog anyCall))
      (Neg $ Conj [ allExperts, allSuperExperts (wlog anyCall) ])

-- The same, but show each result while running and stop if there is a counterexample.
exampleNotSupSuccInThree' :: IO ()
exampleNotSupSuccInThree' = mapM_ (print . (\s -> (s, if isGood s then error ("\n\nfound!\n" ++ ppSequence s ++ "\n\n") else False))) (tries 1 ++ tries 2 ++ tries 3) where
  sigma = parseSequence "ac;ad;ac;bc;ac"
  tries = sequencesUpTo (wlog anyCall) (ASync, totalInit 4, sigma)
  isGood s = (ASync, totalInit 4, sigma ++ s) |=
    (allExperts `con` allSuperExperts (wlog anyCall))

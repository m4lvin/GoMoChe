{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Gossip.Examples where

import Gossip

a,b,c,d,e,f :: Agent
(a,b,c,d,e,f) = (0,1,2,3,4,5)

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
  [ (1,2), (3,4), (5,6), (7,8), (a',b'), (c',d'), (e',f'), (g',h')
  , (2,3), (4,5), (6,7), (8,1), (b,c'), (d',e'), (f',g'), (h',a')
  , (1,a'), (4,c'), (7,h'), (6,f')
  ] where [a',b',c',d',e',f',g',h'] = 0:[9..15]

-- NOTE: only the last cal (6,f) here is not spider permitted!
sixteenAlmostSpi :: Sequence
sixteenAlmostSpi =
  [ (1,2), (3,4), (5,6), (7,8), (a',b'), (c',d'), (e',f'), (g',h')
  , (3,2), (5,4), (7,6), (1,8), (c',b'), (e',d'), (g',f'), (a',h')
  , (1,a'), (c',4), (7,h'), (6,f')
  ] where [a',b',c',d',e',f',g',h'] = 0:[9..15]

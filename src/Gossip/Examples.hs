module Gossip.Examples where

import Gossip

-- | execution tree example, three agents:  a -> b <--> c
threeExample :: State
threeExample = exampleFromList [[0,1],[1,2],[1,2]]

-- | Square with one diagonal, four agents
squareExample :: State
squareExample = exampleFromList [[0,1,2],[1],[2],[0,1,2,3]]

-- | N example. four agents
nExample :: State
nExample = exampleFromList [[0],[1],[0,2],[0,1,3]]

-- | Diamond, four agents
diamondExample :: State
diamondExample = exampleFromList [[0],[1],[0,1,2],[0,1,3]]

-- | Diamond with arms, six agents
lemmaExample :: State
lemmaExample = exampleFromList [[0,2,3],[1,2],[2],[3],[3,4],[2,3,5]]

-- | Triangle, six agents
triangleExample :: State
triangleExample = exampleFromList [[0],[1,4,5],[2,4,0],[3,5,0],[4],[5]]

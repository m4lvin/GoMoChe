module Gossip.Examples.Epistemicity where

import Data.List

import Gossip
import Gossip.General

-- * Epistemicity - Chapter 9 in [vD2025:RaG]

-- | Triangle, six agents
epiEx :: Graph
epiEx = parseGraph "01-12-02-0123 I4" -- directed triangle abc, and d knows all

myProt :: Protocol
myProt (a, b) = i `con` ( ( ii `con` iii ) `dis` iv ) where
  i = N a b -- a has number of b
  ii = ExistsAg (Neg . N a) -- a does not have all numbers
  iii = K a anyCall $ Conj [ Neg (S b c) | c <- [0..3], c /= b ] -- a knows that b has only b -- FIXME use ForallAg ?
  iv = Disj [ Conj [ ExistsAg (\ d -> Neg (Same c d) `con` ExistsAg (\ e -> S c d `con` S c e))
                   | c <- bs ]
            | bs <- subsequences [0..3]
            , length bs >= 3
            ] -- majority knows at least two secrets

isEpistemicAt :: (Agent -> Form -> Form) -> Protocol -> State -> Bool
isEpistemicAt op p (g, sigma) =
  and [ (g, sigma) |= (p (i,j) `Impl` op i (p (i,j)))
      | i <- agentsOf g
      , j <- agentsOf g
      ]

tests :: [(String,Bool)]
tests =
  [ ( "these sequences up to 2"
    , sequencesUpTo myProt (epiEx,[]) 2 ==
      [[(0,1),(0,2)],[(0,1),(1,2)],[(1,2),(1,0)],[(1,2),(2,0)],[(2,0),(0,1)],[(2,0),(2,1)]] )
  , ( "myProt isEpistemicAt K^P (G, [(0,1),(1,2)])"
    , isEpistemicAt (`K` myProt) myProt (epiEx,[(0,1),(1,2)]) )
  , ( "myProt isEpistemicAt K (G, [(0,1),(1,2)])"
    , isEpistemicAt (`K` anyCall) myProt (epiEx,[(0,1),(1,2)]) )
  ]

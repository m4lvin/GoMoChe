module Gossip.Causal where

import Data.List (subsequences)

import Gossip
import Gossip.Internal (tcl)

-- | Occurence of a call.
type CallOcc = (Int,Call)

callsIn :: Sequence -> [CallOcc]
callsIn = zip [0..]

cause0 :: Sequence -> CallOcc -> CallOcc -> Bool
cause0 sigma iCall@(i,(a,b)) jCall@(j,(c,d)) =
  i < j
  &&
  iCall `elem` callsIn sigma
  &&
  jCall `elem` callsIn sigma
  &&
  (a `elem` [c,d] || b `elem` [c,d])

cause :: Sequence -> CallOcc -> CallOcc -> Bool
cause sigma = tcl (callsIn sigma) (cause0 sigma)

causalChain :: Sequence -> [CallOcc] -> Bool
causalChain sigma tauOcc = map snd tauOcc `elem` subsequences sigma && causeLinked tauOcc where
  causeLinked [] = True
  causeLinked [_] = True
  causeLinked (occX:occY:rest) = cause0 sigma occX occY && causeLinked (occY:rest)

causalChains :: Sequence -> [[CallOcc]]
causalChains sigma = filter (causalChain sigma) (subsequences (callsIn sigma))

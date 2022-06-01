module Gossip.Lucky where

import Gossip
import Gossip.General

-- | Agent a is lucky in call ab iff a learns that c /= b is an expert.
isLucky :: State -> Protocol -> Agent -> Bool
isLucky (_, _, []) _ _ = False
isLucky (mode, g, sigma) proto a =
  a `isin` last sigma
  &&
  or [    ( (mode, g, init sigma) |= Neg (K a proto (expert c)) )
       && ( (mode, g,      sigma) |= K a proto (expert c) )
     | c <- agentsOf g, c /= b, c /= a ]
  where
    ab = last sigma
    b = if fst ab == a then snd ab else fst ab

luckiesOf :: State -> Protocol -> [Agent]
luckiesOf state proto = filter (isLucky state proto) (agentsOf state)

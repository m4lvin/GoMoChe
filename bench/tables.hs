module Main where

import Data.List

import Gossip
import Gossip.Examples
import Gossip.General
import Gossip.Strengthening
import Gossip.Internal (finiteIterate)

main :: IO ()
main = do
  writeFile "gossip-n-table.tex" $
    texCompareSequences (nExample,[]) nProtos
  writeFile "gossip-diamond-table.tex" $
    texCompareSequences (diamondExample,[(2,0)]) diamondProtos

nProtos :: [Protocol]
nProtos =
  [ lns
  , strengHard lns
  , strengSoft lns
  , strengStepHard lns
  , finiteIterate 2 strengStepHard lns
  , finiteIterate 3 strengStepHard lns
  , finiteIterate 4 strengStepHard lns
  , strengStepSoft lns
  , finiteIterate 2 strengStepSoft lns
  , finiteIterate 3 strengStepSoft lns
  , finiteIterate 4 strengStepSoft lns
  , finiteIterate 5 strengStepSoft lns ]

diamondProtos :: [Protocol]
diamondProtos =
  [ lns
  , strengHard lns
  , strengStepHard (strengHard lns) -- extra
  , strengSoft lns
  , strengStepHard lns
  , finiteIterate 2 strengStepHard lns
  , finiteIterate 3 strengStepHard lns
  , finiteIterate 4 strengStepHard lns
  , strengStepSoft lns
  , finiteIterate 2 strengStepSoft lns
  , finiteIterate 3 strengStepSoft lns
  , finiteIterate 3 strengStepHard (strengStepSoft lns) ]

texCompareSequences :: State -> [Protocol] -> String
texCompareSequences state protos = wrap . concatMap texify $ compareSequences state protos where
  wrap s = "\\begin{tabular}{ll" ++ replicate (length protos) 'l' ++ "}\n"
    ++ "  & " ++ intercalate "\n  & " (map (\p -> "$" ++ texLabel p ++ "$") protos) ++ "\\\\\n"
    ++ s ++ "\\end{tabular}\n"
  texify (s,list) = concat
    [ texSequence s, " & "
    , intercalate " & " (map (booltex (isSuccSequence state s)) list)
    , " \\\\\n" ]
  texSequence [] = "$\\epsilon$"
  texSequence s  = ppSequence s
  booltex _     False = "  "
  booltex True  True  = "$\\checkmark$"
  booltex False True  = "$\\times$"

texLabel :: Protocol -> String
texLabel p
  | p == lns                                = "LNS"
  | p == strengHard lns                     = "\\cdot^\\hard "
  | p == strengStepHard (strengHard lns)    = "{(\\cdot^\\hard)}^\\stephard"
  | p == strengSoft lns                     = "\\cdot^\\soft"
  | p == strengStepHard lns                 = "\\cdot^\\stephard"
  | p == finiteIterate 2 strengStepHard lns = "\\cdot^{\\stephard 2}"
  | p == finiteIterate 3 strengStepHard lns = "\\cdot^{\\stephard 3}"
  | p == finiteIterate 4 strengStepHard lns = "\\cdot^{\\stephard 4}"
  | p == strengStepSoft lns                 = "\\cdot^\\stepsoft"
  | p == finiteIterate 2 strengStepSoft lns = "\\cdot^{\\stepsoft 2}"
  | p == finiteIterate 3 strengStepSoft lns = "\\cdot^{\\stepsoft 3}"
  | p == finiteIterate 4 strengStepSoft lns = "\\cdot^{\\stepsoft 4}"
  | p == finiteIterate 5 strengStepSoft lns = "\\cdot^{\\stepsoft 5}"
  | p == finiteIterate 3 strengStepHard (strengStepSoft lns) = "{(\\cdot^\\stepsoft)}^{\\stephard 3}"
  | otherwise                               = error $ "Unknown protocol: " ++ show p

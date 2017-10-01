{-# LANGUAGE FlexibleInstances #-}

module Gossip.Tree where

import Gossip
import Gossip.LocalProto
import Gossip.General

data ExecutionTree = Node Point [(Call,ExecutionTree)] deriving (Eq,Ord)

instance ProvidesAgentSet ExecutionTree where
  agentsOf (Node n _) = agentsOf $ fst n


-- MAKE TREES

localTree :: Point -> LocalProtocol -> ExecutionTree
localTree root proto = Node root [ (c, localTree (root `pointCall` c) proto) | c <- proto (uncurry calls root) ]

-- | generate execution tree for a general protocol
tree :: GossipModel -> Point -> Protocol -> ExecutionTree
tree gomo point@(g,sigma) proto =
  Node point [ (c, goOnWith c) | c <- allowedCalls proto gomo point ]
  where
    goOnWith c = tree gomo (g,sigma ++ [c]) proto


-- SUMMARIZE TREES

sumTree :: ExecutionTree -> (Int,Int)
sumTree (Node n []) | isSolved (uncurry calls n) = (1,0)
                    | otherwise                  = (0,1)
sumTree (Node _ ts) = pairSum $ map (sumTree . snd) ts

pairSum :: [(Int,Int)] -> (Int,Int)
pairSum []           = (0,0)
pairSum ((x,y):rest) = (x + xs, y + ys) where (xs,ys) = pairSum rest


-- SHOW TREES

indent :: String
indent = "  "

instance Show ExecutionTree where
  show = s indent where
    s pre (Node n cts) =
      ppState (currentGraph n) ++ "\n" ++
      concatMap (\(c,t) -> pre ++ show c ++ ": " ++ s (pre++indent) t) cts

showTreeUpTo :: Int -> ExecutionTree -> IO ()
showTreeUpTo k0 t0 = putStrLn $ s indent k0 t0 where
  s _ 0 t = case sumTree t of
    (0,0) -> error "nothing!"
    (0,y) -> "⚡ " ++ show y ++ "\n"
    (x,0) -> "☺ " ++ show x ++ "\n"
    (x,y) -> "... " ++ show x ++ "/" ++ show y ++ "\n"
  s pre k (Node n cts) =
    ppState (currentGraph n) ++ "\n" ++
    concatMap
      (\(c,t) -> pre ++ show c ++ ": " ++ s (pre++indent) (k-1) t)
      cts

showTreeUpToDecision :: ExecutionTree -> IO ()
showTreeUpToDecision t0 = putStrLn $ s indent t0 where
  s pre t@(Node n cts) = case sumTree t of
    (0,0) -> error "nothing!"
    (0,y) -> "⚡ " ++ show y ++ "\n"
    (x,0) -> "☺ " ++ show x ++ "\n"
    (_,_) -> ppState (currentGraph n) ++ "\n" ++
              concatMap
                (\(c,newt) -> pre ++ show c ++ ": " ++ s (pre++indent) newt)
                cts

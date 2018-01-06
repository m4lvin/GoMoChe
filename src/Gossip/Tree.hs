{-# LANGUAGE FlexibleInstances #-}

module Gossip.Tree where

import Data.Maybe

import Gossip
import Gossip.LocalProto
import Gossip.General

data ExecutionTree = Node State [(Call,ExecutionTree)] deriving (Eq,Ord)

instance ProvidesAgentSet ExecutionTree where
  agentsOf (Node n _) = agentsOf $ fst n


-- MAKE TREES

localTree :: LocalProtocol -> State -> ExecutionTree
localTree loproto root = Node root [ (c, localTree loproto (root `pointCall` c)) | c <- loproto (uncurry calls root) ]

-- | generate execution tree for a general protocol
tree :: Protocol -> State -> ExecutionTree
tree proto point@(g,sigma) =
  Node point [ (c, goOnWith c) | c <- allowedCalls proto point ]
  where
    goOnWith c = tree proto (g,sigma ++ [c])

-- | summarize a tree to numbers pf (solved, stuck) branches
sumTree :: ExecutionTree -> (Int,Int)
sumTree (Node n []) | isSolved (uncurry calls n) = (1,0)
                    | otherwise                  = (0,1)
sumTree (Node _ ts) = pairSum $ map (sumTree . snd) ts where
  pairSum []           = (0,0)
  pairSum ((x,y):rest) = (x + xs, y + ys) where (xs,ys) = pairSum rest

-- UNIFORM BACKWARD INDUCTION

-- | a tree is terminal iff it has no calls/children
isTerminal :: ExecutionTree -> Bool
isTerminal (Node _ cs) = null cs

-- | find point in an execution tree
findInTree :: State -> ExecutionTree -> Maybe ExecutionTree
findInTree p n@(Node np cs)
  | p == np   = Just n
  | otherwise = case mapMaybe (findInTree p . snd) cs of
                  [] -> Nothing
                  [thisn] -> Just thisn
                  _ -> error "Point found twice in the same tree!"

-- | Hard Uniform Backward Reasoning
hardUBR :: Protocol -> ExecutionTree -> ExecutionTree
hardUBR proto fullTree = hardUBR' fullTree where
  -- keep fullTree constant so we can still findInTree if epistAlt in other branches!
  hardUBR' (Node p cs) = Node p $ concatMap purge cs where
    purge (c@(a,b), newsubTree) =
      [ (c, hardUBR' newsubTree) | not $ any (toBeRemovedAt (a,b)) (epistAlt a proto p) ]
    toBeRemovedAt (a,b) (g,sigma') =
      isJust (findInTree (g,sigma'++[(a,b)]) fullTree)
      && isTerminal (fromJust $ findInTree (g,sigma'++[(a,b)]) fullTree)
      && eval (g,sigma'++[(a,b)]) (Neg allExperts)

-- | Soft Uniform Backward Reasoning
softUBR :: Protocol -> ExecutionTree -> ExecutionTree
softUBR proto fullTree = softUBR' fullTree where
  -- keep fullTree constant so we can still findInTree if epistAlt in other branches!
  softUBR' (Node p cs) = Node p $ concatMap purge cs where
    purge (c@(a,b), newsubTree) =
      [ (c, softUBR' newsubTree) | any (toBeKept (a,b)) (epistAlt a proto p) ]
    toBeKept (a,b) (g,sigma') =
      isJust (findInTree (g,sigma'++[(a,b)]) fullTree)
      && (  not (isTerminal (fromJust $ findInTree (g,sigma'++[(a,b)]) fullTree))
         || eval (g,sigma'++[(a,b)]) allExperts)

-- SHOW TREES

indent :: String
indent = "     "

instance Show ExecutionTree where
  show = s "" where
    s pre (Node n cts) =
      ppGraph (currentGraph n) ++ "\n" ++
      concatMap (\(c,t) -> pre ++ show c ++ ": " ++ s (pre ++ show c) t) cts

showTreeUpTo :: Int -> ExecutionTree -> IO ()
showTreeUpTo k0 t0 = putStrLn $ s indent k0 t0 where
  s _ 0 t = case sumTree t of
    (0,0) -> error "nothing!"
    (0,y) -> "⚡ " ++ show y ++ "\n"
    (x,0) -> "☺ " ++ show x ++ "\n"
    (x,y) -> "... " ++ show x ++ "/" ++ show y ++ "\n"
  s pre k (Node n cts) =
    ppGraph (currentGraph n) ++ "\n" ++
    concatMap
      (\(c,t) -> pre ++ show c ++ ": " ++ s (pre++indent) (k-1) t)
      cts

showTreeUpToDecision :: ExecutionTree -> IO ()
showTreeUpToDecision t0 = putStrLn $ s indent t0 where
  s pre t@(Node n cts) = case sumTree t of
    (0,0) -> error "nothing!"
    (0,y) -> "⚡ " ++ show y ++ "\n"
    (x,0) -> "☺ " ++ show x ++ "\n"
    (_,_) -> ppGraph (currentGraph n) ++ "\n" ++
              concatMap
                (\(c,newt) -> pre ++ show c ++ ": " ++ s (pre++indent) newt)
                cts

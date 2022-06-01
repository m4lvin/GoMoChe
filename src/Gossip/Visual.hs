{-# LANGUAGE FlexibleInstances #-}

module Gossip.Visual where

import Data.Function
import Data.GraphViz hiding (C, N, Star)
import qualified Data.GraphViz.Types.Generalised as GenGV
import Data.GraphViz.Types.Monadic
import Data.GraphViz.Attributes.Complete (Attribute(Dir,Rank,Style),StyleItem (SItem),StyleName(Dashed))
import qualified Data.IntSet as IntSet
import Data.List
import qualified Data.Sequence as Seq
import Data.Text.Lazy (pack)
import System.Process
import System.IO.Temp

import Gossip
import Gossip.Internal
import Gossip.General
import Gossip.Tree

class DotAble a where
  dot :: a -> GenGV.DotGraph String
  dispDot :: a -> IO ()
  dispDot x = runGraphvizCanvas Data.GraphViz.Dot (dot x) Xlib
  texDot :: a -> IO String
  texDot x = withSystemTempDirectory "CKgossip" $ \tmpdir -> do
    _ <- runGraphviz (dot x) DotOutput (tmpdir ++ "/temp.dot")
    runAndWait $ "dot2tex --figonly -ftikz -traw -p --autosize -w -s "++tmpdir++"/temp.dot | sed '/^$/d' > "++tmpdir++"/temp.tex;"
    readFile (tmpdir ++ "/temp.tex")
  svg :: a -> IO String
  svg x = withSystemTempDirectory "CKgossip" $ \tmpdir -> do
    _ <- runGraphviz (dot x) Svg (tmpdir ++ "/temp.svg")
    readFile (tmpdir ++ "/temp.svg")

runAndWait :: String -> IO ()
runAndWait command = do
  (_,_,_,pid) <- runInteractiveCommand command
  _ <- waitForProcess pid
  return ()

instance DotAble Graph where
  dot (n,s) = digraph' $ do
    mapM_ (\x -> node (show x) [toLabel (show x)]) (agentsOf n)
    let sDoubles = [ (x,y) | x <- agentsOf n, y <- IntSet.toList (s `at` x), x < y, x `IntSet.member` (s `at` y) ]
    mapM_ (\(x,y) -> edge (show x) (show y) [Dir Both] ) sDoubles
    let sEdges = [ (x,y) | x <- agentsOf n, y <- IntSet.toList (s `at` x), x /= y, (x,y) `notElem` sDoubles, (y,x) `notElem` sDoubles ]
    mapM_ (\(x,y) -> edge (show x) (show y) [] ) sEdges
    let nDoubles = [ (x,y) | x <- agentsOf n, y <- IntSet.toList (n `at` x), x < y, x `IntSet.member` (n `at` y), (x,y) `notElem` sDoubles, (y,x) `notElem` sDoubles, (x,y) `notElem` sEdges ]
    mapM_ (\(x,y) -> edge (show x) (show y) [style dashed, Dir Both] ) nDoubles
    let nEdges = [ (x,y) | x <- agentsOf n, y <- IntSet.toList (n `at` x), x /= y, (x,y) `notElem` sDoubles, (y,x) `notElem` sDoubles, (x,y) `notElem` nDoubles, (y,x) `notElem` nDoubles, (x,y) `notElem` sEdges ]
    mapM_ (\(x,y) -> edge (show x) (show y) [style dashed] ) nEdges

showCall :: (Agent,Agent) -> String
showCall (x,y) = show x ++ show y

showCallShort :: (Agent,Agent) -> String
showCallShort (x,y) = [ ['a' ..] !! x, ['a'..] !! y ]

-- | Draw an execution tree with epistemic edges, using GraphViz.
-- The arguments are:
-- - agents for which the epistemic relation shoule be drawn
-- - maximum history length to be shown
-- - history length until which the nodes should be ranked on the same level
-- - the execution tree, generated with tree or norepTree
dotTreeWith :: [Agent] -> Int -> Int -> Protocol -> ExecutionTree -> GenGV.DotGraph String
dotTreeWith drawAgents showLimit rankLimit proto tpc@(Node (g,_) _) =
  GenGV.DotGraph { GenGV.strictGraph = False
                 , GenGV.directedGraph = True
                 , GenGV.graphID = Just (Str $ pack "G")
                 , GenGV.graphStatements = Seq.fromList $ stmtLoop tpc ++ stmtRanks } where
    myNodeID (_,hist) = ppSequence hist
    stmtLoop :: ExecutionTree -> [GenGV.DotStatement String]
    stmtLoop (Node n cts) = concat
      [ [ GenGV.SG $ GenGV.DotSG { GenGV.isCluster = False
                                 , GenGV.subGraphID = Just (Str (pack $ "subgraph-" ++ myNodeID n))
                                 , GenGV.subGraphStmts = Seq.fromList $ stmtLoop t }
        | (_,t@(Node (_,nexthist) _)) <- take 100 cts, length nexthist <= showLimit ]
      , [ GenGV.DN $ DotNode (myNodeID n) [toLabel (ppGraphShort (currentGraph n))] ]
      , map GenGV.DE $
            [ DotEdge (myNodeID n) (myNodeID n') [toLabel (showCallShort c)] | (c,Node n'@(_,nexthist) _) <- take 100 cts, length nexthist <= showLimit ] -- calls arrows
        ++  [ DotEdge (myNodeID n) (myNodeID n') [toLabel (['a'..] !! a), Dir NoDir, Style [SItem Dashed []]] -- epistemic edges
            | a <- agentsOf (fst n), n' <- epistAlt a proto n, n < n', a `elem` drawAgents ]
      ]
    stmtRanks :: [GenGV.DotStatement String]
    stmtRanks = concat [ rankTheSame [(g,h) | h <- hs] | hs <- groupedSequences ] where
      groupedSequences = groupBy ((==) `on` length) . sortBy (compare `on` length) $ allSequences
      allSequences = filter ((<= showLimit) . length) $ filter ((<= rankLimit) . length) $ sequencesOf tpc
      sequencesOf :: ExecutionTree -> [Sequence]
      sequencesOf (Node _ cts) = [] : [ c:h | (c, tpc') <- take 100 cts, h <- sequencesOf tpc' ]
      rankTheSame :: [State] -> [GenGV.DotStatement String]
      rankTheSame ns = [ GenGV.SG  GenGV.DotSG  { GenGV.isCluster = False
                                                , GenGV.subGraphID = Just (Str (pack $ "ranking-" ++ show (length (snd $ head ns))))
                                                , GenGV.subGraphStmts = Seq.fromList $
                                                        GenGV.GA (GraphAttrs [Rank SameRank]) :
                                                        [ GenGV.DN $ DotNode (myNodeID n') [] | n' <- ns ]
                                                } ]

dispTreeWith :: [Agent] -> Int -> Int -> Protocol -> ExecutionTree -> IO ()
dispTreeWith drawAgents showLimit rankLimit proto t = dispDot (drawAgents,showLimit,rankLimit,proto,t)

instance DotAble ([Agent],Int,Int,Protocol,ExecutionTree) where
  dot (drawAgents,showLimit,rankLimit,proto,t) = dotTreeWith drawAgents showLimit rankLimit proto t

-- | By default we show no epistemic edges, show up to 10 calls, rank the first 2 steps and consider lns
instance DotAble ExecutionTree where
  dot = dotTreeWith [] 10 2 lns

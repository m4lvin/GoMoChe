module Gossip.Caas where

import Gossip
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap

lonelyAgents :: Graph -> [Agent]
lonelyAgents (nRel,_) = filter isUnreached oblivious where
  oblivious = IntMap.keys $ IntMap.filter (\ys -> IntSet.size ys == 1) nRel
  isUnreached y = all (\ys -> y `IntSet.notMember` ys) (IntMap.delete y nRel)

data Rel = Num | Sec

edges :: Rel -> Graph -> [(Agent,Agent)]
edges Num (nRel,sRel) = [ (x,y) | (x,ySet) <- IntMap.toList nRel
                                , y <- IntSet.toList ySet
                                , y `IntSet.notMember` (sRel IntMap.! x) ]
edges Sec (_   ,sRel) = [ (x,y) | (x,ySet) <- IntMap.toList sRel
                                , y <- IntSet.toList ySet
                                , x /= y ]

minus :: Graph -> (Rel,Agent,Agent) -> Graph
minus (nRel,sRel) (Num,x,y) = (IntMap.adjust (IntSet.delete y) x nRel, sRel)
minus (nRel,sRel) (Sec,x,y) = (IntMap.adjust (IntSet.delete y) x nRel, IntMap.adjust (IntSet.delete y) x sRel)

plus :: Graph -> (Rel,Agent,Agent) -> Graph
plus (nRel,sRel) (Num,x,y) = (IntMap.adjust (IntSet.insert y) x nRel, sRel)
plus _           (Sec,_,_) = undefined

plusAgentWith :: Graph -> Agent -> [Agent] -> Graph
plusAgentWith (nRel,sRel) x nums =
  ( IntMap.insert x (IntSet.fromList nums) nRel
  , IntMap.insert x (IntSet.singleton x) sRel )

subGraphWith :: Graph -> [Agent] -> Graph
subGraphWith (nRel,sRel) ys = (fix nRel, fix sRel) where
  subset = IntSet.fromList ys
  fix r = IntMap.map (IntSet.intersection subset) $ IntMap.filterWithKey (\k _ -> k `IntSet.member` subset) r

isSubGraphOf :: Graph -> Graph -> Bool
isSubGraphOf (nRelA,sRelA) (nRelB,sRelB) = (nRelA `isSubRelOf` nRelB) && (sRelA `isSubRelOf` sRelB)

isSubRelOf :: Relation -> Relation -> Bool
isSubRelOf relA relB = IntMap.foldrWithKey' (\x ys b ->  b && ys `IntSet.isSubsetOf` (relB IntMap.! x)) True relA

graphWithoutUnsafe :: Graph -> Agent -> Graph
graphWithoutUnsafe (nRel,sRel) x = (IntMap.delete x nRel, IntMap.delete x sRel)

-- Construct a graph by induction:
construct :: Graph -> (Graph,Sequence)
construct g0 = construct' (maximum (agentsOf g0) + 1) g0 where
  construct' nextFreshAg g = case (lonelyAgents g, edges Num g, edges Sec g) of
    -- 0. Base Case: Done.
    ([],[],[]) -> (g,[])
    -- 1. one disconnected agent more
    (l:_,_,_) -> (newg,plan) where
      (oldg,plan) = construct' nextFreshAg (graphWithoutUnsafe g l)
      newg = plusAgentWith oldg l [l]
    -- 2. one N \ S edge more
    ([],(a,b):_,_) -> (newg,newplan) where
      (oldg,oldplan) = construct' (nextFreshAg+1) (g `minus` (Num,a,b))
      c = nextFreshAg
      newg = plusAgentWith oldg c [c,a,b]
      newplan = oldplan ++ [(c,a)]
    -- 3. one S edge more
    ([],[],(a,b):_) -> (newg,newplan) where
      (oldg,oldplan) = construct' (nextFreshAg+1) (g `minus` (Sec,a,b))
      c = nextFreshAg
      newg = plusAgentWith oldg c [c,b] `plus` (Num,a,c)
      newplan = [(c,b)] ++ oldplan ++ [(a,c)]

verboseCaasTest :: Graph -> IO ()
verboseCaasTest g = do
  putStr "Goal: "
  print g
  let (start,plan) = construct g
  putStrLn "Start and Plan:"
  print start
  print plan
  let result = calls start plan
  putStr "Result: "
  print result
  let subresult = subGraphWith result (agentsOf g)
  putStr "Subgraph: "
  print subresult
  putStr "Did it work? "
  print (g == subresult)

worksFor :: Graph -> Bool
worksFor g =
  let
    (start,plan) = construct g
    result = calls start plan
    subresult = subGraphWith result (agentsOf g)
  in
    g == subresult && isInitial start

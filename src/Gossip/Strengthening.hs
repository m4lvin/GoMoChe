module Gossip.Strengthening where

import Control.Monad
import Data.List

import Gossip.LocalProto
import Gossip.General

type Strengthening = Protocol -> Protocol

-- | Syntactic strengthenings: ◾ ◆ ◽ ◇
strengHard, strengSoft, strengStepHard, strengStepSoft :: Strengthening
strengHard     p (a,b) = Conj [ p (a,b) , K    a p $ Box (Call a b) (Dia (protoTerm p) allExperts) ]
strengSoft     p (a,b) = Conj [ p (a,b) , HatK a p $ Box (Call a b) (Dia (protoTerm p) allExperts) ]
strengStepHard p (a,b) = Conj [ p (a,b) , K    a p $ Box (Call a b) (Disj [allExperts, protoCanGoOn p]) ]
strengStepSoft p (a,b) = Conj [ p (a,b) , HatK a p $ Box (Call a b) (Disj [allExperts, protoCanGoOn p]) ]

statistics :: Protocol -> State -> (Int,Int)
statistics proto (g,sigma) =
  (length succSequ, length sequ - length succSequ) where
    sequ = sequences proto (g,sigma) \\ [[]]
    succSequ = filter (isSuccSequence (g,sigma)) sequ

strengthenEnough :: Int -> Strengthening -> Protocol -> State -> IO ()
strengthenEnough k streng proto state = do
  let (suc,unsuc) = statistics proto state
  putStrLn $ show k ++ " " ++ ppState state ++ "\t" ++ show (suc,unsuc)
  when (suc > 0 && unsuc > 0) $ do
    putStr "."
    let newproto = streng proto
    strengthenEnough (k+1) streng newproto state

-- strengthenEnough statistics for all graphs with k agents
allStatistics :: Int -> IO ()
allStatistics k =
  mapM_
    (\(str,streng) -> do
      putStrLn $ "\n=====" ++ str ++ "=====";
      mapM_
        (\g -> strengthenEnough 0 streng lns (g, []))
        (solvableInits localLns k)
    )
    [ ("stepSoft"       , strengStepSoft )
    , ("stepHard"       , strengStepHard )
    , ("soft"           , strengSoft     )
    , ("hard"           , strengHard     )
    ]

diamondProto :: Protocol
diamondProto (a,b) = K a lns $ Conj [ lns (a,b), Disj [clause1,clause2a,clause2b,clause3] ] where
  noCallsMade = ForallAg (\i -> ForallAg (\j -> if i == j then Top else Neg $ S i j))
  oneCallMade = ExistsAg (\i -> ExistsAg (\j -> Conj [
    S i j, S j i, ForallAg (\k -> if k `elem` [i,j] then Top else knowsOnlyOwn k)
    ]))
  clause1 = Conj [knowsOnlyOwn a, Disj [noCallsMade, oneCallMade]]
  clause2a = ExistsAg (\k -> ExistsAg (\l ->
    if k /= l && all (`notElem` [a,b]) [k,l] then Conj [S a k, S a l] else Bot))
  clause2b = ForallAg (\k -> ExistsAg (\l -> if k /= l then S k l else Bot))
  clause3 = expert b

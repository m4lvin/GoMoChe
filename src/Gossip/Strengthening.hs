module Gossip.Strengthening where

import Control.Monad
import Data.List

import Gossip
import Gossip.LocalProto
import Gossip.General

type Strengthening = Int -> Protocol -> Protocol

-- | Syntactic strengthenings
strengHard, strengSoft, strengStep :: Strengthening
strengHard k f (a,b) = Conj [ f (a,b) , K    a $ Box (Call a b) (Dia (protoTerm k f) (allExperts k)) ]
strengSoft k f (a,b) = Conj [ f (a,b) , HatK a $ Box (Call a b) (Dia (protoTerm k f) (allExperts k)) ]
strengStep k f (a,b) = Conj [ f (a,b) , HatK a $ Box (Call a b) (Disj [allExperts k, protoCanGoOn k f]) ]

-- | Syntactic strenghtenings with explicit protocol in K operator
strengHardExp, strengSoftExp, strengStepExp :: Strengthening
strengHardExp k f (a,b) = Conj [ f (a,b) , Kp    f a $ Box (Call a b) (Dia (protoTerm k f) (allExperts k)) ]
strengSoftExp k f (a,b) = Conj [ f (a,b) , HatKp f a $ Box (Call a b) (Dia (protoTerm k f) (allExperts k)) ]
strengStepExp k f (a,b) = Conj [ f (a,b) , HatKp f a $ Box (Call a b) (Disj [allExperts k, protoCanGoOn k f]) ]

-- | Selfreferential strengthenings
selfrefHard, selfrefSoft, selfrefStep :: Strengthening
selfrefHard k f (a,b) = Conj [ f (a,b) , Kp    (selfrefStep k f) a $ Box (Call a b) (Dia (protoTerm k f) (allExperts k)) ]
selfrefSoft k f (a,b) = Conj [ f (a,b) , HatKp (selfrefStep k f) a $ Box (Call a b) (Dia (protoTerm k f) (allExperts k)) ]
selfrefStep k f (a,b) = Conj [ f (a,b) , HatKp (selfrefStep k f) a $ Box (Call a b) (Disj [allExperts k, protoCanGoOn k f]) ]

statistics :: Protocol -> GossipModel -> Point -> (Int,Int)
statistics proto gomo (g,sigma) =
  (length succSequ, length sequ - length succSequ) where
    sequ = sequences gomo (g,sigma) proto \\ [[]]
    succSequ = filter (isSuccSequence (g,sigma)) sequ

strengthenEnough :: Int -> Strengthening -> Protocol -> GossipModel -> Point -> IO ()
strengthenEnough k streng proto gomo point = do
  let (suc,unsuc) = statistics proto gomo point
  putStrLn $ show k ++ " " ++ ppPoint point ++ "\t" ++ show (suc,unsuc)
  when (suc > 0 && unsuc > 0) $ do
    putStr "."
    let newproto = streng (length $ agentsOf (fst point)) proto
    let newgomo = gomo {name = name gomo ++ "+", protoCK = proto}
    strengthenEnough (k+1) streng newproto newgomo point

-- Statistics about all graphs for k agents, using LNS and its thinkDifferent strengthening --
allStatistics :: Int -> IO ()
allStatistics k =
  mapM_
    (\(str,streng) -> do
      putStrLn $ "\n=====" ++ str ++ "=====";
      mapM_
        (\g -> strengthenEnough 0 streng lns anyCK (g, []))
        (solvableInits localLns k)
    )
    [ ("hard"       , strengHard   )
    , ("soft"       , strengSoft   )
    , ("step"       , strengStep   )
    , ("hardExp"    , strengHardExp)
    , ("softExp"    , strengSoftExp)
    , ("stepExp"    , strengStepExp)
    , ("selfrefHard", selfrefHard  )
    , ("selfrefSoft", selfrefSoft  )
    , ("selfrefStep", selfrefStep  )
    ]

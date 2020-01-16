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

-- count the number of (successful, not successful) sequences
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

diamondProtoOld :: Protocol
diamondProtoOld (a,b) = K a lns $ Conj [ lns (a,b), Disj [clause1,clause2a,clause2b,clause3] ] where
  noCallsMade = ForallAg (\i -> forallAgWith (/= i) (Neg . S i))
  oneCallMade = ExistsAg (\i -> ExistsAg (\j -> Conj [ S i j, S j i, forallAgWith (`notElem` [i,j]) knowsOnlyOwn ]))
  clause1 = Conj [knowsOnlyOwn a, Disj [noCallsMade, oneCallMade]]
  clause2a = ExistsAg (\k -> existsAgWith (\l -> k /= l && all (`notElem` [a,b]) [k,l]) (\l -> Conj [S a k, S a l]) )
  clause2b = ForallAg (\k -> existsAgWith (/= k) (S k))
  clause3  = expert b

diamondProto :: Protocol
diamondProto (i,j) = K i anyCall $ Disj [noCallsMade,clause2,clause3,clause4,clause5] where
  noCallsMade = ForallAg (\k -> forallAgWith (/= k) (Neg . S k))
  oneCallMade = ExistsAg (\k -> existsAgWith (/= k) (\l ->
                  Conj [ S k l, S l k, forallAgWith (`notElem` [k,l]) knowsOnlyOwn ]))
  clause2 = Conj [oneCallMade, knowsOnlyOwn i]
  clause3 = Conj
    [ Neg $ S i j
    , Disj [ Conj [ existsAgWith (/= i) (\k ->
                      existsAgWith (`notElem` [i,k]) (\l -> Conj [ S i k, S i l ] ) )
                  , forallAgWith (/= i) (\k ->
                      S k i `Impl` forallAgWith (`notElem` [i,k]) (\l -> Neg $ S l i)) ]
           , Conj [ K i lns $ ForallAg (\k -> existsAgWith (/= k) (\l ->
                      Conj [ S k l, forallAgWith (`notElem` [k,l]) (Neg . S k) ] ) )
                  , ForallAg (\k -> N k i `Impl` S k i) ] ] ]
  clause4 = Conj [ Neg $ S i j, HatK i lns (ExistsAg expert)
                 , Neg $ existsAgWith (/= i) (\k -> existsAgWith (`notElem` [i,k]) (\l -> Conj [ S i k , S i l]))
                 , ForallAg (\k -> N k i `Impl` S k i)]
  clause5 = Conj [ Neg $ S i j
                 , HatK i lns (forallAgWith (/= i) expert) ]

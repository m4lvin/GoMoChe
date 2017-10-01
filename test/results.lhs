

\begin{code}
module Main where

import Gossip
import Gossip.Examples
import Gossip.General
import Gossip.Random
import Gossip.Strengthening
import Gossip.Tree
import Test.Hspec
import Test.QuickCheck

main :: IO ()
main = hspec $ do
  describe "general randomized checks" $
    it "epistAlt is an equivalence relation" $
      property $ \(ArbPA (p,i)) -> checkEpistAlt i anyCK p

  describe "concrete examples" $ do
    it "hard lns is empty on lemmaExample after (0,2)" $
      tree lnsCK (lemmaExample,[(0,2)]) (strengHard 6 lns) `shouldBe` Node (lemmaExample,[(0,2)]) []

    describe "statistics for diamondExample with lnsCK" $ do
      it "LNS:  (48,44)" $ statistics lns                lnsCK (diamondExample,[]) `shouldBe` (48,44)
      it "LNS!  (48,36)" $ statistics (strengStep 4 lns) lnsCK (diamondExample,[]) `shouldBe` (48,36)
      it "LNS+^ (48, 8)" $ statistics (strengSoft 4 lns) lnsCK (diamondExample,[]) `shouldBe` (48,8)
      it "LNS+  ( 8, 8)" $ statistics (strengHard 4 lns) lnsCK (diamondExample,[]) `shouldBe` (8,8)

  describe "prettyprinting and visualization" $ do
    it "parseState . ppState == id" $
      property $ \(ArbIS s) -> (parseState (ppState s) == s)
    it "ppState preserves == on initial graphs" $
      property $ \(ArbIS s) (ArbIS t) -> (ppState s == ppState t) == (s == t)
    it "ppState preserves == on points after some calls" $
      property $ \(ArbPA ((s1,sequ1),_)) (ArbPA ((s2,sequ2),_))
        -> (ppState (calls s1 sequ1) == ppState (calls s2 sequ2))
        == (calls s1 sequ1 == calls s2 sequ2)

-- | check that epistAlt describes a reflexive, transitive, symmetric relations
checkEpistAlt :: Agent -> GossipModel -> Point -> Bool
checkEpistAlt a gomo here = reflexive && transitive && symmetric where
  reachables = epistAlt a gomo here
  reflexive = here `elem` reachables
  transitive = all (`elem` reachables) $ concatMap (epistAlt a gomo) reachables
  symmetric = all (elem here) (map (epistAlt a gomo) reachables)

\end{code}

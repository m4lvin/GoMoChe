module Main where

import Control.Exception (evaluate,try,IOException)
import Data.List (nub)
import System.IO.Silently
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Gossip
import Gossip.Caas
import Gossip.Examples
import Gossip.General
import Gossip.LocalProto
import Gossip.Random
import Gossip.Internal
import Gossip.Strengthening
import Gossip.Tree

main :: IO ()
main = hspec $ parallel $ do
  describe "internal functions" $ do
    mapM_ (\n -> it ("length (allInits n) == (2^(n^2) - n)  for n = " ++ show n) $
        length (allInits n) `shouldBe` (2^(n^(2::Integer) - n)) ) [2..5]
    mapM_ (\n -> it ("lineInit and totalInit are in allInits  for n = " ++ show n) $
        lineInit n `elem` allInits n && totalInit n `elem` allInits n) [2..5]
    prop "parseGraph . ppGraph == id" $
      \(ArbIGG g) -> parseGraph (ppGraph g) === g
    prop "ppGraph preserves == on initial graphs" $
      \(ArbIGG g) (ArbIGG h) -> (ppGraph g == ppGraph h) === (g == h)
    prop "ppGraph preserves == on points after some calls" $
      \(ArbPA ((s1,sequ1),_)) (ArbPA ((s2,sequ2),_))
        ->  (ppGraph (calls s1 sequ1) == ppGraph (calls s2 sequ2))
            === (calls s1 sequ1 == calls s2 sequ2)
    prop "ppGraphShort preserves == on initial graphs" $
      \(ArbIGG g) (ArbIGG h) -> (ppGraphShort g == ppGraphShort h) === (g == h)
    it "splitWhere ':' \"x:y\" == [\"x\",\"y\"]" $
      splitWhere ':' "x:y" `shouldBe` ["x","y"]
    it "impossible call should throw an exception" $
      evaluate (call (lineInit 3) (2,1)) `shouldThrow` anyException
    prop "agentsOf agrees on graph and tree" $
      \(ArbIGG g) -> agentsOf g === agentsOf (localTree localLns (g,[]))
    prop "statistics == sumTree . tree" $
      \(ArbIGG g) -> length (sequences lns (g,[])) > 1 ==> statistics lns (g,[]) === sumTree (tree lns (g,[]))
    prop "trees equal iff sequencess equal" $
      \(ArbIGG g) (ArbIGG h) -> (tree lns (g,[]) == tree lns (h,[])) === (sequences lns (g,[]) == sequences lns (h,[]))
    prop "trees equal iff (show.tree)s equal" $
      \(ArbIGG g) (ArbIGG h) -> (tree lns (g,[]) == tree lns (h,[])) === (show (tree lns (g,[])) == show (tree lns (h,[])))
    it "allStatistics 3 throws no IO exception" $
      (try (silence $ allStatistics 3) :: IO (Either IOException ())) `shouldReturn` Right ()
    it "showTreeUpToDecision threeExample throws no IO exception" $
      (try (silence . showTreeUpToDecision . tree lns $ (threeExample,[])) :: IO (Either IOException ())) `shouldReturn` Right ()
    it "showTreeUpTo spaceshipExample throws no IO exception" $
      (try (silence . showTreeUpTo 5 . tree lns $ (spaceshipExample,[])) :: IO (Either IOException ())) `shouldReturn` Right ()

  describe "CAAS" $ do
    prop "works for initial graphs" $
      \(ArbIGG g) -> worksFor g
    prop "works for reachable graphs" $
      \(ArbPA ((ginit,sequ),_)) -> worksFor $ calls ginit sequ
    -- prop "works for reachable graphs" $
    --   \(ArbGG g) -> worksFor g -- TODO needs ArbGG (non-initial, non-reachable!)

  describe "general randomized checks" $ do
    prop "localAnyCall == allowedCalls anyCall" $
      \(ArbIGG g) -> localAnyCall g == allowedCalls anyCall (g,[])
    prop "localNoCall == allowedCalls noCall" $
      \(ArbIGG g) -> localNoCall g == allowedCalls noCall (g,[])
    prop "localLns == allowedCalls lns" $
      \(ArbIGG g) -> localLns g == allowedCalls lns (g,[])
    prop "localSequences localLns === sequences lns" $
      \(ArbIGG g) -> localSequences localLns g === sequences lns (g,[])
    prop "localTree localLns === tree lns" $
      \(ArbIGG g) -> localTree localLns (g,[]) === tree lns (g,[])
    prop "isWeaklySucc localLns iff isWeaklySuccForm lns" $
      \(ArbIGG g) -> isWeaklySucc localLns g === eval (g,[]) (isWeaklySuccForm lns)
    prop "isStronglySucc localLns iff isStronglySuccForm lns" $
      \(ArbIGG g) -> isStronglySucc localLns g === eval (g,[]) (isStronglySuccForm lns)
    prop "isStronglyUnsucc localLns iff isStronglyUnsuccForm lns" $
      \(ArbIGG g) -> isStronglyUnsucc localLns g === eval (g,[]) (isStronglyUnsuccForm lns)
    prop "epistAlt with LNS is an equivalence relation" $
      \(ArbPA (p,i)) -> checkEpistAlt i lns p `shouldBe` [True,True,True]

  describe "concrete examples" $ do
    describe "isWeaklySucc localLns" $ do
      it "threeExample"     $ isWeaklySucc localLns threeExample
      it "easyExample"      $ isWeaklySucc localLns easyExample
      it "squareExample"    $ isWeaklySucc localLns squareExample
      it "spaceshipExample" $ isWeaklySucc localLns spaceshipExample
      it "nExample"         $ isWeaklySucc localLns nExample
      it "diamondExample"   $ isWeaklySucc localLns diamondExample
      it "lemmaExample"     $ isWeaklySucc localLns lemmaExample
      it "triangleExample"  $ isWeaklySucc localLns triangleExample

    describe "nExample" $ do
      it "LNS◇◇◇◇◇ (4,8)" $ statistics (finiteIterate 5 strengStepSoft lns) (nExample,[]) `shouldBe` (4,8)
      it "LNS◽◽◽◽  (0,0)" $ statistics (finiteIterate 4 strengStepHard lns) (nExample,[]) `shouldBe` (0,0)
      it "LNS◆ == LNS◆◆"  $ let fn k = sequences (finiteIterate k strengSoft lns) (nExample,[]) in fn 1 `shouldBe` fn 2

    describe "diamondExample" $ do
      it "LNS      (48,44)" $ statistics lns                                  (diamondExample,[]) `shouldBe` (48,44)
      it "LNS◾     ( 8, 8)" $ statistics (strengHard lns)                     (diamondExample,[]) `shouldBe` ( 8, 8)
      it "LNS◾◽    ( 8, 4)" $ statistics (strengStepHard $ strengHard lns)    (diamondExample,[]) `shouldBe` ( 8, 4)
      it "LNS◾◾    ( 0, 4)" $ statistics (finiteIterate 2 strengHard lns)     (diamondExample,[]) `shouldBe` ( 0, 4)
      it "LNS◾◾◾   ( 0, 0)" $ statistics (finiteIterate 3 strengHard lns)     (diamondExample,[]) `shouldBe` ( 0, 0)
      it "LNS◆     (48, 8)" $ statistics (strengSoft lns)                     (diamondExample,[]) `shouldBe` (48, 8)
      it "LNS◆◆    (48, 8)" $ statistics (strengSoft $ strengSoft lns)        (diamondExample,[]) `shouldBe` (48, 8)
      it "LNS◆ == LNS◆◆"    $ let fn k = sequences (finiteIterate k strengSoft lns) (diamondExample,[]) in fn 1 `shouldBe` fn 2
      it "LNS◽     (24,36)" $ statistics (strengStepHard lns)                 (diamondExample,[]) `shouldBe` (24,36)
      it "LNS◽◽    ( 8,16)" $ statistics (finiteIterate 2 strengStepHard lns) (diamondExample,[]) `shouldBe` ( 8,16)
      it "LNS◽◽◽   ( 8, 4)" $ statistics (finiteIterate 3 strengStepHard lns) (diamondExample,[]) `shouldBe` ( 8, 4)
      it "LNS◽◽◽◽  ( 0, 4)" $ statistics (finiteIterate 4 strengStepHard lns) (diamondExample,[]) `shouldBe` ( 0, 4)
      it "LNS◽◽◽◽◽ ( 0, 0)" $ statistics (finiteIterate 5 strengStepHard lns) (diamondExample,[]) `shouldBe` ( 0, 0)
      it "LNS◇     (48,36)" $ statistics (strengStepSoft lns)                 (diamondExample,[]) `shouldBe` (48,36)
      it "LNS◇◇    (48,32)" $ statistics (finiteIterate 2 strengStepSoft lns) (diamondExample,[]) `shouldBe` (48,32)
      it "LNS◇◇◇   (48,32)" $ statistics (finiteIterate 3 strengStepSoft lns) (diamondExample,[]) `shouldBe` (48,32)
      it "LNS◇◇ == LNS◇◇◇"  $ let fn k = sequences (finiteIterate k strengStepSoft lns) (diamondExample,[]) in fn 2 `shouldBe` fn 3
      it "LNS◇◽◽◽  (16, 0)" $ statistics (finiteIterate 3 strengStepHard $ strengStepSoft lns) (diamondExample,[]) `shouldBe` (16,0)
      it "LNS◇◽◾   (16, 0)" $ statistics (strengHard $ strengStepHard $ strengStepSoft lns)    (diamondExample,[]) `shouldBe` (16,0)
      it "diamondProtoOld (32,0)" $ statistics diamondProtoOld (diamondExample,[]) `shouldBe` (32,0)
      it "diamondProto (8,0)" $ statistics diamondProto (diamondExample,[]) `shouldBe` (8,0)
      it "LNS◾◾ ≠ LNS◾" $ sequences (strengHard $ strengHard lns) (diamondExample,[]) `shouldNotBe` sequences (strengHard lns) (diamondExample,[])
      it "diamondSolvers are successful" $ all (isSuccSequence (diamondExample,[])) diamondSolvers `shouldBe` True
      it "diamondSolvers = diamondProto" $ diamondSolvers `shouldBe` sequences diamondProto (diamondExample,[])

    describe "lemmaExample" $
      it "hard lns is empty on lemmaExample after (0,2)" $
        tree (strengHard lns) (lemmaExample,[(0,2)]) `shouldBe` Node (lemmaExample,[(0,2)]) []

  describe "refuted conjectures" $ do
    it "LNS◾ ⊆ LNS◽◽  refuted by  03-012-2-23 I4" $
      let g = parseGraph "03-012-2-23 I4" in
        sequences (strengHard lns) (g,[]) `shouldNotSatisfy` all (`prefixElem` sequences (strengStepHard $ strengStepHard lns) (g,[]))
    it "LNS◾ ⊆ LNS◾◽  refuted by  diamondExample" $
      let g = diamondExample in
        sequences (strengHard lns) (g,[]) `shouldNotSatisfy` all (`prefixElem` sequences (strengStepHard $ strengHard lns) (g,[]))

  describe "conjectures" $ do
    prop "??? LNS◾ ⊆ LNS◽" $
      \(ArbIGG g) ->
        sequences (strengHard lns) (g,[]) `shouldSatisfy` all (`prefixElem` sequences (strengStepHard lns) (g,[]))
    prop "??? LNS◆ ⊆ LNS◇" $
      \(ArbIGG g) ->
        sequences (strengSoft lns) (g,[]) `shouldSatisfy` all (`prefixElem` sequences (strengStepSoft lns) (g,[]))
    prop "??? LNS◆ ⊆ LNS◇◇" $
      \(ArbIGG g) ->
        sequences (strengSoft lns) (g,[]) `shouldSatisfy` all (`prefixElem` sequences (strengStepSoft $ strengStepSoft lns) (g,[]))
    prop "??? LNS◆ ⊆ LNS◇◇◇" $
      \(ArbIGG g) ->
        sequences (strengSoft lns) (g,[]) `shouldSatisfy` all (`prefixElem` sequences (strengStepSoft $ strengStepSoft $ strengStepSoft lns) (g,[]))
    prop "??? LNS◆ == LNS◆◇" $
      \(ArbIGG g) ->
        sequences (strengSoft lns) (g,[]) == sequences (strengStepSoft $ strengSoft lns) (g,[])

  describe "Uniform Backward Defoliation (this will take a while)" $ do
    prop "hardUBD === strengStepHard" $
      \(ArbIGG g) -> hardUBD lns (tree lns (g,[])) === tree (strengStepHard lns) (g,[])
    prop "hardUBD . hardUBD === strengStepHard . strengStepHard" $
      \(ArbIGG g) -> hardUBD lns (hardUBD lns (tree lns (g,[]))) === tree (strengStepHard $ strengStepHard lns) (g,[])
    prop "softUBD === strengStepSoft" $
      \(ArbIGG g) -> softUBD lns (tree lns (g,[])) === tree (strengStepSoft lns) (g,[])
    prop "softUBD . softUBD === strengStepSoft . strengStepSoft" $
      \(ArbIGG g) -> softUBD lns (softUBD lns (tree lns (g,[]))) === tree (strengStepSoft $ strengStepSoft lns) (g,[])

  describe "e2 examples" $ do
    it "CMO super after ab;cd is super succ" $
      (totalInit 4, [(0,1),(2,3)]) |= isStronglySuperSuccForm cmo (super cmo)
    it "CMO super after ab;cd always has 3 calls left" $
      nub (map length $ sequences (super cmo) (totalInit 4, [(0,1),(2,3)])) `shouldBe` [3]
    it "CMO super after ab;bc is not strongly super succ" $
      (totalInit 4, [(0,1),(1,2)]) |= Neg (isStronglySuperSuccForm cmo (super cmo))
    it "CMO super after ab;bc can continue with 4 or 3 calls" $
      nub (map length $ sequences (super cmo) (totalInit 4, [(0,1),(1,2)])) `shouldBe` [4,3]


-- | Check that epistAlt describes a (in proto) reflexive, transitive, (in proto) symmetric relation.
checkEpistAlt :: Agent -> Protocol -> State -> [Bool]
checkEpistAlt i proto here@(g, sigma)  = [reflexive, transitive, symmetric] where
  reachables = epistAlt i proto here
  inProtocol = isSequenceOf proto (g, []) sigma
  reflexive = not inProtocol || (here `elem` reachables)
  transitive = all (all (`elem` reachables) . epistAlt i proto) reachables
  symmetric = not inProtocol || all (elem here . epistAlt i proto) reachables

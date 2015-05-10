{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Context where

import Control.DeepSeq
import Data.Array.IArray
import Data.Array.Unboxed
import Data.Bits
import Data.List as List (map, null)
import Data.Map as Map (Map, map, mapKeys, toList, fromList)
import Data.Set as Set (Set, fromList)
import Language.Haskell.TH
import Language.Haskell.TH.Context (reifyInstancesWithContext, runContext)
import Language.Haskell.TH.Context.Simple (missingInstances, simpleMissingInstanceTest)
import Language.Haskell.TH.TypeGraph.Expand (expandType, runExpanded)
import Language.Haskell.TH.TypeGraph.Core (pprint')
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Syntax (Lift(lift), Quasi(qReifyInstances))
import System.Exit (ExitCode)
import Test.Hspec hiding (runIO)
import Test.Hspec.Core.Spec (SpecM)

import Common
import Values

tests :: SpecM () ()
tests = do
  it "can run the Q monad" $ do
     typ <- runQ [t|Int|]
     typ `shouldBe` ConT ''Int

  -- String becomes [Char], Maybe String becomes Maybe [Char], Maybe (Maybe String) becomes Maybe (Maybe [Char])
  it "expands types as expected" $ do
     (expected :: [Type]) <- runQ (sequence [ [t| [Char] |], [t|Maybe [Char] |], [t|Maybe (Maybe [Char])|] ])
     let expanded = $(withLocalDeclarations [] (do types <- runQ (sequence [ [t|String|], [t|Maybe String|], [t|Maybe (Maybe String)|] ]) >>= mapM expandType
                                                   runQ . lift $ (List.map runExpanded types)))
     expanded `shouldBe` expected

  -- Test the behavior of th-reify-many
  it "can tell that there is an instance NFData Char" $
     $(do insts <- qReifyInstances ''NFData [ConT ''Char]
          lift $ List.map pprint' insts) `shouldBe` (["instance Control.DeepSeq.NFData GHC.Types.Char"] :: [String])

  it "can tell that there is no instance NFData ExitCode" $
     $(do insts <- qReifyInstances ''NFData [ConT ''ExitCode]
          lift $ List.map pprint' insts) `shouldBe` ([] :: [String])

  it "can tell that an instance hasn't been declared" $
     $(missingInstances simpleMissingInstanceTest [d|instance NFData ExitCode|] >>= lift . List.null)
          `shouldBe` False

  it "can tell that an instance has been declared" $
     $(missingInstances simpleMissingInstanceTest [d|instance NFData Char|] >>= lift . List.null)
          `shouldBe` True

-- GHCs older than 7.10 that haven't been specially patched cannot deal with
-- the unbound type variable a.
#if __GLASGOW_HASKELL__ >= 709 || defined(PATCHED_FOR_TRAC_9262)
  -- Doesn't actually use any th-context functions, but it tests
  -- for trac 9262.
  it "Is using a ghc without bug https://ghc.haskell.org/trac/ghc/ticket/9262 (i.e. either 7.10 or a custom patched ghc)" $ do
     $(do insts <- qReifyInstances ''Eq [ListT `AppT` VarT (mkName "a")]
          -- runIO $ putStrLn (pprint insts)
          lift "ok")
         `shouldBe` "ok"

  it "can find all the Bits instances" $ do
     (setDifferences
        (Set.fromList
           $(do insts <- qReifyInstances ''Bits [VarT (mkName "a")]
                lift (List.map pprintDec insts)))
        bitsInstances)
      `shouldBe` noDifferences
{-
  it "can match all the Enum instances" $ do
     (\ (insts, _pairs) -> (setDifferences (Set.fromList insts) enumInstances))
             $(do (insts, mp) <- runContext (reifyInstancesWithContext ''Enum [VarT (mkName "a")])
                  lift (List.map pprintDec insts, Map.toList (Map.map (List.map pprintDec) (Map.mapKeys pprintPred mp))))
          `shouldBe` noDifferences
-}
  it "can handle multi param class IArray" $ do
     (\ (insts, pairs) -> (setDifferences (Set.fromList insts) arrayInstances,
                           Map.map Set.fromList (Map.fromList pairs)))
             -- Unquote the template haskell Q monad expression
             $(do -- Run instances and save the result and the state monad result
                  (insts, mp) <- runContext (reifyInstancesWithContext ''IArray [ConT ''UArray, VarT (mkName "a")])
                  -- Convert to lists of text so we can lift out of Q
                  lift (List.map pprintDec insts, Map.toList (Map.map (List.map pprintDec) (Map.mapKeys pprintPred mp))))
          `shouldBe` (noDifferences,
                      -- I don't think this is right
                      Map.fromList [{-("Data.Array.Base.IArray Data.Array.Base.UArray a", arrayInstances)-}] :: Map String (Set String))
#endif

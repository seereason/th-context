{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Context where

import Control.DeepSeq
import Control.Lens (view)
import Control.Monad.State (evalStateT, runStateT)
import Data.Array.IArray
import Data.Array.Unboxed
import Data.Bits
import Data.List as List (map)
import Data.Map as Map (Map, empty, map, mapKeys, toList, fromList)
import Data.Set as Set (fromList, map, Set)
import Language.Haskell.TH
import Language.Haskell.TH.Context (reifyInstancesWithContext, expandType)
-- import Language.Haskell.TH.Context.S (S(S), instMap)
-- import Language.Haskell.TH.Context.Simple (missingInstances, simpleMissingInstanceTest)
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Syntax (Lift(lift), Quasi(qReifyInstances))
import Language.Haskell.TH.TypeGraph.Expand (E(unE), ExpandMap)
import Language.Haskell.TH.TypeGraph.Prelude (pprint')
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
     let actual = $(withLocalDeclarations [] $ flip evalStateT (Map.empty :: ExpandMap) $
                    do (types :: [Type]) <- runQ (sequence [ [t|String|], [t|Maybe String|], [t|Maybe (Maybe String)|] ]) >>= mapM expandType >>= return . List.map unE
                       runQ . lift $ types)
     actual `shouldBe` expected

  -- Test the behavior of th-reify-many
  it "can tell that there is an instance NFData Char" $
     $(do insts <- qReifyInstances ''NFData [ConT ''Char]
          lift $ List.map pprint' insts) `shouldBe` (["instance Control.DeepSeq.NFData GHC.Types.Char"] :: [String])

  it "can tell that there is no instance NFData ExitCode" $
     $(do insts <- qReifyInstances ''NFData [ConT ''ExitCode]
          lift $ List.map pprint' insts) `shouldBe` ([] :: [String])
{-
  it "can tell that an instance hasn't been declared" $
     $(missingInstances simpleMissingInstanceTest [d|instance NFData ExitCode|] >>= lift . List.null)
          `shouldBe` False

  it "can tell that an instance has been declared" $
     $(missingInstances simpleMissingInstanceTest [d|instance NFData Char|] >>= lift . List.null)
          `shouldBe` True
-}
-- GHCs older than 7.10 that haven't been specially patched cannot deal with
-- the unbound type variable a.
  -- Doesn't actually use any th-context functions, but it tests
  -- for trac 9262.
  it "Is using a ghc without bug https://ghc.haskell.org/trac/ghc/ticket/9262 (i.e. either 7.10 or a custom patched ghc)" $ do
     $(do _insts <- qReifyInstances ''Eq [ListT `AppT` VarT (mkName "a")]
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
                  (insts, s) <- runStateT (reifyInstancesWithContext ''IArray [ConT ''UArray, VarT (mkName "a")]) (S mempty mempty mempty)
                  -- Convert to lists of text so we can lift out of Q
                  lift (List.map pprintDec insts, Map.toList (Map.map (List.map pprintDec') (Map.mapKeys (pprintPred . unE) (view instMap s)))))
          `shouldBe` (noDifferences,
                      -- I don't think this is right
                      Map.fromList [("IArray UArray a", Set.map (\ x -> "Declared (" ++ x ++ ")") arrayInstances)] :: Map String (Set String))

  it "handles a wrapper instance" $
     $(do (insts, s) <- runStateT (reifyInstancesWithContext ''MyClass [AppT (ConT ''Wrapper) (ConT ''Int)]) (S mempty mempty mempty)
          lift (List.map pprintDec insts, Map.toList (Map.map (List.map pprintDec') (Map.mapKeys (pprintPred . unE) (view instMap s)))))
          `shouldBe` (["instance MyClass a => MyClass (Wrapper a)"],
                      [("MyClass (Wrapper Int)",["Declared (instance MyClass a => MyClass (Wrapper a))"]),
                       ("MyClass Int",["Declared (instance MyClass Int)"])])
  it "handles a multi param wrapper instance" $
     $(do (insts, s) <- runStateT (reifyInstancesWithContext ''MyMPClass [VarT (mkName "a"), AppT (ConT ''Wrapper) (ConT ''Int)]) (S mempty mempty mempty)
          lift (List.map pprintDec insts, Map.toList (Map.map (List.map pprintDec') (Map.mapKeys (pprintPred . unE) (view instMap s)))))
          `shouldBe` (["instance MyMPClass a b => MyMPClass a (Wrapper b)"],
                      [("MyMPClass a (Wrapper Int)",["Declared (instance MyMPClass a b => MyMPClass a (Wrapper b))"]),
                       ("MyMPClass a Int",["Declared (instance MyMPClass a Int)"])])

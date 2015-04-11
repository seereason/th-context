{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module TypeGraph where

import Control.Monad (filterM)
import Data.Map as Map (toList)
import Data.Set as Set (Set, fromList, toList, union)
import GHC.Prim -- ByteArray#, Char#, etc
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Context.Expand (expandType, runExpanded, E)
import Language.Haskell.TH.Context.Helpers (pprint', typeArity)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.TypeGraph (typeGraphVertices, typeGraphEdges, VertexStatus(Vertex))
import Test.Hspec hiding (runIO)
import Test.Hspec.Core.Spec (SpecM)

import Common
import Values

tests :: SpecM () ()
tests = do
  it "can find the subtypes of Type" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                  runQ [t|Type|] >>=
                                  expandType >>= \ (typ :: E Type) ->
                                  typeGraphVertices (const $ return Vertex) [typ] >>=
                                  runQ . lift . map (pprintType . runExpanded) . Set.toList)) subtypesOfType
        `shouldBe` noDifferences

  it "can find the edges of the subtype graph of Type" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Type|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                typeGraphEdges (const $ return Vertex) [typ] >>=
                                runQ . lift . edgesToStrings)) typeEdges
        `shouldBe` noDifferences

  it "can find the edges of the subtype graph of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                typeGraphEdges (const $ return Vertex) [typ] >>=
                                runQ . lift . edgesToStrings)) decEdges
        `shouldBe` noDifferences

  it "can find the subtypes of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                typeGraphVertices (const $ return Vertex) [typ] >>=
                                runQ . lift . map (pprintType . runExpanded) . Set.toList)) subtypesOfDec
        `shouldBe` noDifferences

  it "can find the arity 0 subtypes of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                typeGraphVertices (const $ return Vertex) [typ] >>=
                                filterM (\ t -> typeArity (runExpanded t) >>= \ a -> return (a == 0)) . Set.toList >>=
                                runQ . lift . map (pprintType . runExpanded))) arity0SubtypesOfDec
        `shouldBe` noDifferences

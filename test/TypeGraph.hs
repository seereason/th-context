{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module TypeGraph where

import Control.Monad (filterM)
--import Data.Map as Map (toList)
import Data.Set as Set (fromList, toList)
--import GHC.Prim -- ByteArray#, Char#, etc
import Language.Haskell.TH
import Language.Haskell.TH.Context.Expand (expandType, runExpanded')
import Language.Haskell.TH.Context.Helpers (typeArity)
import Language.Haskell.TH.Context.TypeGraph (typeGraphVertices, typeGraphEdges, VertexStatus(Vertex))
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax
import Test.Hspec hiding (runIO)
import Test.Hspec.Core.Spec (SpecM)

import Common
import Values

tests :: SpecM () ()
tests = do
  it "can find the subtypes of Type" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                  runQ [t|Type|] >>=
                                  expandType >>= \typ ->
                                  typeGraphVertices (const $ return Vertex) [runExpanded' typ] >>=
                                  runQ . lift . map pprintType . Set.toList)) subtypesOfType
        `shouldBe` noDifferences

  it "can find the edges of the subtype graph of Type" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Type|] >>=
                                expandType >>= \typ ->
                                typeGraphEdges (const $ return Vertex) [runExpanded' typ] >>=
                                runQ . lift . edgesToStrings)) typeEdges
        `shouldBe` noDifferences

  it "can find the edges of the subtype graph of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \typ ->
                                typeGraphEdges (const $ return Vertex) [runExpanded' typ] >>=
                                runQ . lift . edgesToStrings)) decEdges
        `shouldBe` noDifferences

  it "can find the subtypes of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \typ ->
                                typeGraphVertices (const $ return Vertex) [runExpanded' typ] >>=
                                runQ . lift . map pprintType . Set.toList)) subtypesOfDec
        `shouldBe` noDifferences

  it "can find the arity 0 subtypes of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \typ ->
                                typeGraphVertices (const $ return Vertex) [runExpanded' typ] >>=
                                filterM (\ t -> typeArity t >>= \ a -> return (a == 0)) . Set.toList >>=
                                runQ . lift . map pprintType)) arity0SubtypesOfDec
        `shouldBe` noDifferences

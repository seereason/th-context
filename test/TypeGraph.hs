{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module TypeGraph where

import Control.Monad (filterM)
import Data.List as List (map)
import Data.Set as Set (fromList, map, toList)
--import GHC.Prim -- ByteArray#, Char#, etc
import Language.Haskell.TH
import Language.Haskell.TH.Context.Helpers (typeArity)
import Language.Haskell.TH.Context.TypeGraph (typeGraphVertices, typeGraphEdges, TypeGraphNode(..), typeNode, VertexStatus(Vertex), expandNode)
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax
import Test.Hspec hiding (runIO)
import Test.Hspec.Core.Spec (SpecM)

import Common
import Values

tests :: SpecM () ()
tests = do
  it "records a type synonym" $ do
     $([t|String|] >>= \ string -> typeNode string >>= lift) `shouldBe` (TypeGraphNode Nothing [''String] (AppT ListT (ConT ''Char)))

  it "can find the subtypesOfType" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                  runQ [t|Type|] >>= \typ ->
                                  typeGraphVertices (const $ return Vertex) [typ] >>=
                                  runQ . lift . List.map pprintNode . Set.toList)) subtypesOfType
        `shouldBe` noDifferences

  it "can find the edges of the subtype graph of Type (typeEdges)" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Type|] >>= \typ ->
                                typeGraphEdges (const $ return Vertex) [typ] >>=
                                runQ . lift . edgesToStrings)) typeEdges
        `shouldBe` noDifferences

  it "can find the edges of the subtype graph of Dec (decEdges)" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                typeGraphEdges (const $ return Vertex) [typ] >>=
                                runQ . lift . edgesToStrings)) decEdges
        `shouldBe` noDifferences

  it "can find the subtypesOfDec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                typeGraphVertices (const $ return Vertex) [typ] >>=
                                runQ . lift . List.map pprintNode . Set.toList)) subtypesOfDec
        `shouldBe` noDifferences

  it "can find the arity0SubtypesOfDec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                typeGraphVertices (const $ return Vertex) [typ] >>=
                                filterM (\ t -> typeArity (_etype t) >>= \ a -> return (a == 0)) . Set.toList >>=
                                runQ . lift . List.map pprintNode)) arity0SubtypesOfDec
        `shouldBe` noDifferences

  it "can find the expandedSubtypesOfDec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>= \typ ->
                                typeGraphVertices (const $ return Vertex) [typ] >>=
                                runQ . lift . List.map pprintNode . Set.toList . Set.map expandNode)) expandedSubtypesOfDec
        `shouldBe` noDifferences


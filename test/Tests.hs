{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import Test.Hspec hiding (runIO)
import Context (tests)

main :: IO ()
main = hspec $ do
  Context.tests

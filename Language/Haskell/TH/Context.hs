{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Haskell.TH.Context
    ( InstMap
    , tellInstance
    , reifyInstancesWithContext
    , runContext
    , execContext
    , evalContext
    , S
    , HasSet(..)
    , instMap
    , visited
    ) where

import Language.Haskell.TH.Context.Reify

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
    ) where

import Language.Haskell.TH.Context.Reify (InstMap, reifyInstancesWithContext, execContext, runContext)

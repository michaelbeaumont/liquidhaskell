{-# LANGUAGE ExistentialQuantification, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, TypeSynonymInstances, CPP, DeriveDataTypeable #-}



module Xmonad where

import Control.Monad.State
import Control.Monad.Reader

data XConf
data XState

newtype X a = X (ReaderT XConf (StateT XState IO) a)
    deriving (Monad, MonadIO, MonadState XState, MonadReader XConf)

runX :: XConf -> XState -> X a -> IO (a, XState)
runX c st (X a) = runStateT (runReaderT a c) st




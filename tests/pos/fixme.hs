module Fixme  where

import Prelude hiding (head)
import Language.Haskell.Liquid.Prelude

{-@ foo :: a -> {v:Bool| (Prop v) } @-}
foo :: a -> Bool
foo _ = 0==0

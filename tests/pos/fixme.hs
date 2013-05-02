
{-# LANGUAGE NoMonomorphismRestriction #-}

module Fun where

import Language.Haskell.Liquid.Prelude


data F a = F a a

{-@ data F a = F {ii :: a, jj :: {v:a|v>=ii}} @-}

{-@ measure getI :: F a -> a
    getI (F i j) = i
  @-}

{-@ measure getJ :: F a -> a
    getI (F i j) = j
  @-}

{-@ invariant {v:F a | (getI v) = (getJ v)}@-}
{-@ modify :: (F a -> F a) -> F a -> F a @-}
modify :: (F a -> F a) -> F a -> F a
modify = undefined

{-@ foo :: Eq a => F a -> F a @-}
foo :: Eq a => F a -> F a
foo = modify $ \c -> case c of {F i j -> liquidAssert (i == j) (F i j)}



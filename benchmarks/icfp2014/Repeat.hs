module Repeat where

import Prelude hiding (repeat, head, tail, map, filter)

{-@ codata L @-}

data L a = N | C a (L a)
infixr `C`

repeat :: a -> L a
repeat x = let xs = repeat x in x `C` xs

map f N = N
map f (C x xs) = C (f x) (map f xs) 

filter p N = N
filter p (C x xs) | p x       = x `C` filter p xs
                  | otherwise = filter p xs
head (C x _) = x

len N = 0
len (C _ xs) = 1 + len xs

{-
SMT query :: 

whnf xs => inf xs
-----------------
inf xs  => inf v

-}






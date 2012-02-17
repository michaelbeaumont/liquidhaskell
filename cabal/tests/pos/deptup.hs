module Deptup where

import Language.Haskell.Liquid.Prelude

data Pair a b = P a b

mkPair x y = P x y

incr :: Int -> Int
incr x = x + 1

baz    :: Int -> Pair Int Int    
baz x  = P x (incr x)

bazList  xs = map baz xs

n           = choose 0
xs          = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]

prop_baz    = chk (baz n) --map chk ( bazList xs )
--prop =  chk (P 0 1)
chk (P x y) = assert (x <= y)



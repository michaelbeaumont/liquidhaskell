module Repeat where

import Prelude hiding (tail, repeat, head)

{-@ LIQUID "--notermination" @-}


data L = N | C Int L
infixr `C`

{-@ measure llen :: L -> Int
    llen(N)      = 0
    llen(C x xs) = 1 + (llen xs)
  @-}

{-@ repeat :: i:Int -> Int -> {v:L | (llen v) > i} @-}
repeat :: Int -> Int -> L
repeat i x = C x (repeat i x)

{-
TYPING REPEAT

G0 = 
  fix :: T -> T -> T, 
  C   :: x:Int -> xs:L -> {v:L | llen v = llen xs + 1},
  N   :: {v:L | llen v = 0}

tf = i:Int -> Int -> {v:L | (llen v) > i}



G0, f:tf, i:Int, x:Int, xs :{v:L | llen v > i} |- C x xs  ::{v : L | llen v = 1 + llen xs} 

G0, f:tf, i:Int, x:Int, xs :{v:L | llen v > i} 
   |- {v : L | llen v = 1 + llen xs} <: {v:L | llen v > i}
-------------------------------------------------------------- [1]
G0, f:tf, i:Int, x:Int, xs :{v:L | llen v > i} |- C x xs  ::{v : L | llen v > i} 

G0, f:tf, i:Int, x:Int  |- f i x  ::{v : L | llen v > i} 
[1] G0, f:tf, i:Int, x:Int, xs :{v:L | llen v > i} |- C x xs  ::{v : L | llen v > i} 
--------------------------------------------------------------
G0, f:tf, i:Int, x:Int  |- let xs = f i x in C x xs :: {v:L | (llen v) > i}
--------------------------------------------------------------
G0, f:tf |- \i x -> let xs = f i x in C x xs :: tf
--------------------------------------------------------------
G0 |- \f i x -> let xs = f i x in C x xs :: tf -> tf
--------------------------------------------------------------
G0 |- fix (\f i x -> let xs = f i x in C x xs) :: tf
-}

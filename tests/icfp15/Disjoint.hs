-- Niki Vazou TODO : How dow we prove Disjiontness of the contra-variant domain?

module Disjoint where


data DB a = DB (Tag -> a) | Ghost Tag

{-@ data DB a <d :: Tag -> Prop>
  = DB (dummy:: (i:Tag<d> -> a))
  | Ghost (dummyghost::Tag<d>)
  @-}

{-@  disjoint ::forall <p :: Tag -> Prop, q :: Tag -> Prop>.
     {x:Tag<p> -> y:(Tag<q>) -> {v:Tag | v = x && v = y} -> {v:Tag|false}} 
   DB <p> Value -> DB <q> Value  -> DB Value
  @-}
disjoint :: DB Value -> DB Value -> DB Value
disjoint = undefined

data Value = V

data Tag = NAME 
         | AGE 
         | MAIL 
         | ADDRESS  
         deriving Eq


nameage, nameagemail :: DB Value
{-@ nameage     :: DB <{\v ->  v = NAME || v = AGE}> Value @-}
{-@ nameagemail :: DB <{\v ->  v = NAME || v = AGE || v = MAIL}> Value @-}
nameage     = undefined
nameagemail = undefined

foo = disjoint nameagemail nameage


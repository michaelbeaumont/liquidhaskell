module Language.Haskell.Liquid.Misc where

maybeIndex :: [a] -> Int -> Maybe a
maybeIndex ls     i | i < 0 = Nothing
maybeIndex []     _ = Nothing
maybeIndex (x:_)  0 = Just x
maybeIndex (_:xs) n = maybeIndex xs (n-1)
 

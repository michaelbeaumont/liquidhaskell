{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Haskell.Liquid.Productivity (
  productivityAnalysis, 
  checkProductiveExpr
) where

import CoreSyn 
import Id  (isDataConWorkId)
import Var

import Control.Applicative ((<$>))
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.GhcMisc

productivityAnalysis cbs = checkProductive <$> cbs

checkProductive bs@(NonRec x e) 
  | isProductive e = [("YES", x)]
  | otherwise      = [("NO" , x)]
checkProductive bs@(Rec xs) =  concatMap checkProductive ((\(x, e) -> NonRec x e) <$> xs) 

checkProductiveExpr :: Expr Id -> Bool
checkProductiveExpr = isProductive

isProductive (Var _) = False
isProductive (Lit _) = False
isProductive (App e a) | isDataCon e = True
                       | isType a    = isProductive e
                       | otherwise   = isProductive e
isProductive (Lam _ e) = traceShow ("LamCHECKING " ++ show e) $ isProductive e
isProductive (Let _ e) = traceShow ("LetCHECKING " ++ show e) $ isProductive e
isProductive (Case e _ _ alt) = isTrivial e && and (isProductive <$> (thd3 <$> alt))
isProductive (Cast e _) = isProductive e
isProductive (Tick _ e) = isProductive e
isProductive (Type _ ) = False
isProductive (Coercion _) = False

isTrivial (Var _) = True
isTrivial (Tick _ e) = isTrivial e
isTrivial _       = False

isDataCon (Var v) = traceShow ("ISDATACON" ++ show v ) $ isDataConWorkId v
isDataCon _       = False

isType (Type _) = True
isType _        = False


instance Show (Expr Id) where
  show = showPpr

instance Show Var where
  show = showPpr

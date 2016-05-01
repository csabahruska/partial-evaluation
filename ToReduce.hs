{-# LANGUAGE LambdaCase #-}
module ToReduce where

import qualified Curry as C
import Reduce

toLit = \case
  C.LFloat a -> LFloat a

toPrimFun = \case
  C.PAddI -> PAdd
  C.PMulF -> PMul

toExp :: C.TypedExp -> Exp
toExp = \case
  C.TELit     _ l -> ELit C (toLit l)
  C.TEPrimFun _ f -> EPrimFun C (toPrimFun f)
  C.TEVar     _ n -> EVar C n
  C.TEApp     _ a b -> EApp C (toExp a) (toExp b)
  C.TELam     _ n a -> ELam C n (toExp a)
  C.TEBody    _ a -> EBody C (toExp a)
  C.TELet     _ n a b -> ELet C n (toExp a) (toExp b)
  C.TECon     _ n a -> ECon C n $ map toExp a

toExp' :: C.Exp -> Exp
toExp' = \case
  C.ELit     l -> ELit C (toLit l)
  C.EPrimFun f -> EPrimFun C (toPrimFun f)
  C.EVar     n -> EVar C n
  C.EApp     a b -> EApp C (toExp' a) (toExp' b)
  C.ELam     n a -> ELam C n (toExp' a)
  C.EBody    a -> EBody C (toExp' a)
  C.ELet     n a b -> ELet C n (toExp' a) (toExp' b)
  C.ECon     n a -> ECon C n $ map toExp' a
  C.ECase    e l -> ECase C (toExp' e) (map toPat' l)

toPat' :: C.Pat -> Pat
toPat' (C.Pat n l e) = Pat n l (toExp' e)


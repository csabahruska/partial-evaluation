{-# LANGUAGE LambdaCase #-}
module ToReduce where

import qualified Curry as C
import Reduce
{-
data Exp
  -- pattern match
  | ECon      Stage ConName [Exp]
  | ECase     Stage Exp [Pat]
-}
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


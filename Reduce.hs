{-# language PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}

module Reduce where

import Debug.Trace
import Data.Map (Map)
import qualified Data.Map as Map

type EName = String

data Stage = R | C deriving (Show,Eq,Ord)

data Lit
  = LFloat Float
  deriving (Show,Eq,Ord)

data PrimFun
  = PAdd
  | PMul
  | PIfZero
  deriving (Show,Eq,Ord)

data Exp
  = ELit      Stage Lit
  | EPrimFun  Stage PrimFun
  | EVar      Stage EName
  | EApp      Stage Exp Exp
  | ELam      Stage EName Exp
  | ELet      Stage EName Exp Exp
  deriving (Show,Eq,Ord)

ifZero v t e = EApp C (EApp C (EApp C (EPrimFun C PIfZero) v) t) e
powerFun =
  ELet C "power" (ELam C "x" $ ELam C "n" $ ifZero (EVar C "n")
    (ELit C $ LFloat 1.0)
    (EApp C (EApp C (EPrimFun C PMul) (EVar C "x"))
            (EApp C (EApp C (EVar C "power") (EVar C "x")) (EApp C (EApp C (EPrimFun C PAdd) (ELit C $ LFloat $ -1.0)) (EVar C "n"))))
  )

reduceExp = powerFun $ EApp C (EApp C (EVar C "power") (ELit C $ LFloat 2.0)) (ELit C $ LFloat 3.0)

lit1 = ELit C $ LFloat 1.0
lit2 = ELit C $ LFloat 2.0

idFun = ELet C "id" (ELam C "x" $ EVar C "x")
reduceId = idFun $ EApp C (EVar C "id") lit1

lamIdFun = ELam C "x" $ EVar C "x"
reduceLamId = EApp C lamIdFun lit1

lamFun = ELam C "x" $ ELam C "y" $ EVar C "x"
reduceLamFun = EApp C (EApp C lamFun lit1) lit2

lamMixFun1 = ELam C "x" $ ELam R "y" $ ELam C "z" $ EApp R (EVar C "x") (EVar C "z") -- let fun = \x@C -> \y@R -> \z@C -> x@C z@C
reduceLamMix1 = EApp C (EApp R (EApp C lamMixFun1 lit1) (EVar R "a")) lit2 -- fun 1.0@C a@R 2.0@C ==> (\y -> 1.0 2.0) a

let0 = ELet C "v" lit1 $ EVar C "v"
let1 = ELet R "v" lit1 $ EVar R "v"

add = EApp C (EApp C (EPrimFun C PAdd) lit1) lit2
mul = EApp C (EApp C (EPrimFun C PMul) lit1) lit2

test = reduce mempty mempty reduceLamId
test1 = reduce mempty mempty reduceLamFun
test2 = reduce mempty mempty reduceLamMix1
test3 = reduce mempty mempty let0
test4 = reduce mempty mempty let1
test5 = reduce mempty mempty add
test6 = reduce mempty mempty mul

testPower = reduce mempty mempty reduceExp

type Env = Map EName Exp

addEnv env n x = Map.insert n x env

reduce env stack e = {-trace (unlines [show env,show stack,show e,"\n"]) $ -}case e of
  ELit {} -> e
  -- question: who should reduce the stack arguments?
  EPrimFun C PAdd | (ELit _ (LFloat a)):(ELit _ (LFloat b)):_ <- stack -> ELit C $ LFloat $ a + b
  EPrimFun C PMul | (ELit _ (LFloat a)):(ELit _ (LFloat b)):_ <- stack -> ELit C $ LFloat $ a * b
  EPrimFun C PIfZero -> error $ "PIfZero " ++ show stack
  EPrimFun C PIfZero | el:th:(ELit _ (LFloat v)):_ <- stack -> if v == 0 then reduce env (drop 3 stack) th else reduce env (drop 3 stack) el
--  EPrimFun {} -> e
--  EVar R n -> e
  EVar C n -> case Map.lookup n env of
    Nothing -> error $ "missing variable: " ++ n
    Just v -> reduce env stack v

  -- lam id
  ELam C n x -> reduce (addEnv env n (head stack)) (tail stack) x
--  EApp C f a -> reduce env (reduce env stack a:stack) f
  EApp C f a -> reduce env (a:stack) f

--  ELam R n x -> ELam R n $ reduce env (tail stack) x
--  EApp R f a -> EApp R (reduce env (a:stack) f) (reduce env stack a)

  ELet C n a b -> reduce (addEnv env n a) stack b
--  ELet R n a b -> ELet R n (reduce env stack a) (reduce env stack b)

  -- TODO: let
  _ -> error $ "can not reduce: " ++ show e
{-
  TODO:
    how to reduce "power"?
    how to specialise "power"?
-}


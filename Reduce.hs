{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

module Reduce where

import Debug.Trace
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

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
  -- specialization
  | EBody     Stage Exp
  -- during reduction
  | ESpec     EName Int Exp
  | ESpecFun  EName Exp
  deriving (Show,Eq,Ord)

powerFun =
  ELet C "power" (ELam C "x" $ ELam C "n" $ EBody C $ ifZero (EVar C "n")
    (ELit C $ LFloat 1.0)
    (EApp C (EApp C (EPrimFun C PMul) (EVar C "x"))
            (EApp C (EApp C (EVar C "power") (EVar C "x")) (EApp C (EApp C (EPrimFun C PAdd) (ELit C $ LFloat $ -1.0)) (EVar C "n"))))
  )

reduceExp = powerFun $ EApp C (EApp C (EVar C "power") (ELit C $ LFloat 2.0)) (ELit C $ LFloat 4.0)

lit0R = ELit R $ LFloat 0.0
lit1R = ELit R $ LFloat 1.0

lit0 = ELit C $ LFloat 0.0
lit1 = ELit C $ LFloat 1.0
lit2 = ELit C $ LFloat 2.0

ifZero v t e = EApp C (EApp C (EApp C (EPrimFun C PIfZero) v) t) e

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

letFun0 = ELet C "v" (ELam C "x" $ EBody C $ EVar C "x") $ EApp C (EVar C "v") lit1
letFun1 = ELet C "f" (ELam C "x" $ ELam C "y" $ EBody C $ ifZero (EVar C "x") (EVar C "y") (EApp C (EApp C (EVar C "f") (EVar C "y")) (EVar C "x"))) $
  EApp C (EApp C (EVar C "f") lit2) lit0

reduceIfZero = ifZero lit0 lit1 lit2

-------- specialization test
primAddR x y = EApp R (EApp R (EPrimFun R PAdd) x) y
specFun0 = ELam R "x" $ ELam C "y" $ EBody R $ primAddR (EVar R "x") (EVar C "y")
letSpecFun0 = ELet C "f" specFun0 $ EApp C (EApp R (EVar C "f") lit1R) lit2
letSpecFun1 = ELet C "f" specFun0 $ EApp C (EApp R (EVar C "f") (EApp C (EApp R (EVar C "f") lit1R) lit1)) lit2

powerFunR =
  ELet C "power" (ELam R "x" $ ELam C "n" $ EBody R $ ifZero (EVar C "n")
    (ELit C $ LFloat 1.0)
    (EApp R (EApp R (EPrimFun R PMul) (EVar R "x"))
            (EApp C (EApp R (EVar C "power") (EVar R "x")) (EApp C (EApp C (EPrimFun C PAdd) (ELit C $ LFloat $ -1.0)) (EVar C "n"))))
  )

powerExpR = powerFunR $ EApp C (EApp R (EVar C "power") lit2) lit1
--------
-- TODO
{-
  the generic function "f" should not be used in the residual; should be replaced with the specialised functions in the same scope
-}

test = runReduce reduceLamId
test1 = runReduce reduceLamFun
test2 = runReduce reduceLamMix1
test3 = runReduce let0
test4 = runReduce let1
test5 = runReduce add
test6 = runReduce mul
test7 = runReduce letFun0
test8 = runReduce reduceIfZero
test9 = runReduce letFun1
test10 = runReduce letSpecFun0
test11 = runReduce letSpecFun1
test12 = runReduce powerExpR

testPower = runReduce reduceExp

result = ELit C (LFloat 1.0)
result1 = ELit C (LFloat 1.0)
result2 = EApp R (ELam R "y" (EApp R (ELit C (LFloat 1.0)) (ELit C (LFloat 2.0)))) (EVar R "a")
result3 = ELit C (LFloat 1.0)
result4 = ELet R "v" (ELit C (LFloat 1.0)) (EVar R "v")
result5 = ELit C (LFloat 3.0)
result6 = ELit C (LFloat 2.0)
result7 = ELit C (LFloat 1.0)
result8 = ELit C (LFloat 1.0)
result9 = ELit C (LFloat 2.0)
resultPower = ELit C (LFloat 16.0)
result10 = ELet R "f0" (ELam R "x" (EBody R (EApp R (EApp R (EPrimFun R PAdd) (EVar R "x")) (ELit C (LFloat 2.0))))) (EApp R (EVar R "f0") (ELit R (LFloat 1.0)))
result11 =
   ELet R "f0" (ELam R "x" (EBody R (EApp R (EApp R (EPrimFun R PAdd) (EVar R "x")) (ELit C (LFloat 1.0)))))
  (ELet R "f1" (ELam R "x" (EBody R (EApp R (EApp R (EPrimFun R PAdd) (EVar R "x")) (ELit C (LFloat 2.0)))))
  (EApp R (EVar R "f1") (EApp R (EVar R "f0") (ELit R (LFloat 1.0)))))

tests =
  [ (test,result)
  , (test1,result1)
  , (test2,result2)
  , (test3,result3)
  , (test4,result4)
  , (test5,result5)
  , (test6,result6)
  , (test7,result7)
  , (test8,result8)
  , (test9,result9)
  , (testPower,resultPower)
  , (test10,result10)
  , (test11,result11)
  ]

ok = mapM_ (\(a,b) -> putStrLn $ show (a == b) ++ " - " ++ show b) tests

type Env = Map EName Exp

--TODO(improve scoping): addEnv env n x = Map.insertWith (\new old -> error $ "addEnv - name clash: " ++ n ++ " " ++ show (new,old)) n x env
addEnv env n x = Map.insert n x env

stage :: Exp -> Stage
stage = \case
  ELit      s _ -> s
  EPrimFun  s _ -> s
  EVar      s _ -> s
  EApp      s _ _ -> s
  ELam      s _ _ -> s
  ELet      s _ _ _ -> s
  EBody     s _ -> s
  ESpec     {} -> error "stage - ESpec"

-- HINT: the stack items are reduced expressions

insertSpec :: Exp -> EvalM Exp
insertSpec x = case {-trace (show x)-} x of
  EApp      s a b -> EApp s <$> insertSpec a <*> insertSpec b
  ELam      s n a -> ELam s n <$> insertSpec a
  ELet      s n a b -> ELet s n <$> insertSpec a <*> insertSpec b
  EBody     s a -> EBody s <$> insertSpec a
  ESpec     {} -> error "insertSpec - ESpec"
  ESpecFun  n b -> do
                    m <- gets (Map.lookup n)
                    case m of
                      Nothing -> error $ "insertSpec - ESpecFun: missing function: " ++ n
                      Just sm -> foldr (\(n,a) e -> ELet R n a e) <$> insertSpec b <*> pure (Map.elems sm)
  e -> return e

type EvalM = State (Map EName (Map [Maybe Exp] (EName,Exp)))

runReduce :: Exp -> Exp
runReduce a = evalState (reduce mempty mempty a >>= insertSpec) mempty

runReduce' a = runState (reduce mempty mempty a >>= insertSpec) mempty

reduce :: Env -> [Exp] -> Exp -> EvalM Exp
reduce env stack e = {-trace (unlines [show env,show stack,show e,"\n"]) $ -}case e of
  ELit {} -> return e
  -- question: who should reduce the stack arguments?
  --  answer: EApp

  EPrimFun C PAdd | (ELit _ (LFloat a)):(ELit _ (LFloat b)):_ <- stack -> return $ ELit C $ LFloat $ a + b
  EPrimFun C PMul | (ELit _ (LFloat a)):(ELit _ (LFloat b)):_ <- stack -> return $ ELit C $ LFloat $ a * b

  EPrimFun C PIfZero | (ELit _ (LFloat v)):th:el:_ <- stack -> return $ if v == 0 then th else el

  EPrimFun R _ -> return e

  EVar R n -> return e
  EVar C n -> case Map.lookup n env of
    Nothing -> error $ "missing variable: " ++ n
    Just v -> reduce env stack v

  ELam C n x -> reduce (addEnv env n (head stack)) (tail stack) x
  ELam R n x -> ELam R n <$> reduce env (tail stack) x

  EBody C a -> reduce env stack a
  EBody R a -> EBody R <$> reduce env stack a

  -- specialise function with key: name + args + body
  ESpec n i e -> do
                  m <- gets id
                  let args = [if stage a == C then Just a else Nothing | a <- take i stack]
                  (n',m') <- case Map.lookup n m of
                    Just sm -> case Map.lookup args sm of
                      Just (fn,_) -> return (fn,m)
                      Nothing -> do
                                  e' <- reduce env stack e
                                  m <- gets id
                                  let fn = n ++ show (Map.size m)
                                  return (fn,Map.adjust (\sm -> Map.insertWith (\_ _ -> error $ "args conflict") args (fn,e') sm) n m)
                    Nothing -> do
                                  e' <- reduce env stack e
                                  m <- gets id
                                  let fn = {-trace ("\n<SPEC> " ++ show (take 3 $ Map.keys m2) ++ "\n") $ -}n ++ show (Map.size m)
                                  return (fn,Map.insertWith (\_ _ -> error "name conflict") n (Map.singleton args (fn,e')) m)
                  put m'
                  return $ EVar R n'

  EApp C f a -> do
                  a' <- reduce env stack a
                  reduce env (a':stack) f
  EApp R f a -> do
                  a' <- reduce env stack a
                  EApp R <$> (reduce env (a':stack) f) <*> pure a'

  ELet C n a b -> do
    let go i l x = case x of
          EBody s _ -> (i,l)
          ELam s _ x -> go (i+1) (s:l) x
          _ | i == 0 -> (i,l)
            | otherwise -> error $ "invalid function: " ++ show a
        (arity,stages) = go 0 [] a
        needSpec = not $ null [() | C <- stages] || null [() | R <- stages]
    case arity > 0 && needSpec of
      True  -> ESpecFun n <$> reduce (addEnv env n (ESpec n arity a)) stack b
      False -> reduce (addEnv env n a) stack b
  ELet R n a b -> ELet R n <$> (reduce env stack a) <*> (reduce env stack b)

  _ -> error $ "can not reduce: " ++ show e

{-
  TODO:
    annotate RHS in let expressions
    specialize add x@c y@r
    how to specialise "power"?
-}

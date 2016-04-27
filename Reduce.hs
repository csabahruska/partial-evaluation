{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

module Reduce where

import Debug.Trace
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Writer
import Control.Monad.Reader
import Data.Foldable (foldrM)

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
  -- inserted during reduction
  | ESpec     EName Int Exp
  | ESpecLet  EName Exp
  | ESpecFun  EName [Maybe Exp] Exp -- original name, spec args, spec function
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
lit3 = ELit C $ LFloat 3.0

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
{-
  the generic function "f" should not be used in the residual; should be replaced with the specialised functions in the same scope
-}

powerFunR =
  ELet C "power" (ELam R "x" $ ELam C "n" $ EBody R $ ifZero (EVar C "n")
    (ELit C $ LFloat 1.0)
    (EApp R (EApp R (EPrimFun R PMul) (EVar R "x"))
            (EApp C (EApp R (EVar C "power") (EVar R "x")) (EApp C (EApp C (EPrimFun C PAdd) (ELit C $ LFloat $ -1.0)) (EVar C "n"))))
  )

powerExpR = powerFunR $ EApp C (EApp R (EVar C "power") lit2) lit1
powerExpR1 = powerFunR $ EApp C (EApp R (EVar C "power") lit2) lit2

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
test13 = runReduce powerExpR1

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

result12 =
   ELet R "power0" (ELam R "x" (EBody R (ELit C (LFloat 1.0))))
  (ELet R "power1" (ELam R "x" (EBody R (EApp R (EApp R (EPrimFun R PMul) (EVar R "x")) (EApp R (EVar R "power0") (EVar R "x")))))
  (EApp R (EVar R "power1") (ELit C (LFloat 2.0))))

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
  , (test12,result12)
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
type SpecW = Writer (Map (EName,[Maybe Exp]) Exp)

collectSpec :: Exp -> SpecW Exp
collectSpec x = case x of
  EApp      s a b -> EApp s <$> collectSpec a <*> collectSpec b
  ELam      s n a -> ELam s n <$> collectSpec a
  ELet      s n a b -> ELet s n <$> collectSpec a <*> collectSpec b
  EBody     s a -> EBody s <$> collectSpec a
  ESpec     {} -> error "collectSpec - ESpec"
  ESpecLet  n b -> ESpecLet n <$> collectSpec b
  ESpecFun  n a f -> collectSpec f >> x <$ tell (Map.singleton (n,a) f)
  e -> return e

type SpecR = Reader (Map EName (Map [Maybe Exp] (EName,Exp)))

insertSpec :: Exp -> SpecR Exp
insertSpec x = case x of
  EApp      s a b -> EApp s <$> insertSpec a <*> insertSpec b
  ELam      s n a -> ELam s n <$> insertSpec a
  ELet      s n a b -> ELet s n <$> insertSpec a <*> insertSpec b
  EBody     s a -> EBody s <$> insertSpec a
  ESpec     {} -> error "insertSpec - ESpec"
  ESpecLet  n b -> do
                    m <- reader (Map.lookup n)
                    case m of
                      Nothing -> error $ "insertSpec - ESpecLet: missing function: " ++ n
                      Just sm -> do
                        b' <- insertSpec b
                        foldrM (\(n,a) e -> ELet R n <$> insertSpec a <*> insertSpec e) b' (Map.elems sm)
  ESpecFun  n a _ -> do
                    m <- reader (Map.lookup n)
                    case m of
                      Nothing -> error $ "insertSpec - ESpecFun: missing function: " ++ n
                      Just sm -> case Map.lookup a sm of
                        Nothing -> error $ "insertSpec - ESpecFun: missing spec function: " ++ n ++ " args: " ++ show a
                        Just (sn,_) -> return $ EVar R sn
  e -> return e

runReduce :: Exp -> Exp
runReduce exp = runReader (insertSpec rExp) m
  where
    rExp = reduce mempty mempty exp
    specMap = execWriter $ collectSpec rExp
    m = go (Map.toList specMap) mempty
    go [] m = m
    go (((n,a),f):l) m = go l $ case Map.lookup n m of
      Nothing -> Map.insert n (Map.singleton a (n ++ "0",f)) m
      Just sm -> case Map.lookup a sm of
        Nothing -> Map.adjust (\sm -> Map.insert a (n ++ show (Map.size sm),f) sm) n m
        Just _  -> m

reduce :: Env -> [Exp] -> Exp -> Exp
reduce env stack e = {-trace (unlines [show env,show stack,show e,"\n"]) $ -}case e of
  ELit {} -> e
  -- question: who should reduce the stack arguments?
  --  answer: EApp

  EPrimFun C PAdd | (ELit _ (LFloat a)):(ELit _ (LFloat b)):_ <- stack -> ELit C $ LFloat $ a + b
  EPrimFun C PMul | (ELit _ (LFloat a)):(ELit _ (LFloat b)):_ <- stack -> ELit C $ LFloat $ a * b
  EPrimFun C PIfZero | (ELit _ (LFloat v)):th:el:_ <- stack -> if v == 0 then th else el

  EPrimFun R _ -> e

  EVar R n -> e
  EVar C n -> case Map.lookup n env of
    Nothing -> error $ "missing variable: " ++ n
    Just v -> reduce env stack v

  ELam C n x -> reduce (addEnv env n (head stack)) (tail stack) x
  ELam R n x -> ELam R n $ reduce env (tail stack) x

  EBody C a -> reduce env stack a
  EBody R a -> EBody R $ reduce env stack a

  EApp C f a -> reduce env (a':stack) f where a' = reduce env stack a
  EApp R f a -> EApp R (reduce env (a':stack) f) a' where a' = reduce env stack a

  ELet R n a b -> ELet R n (reduce env stack a) (reduce env stack b)
  ELet C n a b ->
    case arity > 0 && needSpec of
      True  -> ESpecLet n $ reduce (addEnv env n (ESpec n arity a)) stack b
      False -> reduce (addEnv env n a) stack b
   where
        go i l x = case x of
          EBody s _ -> (i,l)
          ELam s _ x -> go (i+1) (s:l) x
          _ | i == 0 -> (i,l)
            | otherwise -> error $ "invalid function: " ++ show a
        (arity,stages) = go 0 [] a
        needSpec = not $ null [() | C <- stages] || null [() | R <- stages]

  -- inserted by ELet C
  ESpec n i e -> ESpecFun n args (reduce env stack e) where args = [if stage a == C then Just a else Nothing | a <- take i stack]

  _ -> error $ "can not reduce: " ++ show e

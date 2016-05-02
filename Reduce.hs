{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

module Reduce where

import Debug.Trace
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Writer
import Control.Monad.Reader
import Data.Foldable (foldrM,find)

type EName = String
type ConName = String

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
  -- pattern match
  | ECon      Stage ConName [Exp]
  | ECase     Stage Exp [Pat]
  deriving (Show,Eq,Ord)

data Pat = Pat ConName [EName] Exp deriving (Show,Eq,Ord)

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
  e -> error $ "stage: " ++ show e

-- HINT: the stack items are reduced expressions
type SpecW = Writer (Map (EName,[Maybe Exp]) Exp)

collectSpec :: Exp -> SpecW Exp
collectSpec x = case x of
  EApp      R a b -> EApp R <$> collectSpec a <*> collectSpec b
  ELam      R n a -> ELam R n <$> collectSpec a
  ELet      R n a b -> ELet R n <$> collectSpec a <*> collectSpec b
  EBody     R a -> EBody R <$> collectSpec a
  ESpec     {} -> error "collectSpec - ESpec"
  ESpecLet  n b -> ESpecLet n <$> collectSpec b
  ESpecFun  n a f -> collectSpec f >> x <$ tell (Map.singleton (n,a) f)
  ELit      {} -> return x
  EPrimFun  {} -> return x
  EVar      {} -> return x
  ECon      s n l -> ECon s n <$> mapM collectSpec l
  ECase     R a l -> ECase R <$> collectSpec a <*> mapM (\(Pat pn vl b) -> Pat pn vl <$> collectSpec b) l
  e -> error $ "collectSpec: " ++ show e

type SpecR = Reader (Map EName (Map [Maybe Exp] (EName,Exp)))

insertSpec :: Exp -> SpecR Exp
insertSpec x = case x of
  EApp      R a b -> EApp R <$> insertSpec a <*> insertSpec b
  ELam      R n a -> ELam R n <$> insertSpec a
  ELet      R n a b -> ELet R n <$> insertSpec a <*> insertSpec b
  EBody     R a -> EBody R <$> insertSpec a
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
  ELit      {} -> return x
  EPrimFun  {} -> return x
  EVar      {} -> return x
  ECon      s n l -> ECon s n <$> mapM insertSpec l
  ECase     R a l -> ECase R <$> insertSpec a <*> mapM (\(Pat pn vl b) -> Pat pn vl <$> insertSpec b) l
  e -> error $ "insertSpec: " ++ show e

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

  -- HINT: we can not eliminate ECon C here, but they should disappear from the residual exp
  ECon s n l -> ECon s n (map (reduce env stack) l)

  ECase R e l -> ECase R (reduce env stack e) [Pat n v (reduce env stack a) | Pat n v a <- l]
  ECase C e l -> case reduce env stack e of
                  ECon C n vExp -> p where
                    go a [] [] = a
                    go a (x:xs) (y:ys) = go (Map.insert x y a) xs ys
                    go _ x y = error $ "invalid pattern and constructor: " ++ show (n,x,y)
                    p = case find (\(Pat pn _ _) -> n == pn) l of
                          Nothing -> error $ "no matching pattern for constructor: " ++ n
                          Just (Pat _ vNames body) -> reduce (go env vNames vExp) stack body
                  x -> error $ "invalid case expression: " ++ show x

  _ -> error $ "can not reduce: " ++ show e ++ " stack: " ++ show stack

{-
  pattern match:
    case x of
      Tag a b c ... -- Contructor Tag + variables
  -- evaluation of a constructor alternative is like in Lam + App

  example:
    data Maybe a = Nothing | Just a

    let x = Just 1
    in case x of
        Nothing -> 0
        Just i  -> i
-}

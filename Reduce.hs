{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

module Reduce where

import Text.Show.Pretty

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
  -- partial app
  | EThunk    Env [Arg EName] [Arg EName] [Arg Exp] Exp -- env, missing args, all arg names, applied args, body
  deriving (Show,Eq,Ord)

data Arg a = Arg Stage a deriving (Show,Eq,Ord)

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
    rExp = reduce mempty exp
    specMap = execWriter $ collectSpec rExp
    m = go (Map.toList specMap) mempty
    go [] m = m
    go (((n,a),f):l) m = go l $ case Map.lookup n m of
      Nothing -> Map.insert n (Map.singleton a (n ++ "0",f)) m
      Just sm -> case Map.lookup a sm of
        Nothing -> Map.adjust (\sm -> Map.insert a (n ++ show (Map.size sm),f) sm) n m
        Just _  -> m

primThunk :: [EName] -> Exp -> Exp
primThunk l = EThunk mempty ns ns [] where ns = [Arg C n | n <- l]

evalPrimFun :: Env -> PrimFun -> Exp
evalPrimFun env = \case
  PAdd | Just (ELit _ (LFloat a)) <- Map.lookup "x" env
       , Just (ELit _ (LFloat b)) <- Map.lookup "y" env -> ELit C $ LFloat $ a + b
  PMul | Just (ELit _ (LFloat a)) <- Map.lookup "x" env
       , Just (ELit _ (LFloat b)) <- Map.lookup "y" env -> ELit C $ LFloat $ a * b
  PIfZero | Just (ELit _ (LFloat v)) <- Map.lookup "c" env
          , Just th <- Map.lookup "t" env
          , Just el <- Map.lookup "e" env -> if v == 0 then th else el

 -- TODO: add R lambdas and R apps
evalThunk (EThunk env [] ns vs exp) = foldr mkApp (foldr mkLam rexp ns) vs where
  rexp = case exp of
    EPrimFun C f -> evalPrimFun env f
    _ -> reduce env exp
  mkApp (Arg C _) x = x
  mkApp (Arg R v) x = EApp R x v
  mkLam (Arg C _) x = x
  mkLam (Arg R n) x = ELam R n x
evalThunk e@EThunk{} = e
evalThunk e = error $ "evalThunk - expected a thunk, got: " ++ show e

reduce :: Env -> Exp -> Exp
reduce env e = {-trace (unlines [show env,show stack,show e,"\n"]) $ -}case e of
  ELit {} -> e

  EPrimFun C PAdd -> primThunk ["x","y"] e
  EPrimFun C PMul -> primThunk ["x","y"] e
  EPrimFun C PIfZero -> primThunk ["c","t","e"] e

  EPrimFun R _ -> e

  EVar R n -> e
  EVar C n -> case Map.lookup n env of
    Nothing -> error $ "missing variable: " ++ n
    Just v -> reduce env v

  -- check arity and create thunk: env + missing arg count
  ELam{} -> go [] e where
        go l x = case x of
          ELam s a x -> go ((Arg s a):l) x
          b -> EThunk env revl revl [] b where revl = reverse l

  EBody C a -> reduce env a
  EBody R a -> EBody R $ reduce env a

  -- apply arg to thunk or if it's saturated then cretate a new thunk
  EApp s f a -> let a' = reduce env a in
                case reduce env f of
                  EThunk tenv ((Arg s' n):ns) args apps b
                    | False && s /= s' -> error $ "EApp - stage mismatch: " ++ show e
                    | otherwise -> evalThunk $ case s of
                                    C -> EThunk (Map.insert n a' tenv) ns args ((Arg C a'):apps) b
                                    R -> EThunk tenv ns args ((Arg R a'):apps) b
                  x@(EPrimFun R _) -> x
                  x -> error $ "EApp - expected a thunk, got: " ++ show x

  ELet R n a b -> ELet R n (reduce env a) (reduce env b)
  ELet C n a b ->
    case arity > 0 && needSpec of
      True  -> ESpecLet n $ reduce (addEnv env n (ESpec n arity a)) b -- TODO: add fun name to thunk to generate ESpecFun at eval
      False -> reduce (addEnv env n a) b
   where
        go i l x = case x of
          EBody s _ -> (i,l)
          ELam s _ x -> go (i+1) (s:l) x
          _ | i == 0 -> (i,l)
            | otherwise -> error $ "invalid function: " ++ show a
        (arity,stages) = go 0 [] a
        needSpec = False -- not $ null [() | C <- stages] || null [() | R <- stages]

  -- inserted by ELet C
  ESpec n i e -> ESpecFun n args (reduce env e) where args = [if stage a == C then Just a else Nothing | a <- take i []] -- TODO

  -- HINT: we can not eliminate ECon C here, but they should disappear from the residual exp
  ECon s n l -> ECon s n (map (reduce env) l)

  ECase R e l -> ECase R (reduce env e) [Pat n v (reduce env a) | Pat n v a <- l]
  ECase C e l -> case reduce env e of
                  ECon C n vExp -> p where
                    go a [] [] = a
                    go a (x:xs) (y:ys) = go (Map.insert x y a) xs ys
                    go _ x y = error $ "invalid pattern and constructor: " ++ show (n,x,y)
                    p = case find (\(Pat pn _ _) -> n == pn) l of
                          Nothing -> error $ "no matching pattern for constructor: " ++ n
                          Just (Pat _ vNames body) -> reduce (go env vNames vExp) body
                  x -> error $ "invalid case expression: " ++ show x

  EThunk{} -> evalThunk e
  _ -> error $ "can not reduce: " ++ ppShow e

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

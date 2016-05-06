{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Reduce where

import Text.Show.Pretty

import Debug.Trace
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Writer
import Control.Monad.Reader
import Data.Foldable (foldrM,find)
import Data.Text (Text,pack,unpack)

type EName = Text
type ConName = Text

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
  | EThunk    (Maybe (EName,Int)) Env [Arg EName] [Arg EName] [Arg Exp] Exp -- function specialization info (name + arity till RHS)
                                                                            -- env, missing args, all arg names, applied args, body
  deriving (Show,Eq,Ord)

data Arg a = Arg Stage a deriving (Show,Eq,Ord)

data Pat
  = PatCon      ConName [EName] Exp
  | PatLit      Lit Exp
  | PatWildcard Exp
  deriving (Show,Eq,Ord)

type Env = Map EName Exp

--TODO(improve scoping): addEnv env n x = Map.insertWith (\new old -> error $ "addEnv - name clash: " ++ n ++ " " ++ show (new,old)) n x env
addEnv env n x = Map.insert n x env

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
  ECase     R a l -> ECase R <$> collectSpec a <*> mapM (traversePat collectSpec) l
  EThunk    _ _ [] _ _ _ -> collectSpec $ evalThunk x
  e -> error $ "collectSpec: " ++ show e

traversePat f = \case
  PatCon pn vl b -> PatCon pn vl <$> f b
  PatLit l b -> PatLit l <$> f b
  PatWildcard b -> PatWildcard <$> f b

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
                      Nothing -> error $ "insertSpec - ESpecLet: missing function: " ++ unpack n
                      Just sm -> do
                        b' <- insertSpec b
                        foldrM (\(n,a) e -> ELet R n <$> insertSpec a <*> insertSpec e) b' (Map.elems sm)
  ESpecFun  n a _ -> do
                    m <- reader (Map.lookup n)
                    case m of
                      Nothing -> error $ "insertSpec - ESpecFun: missing function: " ++ unpack n
                      Just sm -> case Map.lookup a sm of
                        Nothing -> error $ "insertSpec - ESpecFun: missing spec function: " ++ unpack n ++ " args: " ++ show a
                        Just (sn,_) -> return $ EVar R sn
  ELit      {} -> return x
  EPrimFun  {} -> return x
  EVar      {} -> return x
  ECon      s n l -> ECon s n <$> mapM insertSpec l
  ECase     R a l -> ECase R <$> insertSpec a <*> mapM (traversePat insertSpec) l
  e -> error $ "insertSpec: " ++ show e

runReduce :: Exp -> Exp
runReduce exp = runReader (insertSpec rExp) m
  where
    (rExp,specMap) = runWriter $ collectSpec $ reduce mempty exp
    m = go (Map.toList specMap) mempty
    go [] m = m
    go (((n,a),f):l) m = go l $ case Map.lookup n m of
      Nothing -> Map.insert n (Map.singleton a (n <> "0",f)) m
      Just sm -> case Map.lookup a sm of
        Nothing -> Map.adjust (\sm -> Map.insert a (n <> pack (show (Map.size sm)),f) sm) n m
        Just _  -> m

evalPrimFun :: Env -> PrimFun -> Exp
evalPrimFun env = \case
  PAdd | Just (ELit _ (LFloat a)) <- Map.lookup "x" env
       , Just (ELit _ (LFloat b)) <- Map.lookup "y" env -> ELit C $ LFloat $ a + b
  PMul | Just (ELit _ (LFloat a)) <- Map.lookup "x" env
       , Just (ELit _ (LFloat b)) <- Map.lookup "y" env -> ELit C $ LFloat $ a * b
  PIfZero | Just (ELit _ (LFloat v)) <- Map.lookup "c" env
          , Just th <- Map.lookup "t" env
          , Just el <- Map.lookup "e" env -> if v == 0 then th else el

evalThunk (EThunk spec env [] ns vs exp) = foldr mkApp (mkSpecFun $ foldr mkLam rexp ns) vs where
  rexp = case exp of
    EPrimFun C f -> evalPrimFun env f
    EPrimFun R f -> exp
    _ -> reduce env exp

  mkSpecFun e = case spec of
    Nothing    -> e
    Just (n,i) -> ESpecFun n args e where args = [if s == C then Just a else Nothing | Arg s a <- take i $ reverse $ {-trace ("\n* ESpecFun args: " ++ show (reverse vs))-} vs]

  mkApp (Arg C _) x = x
  mkApp (Arg R v) x = EApp R x v

  mkLam (Arg C _) x = x
  mkLam (Arg R n) x = case exp of
    EPrimFun{} -> x
    _ -> ELam R n x
evalThunk e@EThunk{} = {-# SCC thunk_bypass #-} e
evalThunk e = error $ "evalThunk - expected a thunk, got: " ++ show e

primThunk :: [EName] -> Exp -> Exp
primThunk l = EThunk Nothing mempty ns ns [] where ns = [Arg C n | n <- l]

valThunk :: Env -> Exp -> Exp
valThunk env = EThunk Nothing env mempty mempty mempty

reduce :: Env -> Exp -> Exp
reduce env e = {-trace (unlines [show env,show stack,show e,"\n"]) $ -}case e of
  ELit {} -> {-# SCC elit #-} e

  EPrimFun _ PAdd -> {-# SCC eprimfun_padd #-} primThunk ["x","y"] e
  EPrimFun _ PMul -> {-# SCC eprimfun_pmul #-} primThunk ["x","y"] e
  EPrimFun _ PIfZero -> {-# SCC eprimfun_pifzero #-} primThunk ["c","t","e"] e

  EVar R n -> e
  EVar C n -> {-# SCC evar #-} case Map.lookup n env of
    Nothing -> error $ "missing variable: " ++ unpack n
    Just v -> reduce env v

  -- check arity and create thunk: env + missing arg count
  ELam{} -> {-# SCC elam #-} go [] e where
        go l x = case x of
          ELam s a x -> go ((Arg s a):l) x
          b -> EThunk Nothing env revl revl [] b where revl = reverse $ {-trace ("\n* EThunk args: " ++ show l)-} l

  EBody C a -> {-# SCC ebody #-} reduce env a
  EBody R a -> EBody R $ reduce env a

  -- apply arg to thunk or if it's saturated then cretate a new thunk
  EApp s f a -> {-# SCC eapp #-} let a' = reduce env a in
                case reduce env f of
                  EThunk spec tenv names@((Arg s' n):ns) args apps b
                    | False && s /= s' -> error $ "EApp - stage mismatch: " ++ show (e,names) -- TODO
                    | otherwise -> evalThunk $ EThunk spec (addEnv tenv n a') ns args ((Arg s a'):apps) b
                  x -> error $ "EApp - expected a thunk, got: " ++ show x

  ELet R n a b -> ELet R n (reduce env a) (reduce env b)
  ELet C n a b -> {-# SCC elet_c #-}
    case arity > 0 && needSpec of
      True  -> {-# SCC elet_spec #-} ESpecLet n $ reduce (addEnv env n (ESpec n arity a)) b -- add fun name to thunk to generate ESpecFun at eval
      False -> reduce (addEnv env n a) b
   where
        go i l x = case x of
          EBody s _ -> (i,l)
          ELam s _ x -> go (i+1) (s:l) x
          _ | i == 0 -> (i,l)
            | otherwise -> error $ "invalid function: " ++ show a
        (arity,stages) = go 0 [] a
        needSpec = not $ null [() | C <- stages] || null [() | R <- stages]

  -- inserted by ELet C
  ESpec n i b -> {-# SCC espec #-} case reduce env b of
                  EThunk Nothing tenv ns args apps b -> EThunk (Just (n,i)) tenv ns args apps b
                  x -> error $ "ESpec - expected a thunk without spec, got: " ++ show x

  -- HINT: we can not eliminate ECon C here, but they should disappear from the residual exp
  ECon s n l -> {-# SCC econ #-} ECon s n (map (valThunk env) l)

  ECase R e l -> ECase R (reduce env e) (map reducePat l) where
                  reducePat = \case
                    PatCon n v a -> PatCon n v (reduce env a)
                    PatLit l a -> PatLit l (reduce env a)
                    PatWildcard a -> PatWildcard (reduce env a)
  ECase C e l -> {-# SCC ecase #-} case reduce env e of
                  ECon C n vExp -> findPat l $ error $ "no matching pattern for constructor: " ++ unpack n where
                    go a [] [] = a
                    go a (x:xs) (y:ys) = go (addEnv a x y) xs ys
                    go _ x y = error $ "invalid pattern and constructor: " ++ show (n,x,y)
                    findPat [] defPat = defPat
                    findPat (x:xs) defPat = case x of
                      PatCon pn vNames body | n == pn -> {-# SCC ecase_patcon #-} reduce (go env vNames vExp) body
                      PatWildcard body -> findPat xs $ reduce env body
                      _ -> findPat xs defPat
                  ELit C v -> findPat l $ error $ "no matching pattern for literal: " ++ show v where
                    findPat [] defPat = defPat
                    findPat (x:xs) defPat = case x of
                      PatLit pv body | v == pv -> {-# SCC ecase_patlit #-} reduce env body
                      PatWildcard body -> findPat xs $ reduce env body
                      _ -> findPat xs defPat
                  x -> error $ "invalid case expression: " ++ show x

  EThunk{} -> {-# SCC ethunk #-} evalThunk e
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

module Curry where
import Data.Functor.Identity
import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid
import Data.Functor

data Lit
  = LInt
  | LBool
  | LFloat
  deriving (Show,Eq,Ord)

data PrimFun
  = PAddI
  | PAnd
  | PMulF
  deriving (Show,Eq,Ord)

data Exp
  = ELit      Lit
  | EPrimFun  PrimFun
  | EVar      EName
  | EApp      Exp Exp
  | ELam      EName Exp
  | EBody     Exp
  | ELet      EName Exp Exp
  deriving (Show,Eq,Ord)

data TypedExp
  = TELit     Ty Lit
  | TEPrimFun Ty PrimFun
  | TEVar     Ty EName
  | TEApp     Ty TypedExp TypedExp
  | TELam     Ty EName TypedExp
  | TEBody    Ty TypedExp
  | TELet     Ty EName TypedExp TypedExp
  deriving (Show,Eq,Ord)

infixr 7 :->
data Ty
  = TVar TName
  | Ty :-> Ty
  -- primitive types
  | TInt
  | TBool
  | TFloat
  deriving (Show,Eq,Ord)

type EName = String
type TName = String
type Env = Map EName Ty
type Subst = Map TName Ty

inferPrimFun :: PrimFun -> Ty
inferPrimFun a = case a of
  PAddI   -> TInt :-> TInt :-> TInt
  PAnd    -> TBool :-> TBool :-> TBool
  PMulF   -> TFloat :-> TFloat :-> TFloat

inferLit :: Lit -> Ty
inferLit a = case a of
  LInt    -> TInt
  LBool   -> TBool
  LFloat  -> TFloat

type Unique a = StateT Int (Except String) a

newVar :: Unique Ty
newVar = do
  n <- get
  put (n+1)
  return $ TVar $ 't':show n

applyEnv :: Env -> Subst -> Env
applyEnv e s = fmap (flip apply s) e

apply :: Ty -> Subst -> Ty
apply (TVar a) st = case Map.lookup a st of
  Nothing -> TVar a
  Just t  -> t
apply (a :-> b) st = (apply a st) :-> (apply b st)
apply t _ = t

unify :: Ty -> Ty -> Unique Subst
unify (TVar u) t = bindVar u t
unify t (TVar u) = bindVar u t
unify (a1 :-> b1) (a2 :-> b2) = do
  s1 <- unify a1 a2
  s2 <- unify (apply b1 s1) (apply b2 s1)
  return $ s1 `compose` s2
unify a b
  | a == b = return mempty
  | otherwise = throwError $ "can not unify " ++ show a ++ " with " ++ show b

freeVars :: Ty -> Set TName
freeVars (TVar a) = Set.singleton a
freeVars (a :-> b) = freeVars a `mappend` freeVars b
freeVars _ = mempty

bindVar :: TName -> Ty -> Unique Subst
bindVar n t
  | TVar n == t = return mempty
  | n `Set.member` freeVars t = throwError $ "Infinite type, type variable " ++ n ++ " occurs in " ++ show t
  | otherwise = return $ Map.singleton n t

compose :: Subst -> Subst -> Subst
compose a b = mappend a $ (flip apply) a <$> b

remove :: EName -> Env -> Env
remove n e = Map.delete n e

infer env (EPrimFun f) = do
  let t = inferPrimFun f
  return (mempty,t,\s -> TEPrimFun (apply t s) f)
infer env (ELit l) = do
  let t = inferLit l
  return (mempty,t,\s -> TELit (apply t s) l)
infer env (EVar n) = case Map.lookup n env of
  Nothing -> throwError $ "unbounded variable: " ++ n
  Just t  -> return (mempty,t,\s -> TEVar (apply t s) n)
infer env (EApp f a) = do
  (s1,t1,f') <- infer env f
  (s2,t2,a') <- infer env a
  tv <- newVar
  s3 <- unify (apply t1 s2) (t2 :-> tv)
  let t = apply tv s3
  return (s1 `compose` s2 `compose` s3, t, \s -> TEApp (apply t s) (f' s) (a' s))
infer env (ELam n e) = do
  tv <- newVar
  (s1,tbody,e') <- infer (Map.insert n tv env) e
  let t = (apply tv s1) :-> tbody
  return (s1,t,\s -> TELam (apply t s) n (e' s))
infer env (EBody e) = (\(s,t,a) -> (s,t,\b -> TEBody (apply t b) $ a b)) <$> infer env e
infer env (ELet n e1 e2) = do
  (s1,t1,e1') <- infer env e1
  let env' = applyEnv (Map.insert n t1 env) s1
  (s2,t2,e2') <- infer env' e2
  return (s1 `compose` s2,t2,\s -> TELet (apply t2 s) n (e1' s) (e2' s))

inference :: Exp -> Either String TypedExp
inference e = runIdentity $ runExceptT $ (flip evalStateT) 0 act
 where
  act = do
    (s,t,e') <- infer mempty e
    return (e' s)--(apply t s)

-- test
ok =
  [ ELit LInt
{-
  , ELam "x" $ EVar "x"
  , ELam "x" $ ELam "y" $ ELit LFloat
  , ELam "x" $ EApp (EVar "x") (ELit LBool)
  , ELam "x" $ EApp (EApp (EPrimFun PAddI) (ELit LInt)) (EVar "x")
-}
  , ELet "id" (ELam "x" $ EVar "x") (ELet "a" (EApp (EVar "id") (ELit LBool)) (EApp (EVar "id") (ELit LBool)))
  ]
err =
  [ ELam "x" $ EApp (EVar "x") (EVar "x")
  , EApp (ELit LInt) (ELit LInt)
  , ELet "id" (ELam "x" $ EVar "x") (ELet "a" (EApp (EVar "id") (ELit LBool)) (EApp (EVar "id") (ELit LFloat)))
  ]

test = do
  putStrLn "Ok:"
  mapM_ (\e -> print e >> (print . inference $ e)) ok
--  putStrLn "Error:"
--  mapM_ (\e -> print e >> (print . inference $ e)) err


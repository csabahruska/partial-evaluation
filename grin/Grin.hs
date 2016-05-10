{-# LANGUAGE LambdaCase #-}
module Grin where

import Debug.Trace

import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Control.Monad.State
import Control.Monad.Reader

type Name = String

type Prog = Map Name Def

data Def = Def Name [Name] Exp
  deriving Show

data Exp
  = Bind  SimpleExp LPat Exp
  | Case  Val [Alt]
  | SExp  SimpleExp
  deriving Show

data SimpleExp
  = App     Name [SimpleVal]
  | Return  Val
  | Store   Val
  | Fetch   Name
--  | FetchI  Name Int -- fetch node component
  | Update  Name Val
--  | Block   Exp
  deriving Show

type LPat = Val
type SimpleVal = Val
data Val
  = TagNode   Tag  [SimpleVal]
  | VarNode   Name [SimpleVal]
  | ValTag    Tag
  | Unit
  -- simple val
  | Lit Lit
  | Var Name
  -- extra
  | Loc Int
  | Undefined
  deriving (Eq,Show)

data Lit = LFloat Float
  deriving (Eq,Show)

data Alt = Alt CPat Exp
  deriving Show

data CPat
  = NodePat Tag [Name]
  | TagPat  Tag
  | LitPat  Lit
  deriving Show

data TagType = C | F | P
  deriving (Eq,Show)

data Tag = Tag TagType Name Int
  deriving (Eq,Show)

type Store = IntMap Val
type Env = Map Name Val
type GrinM = ReaderT Prog (State Store)

bindPatMany :: Env -> [Val] -> [LPat] -> Env
bindPatMany a [] [] = a
bindPatMany a (x:xs) (y:ys) = bindPatMany (bindPat a x y) xs ys
bindPatMany _ x y = error $ "bindPatMany - pattern mismatch: " ++ show (x,y)

bindPat :: Env -> Val -> LPat -> Env
bindPat env v p = case p of
  Var n -> case v of
              ValTag{}  -> Map.insert n v env
              Unit      -> Map.insert n v env
              Lit{}     -> Map.insert n v env
              Loc{}     -> Map.insert n v env
              Undefined -> Map.insert n v env
              _ -> {-trace ("bindPat - illegal value: " ++ show v) $ -}Map.insert n v env
              _ -> error $ "bindPat - illegal value: " ++ show v
  TagNode t l -> case v of
                  TagNode vt vl | vt == t -> bindPatMany env vl l
                  _ -> error $ "bindPat - illegal value for TagNode: " ++ show v
  VarNode n l -> case v of
                  TagNode vt vl -> bindPatMany (Map.insert n (ValTag vt) env) vl l
                  _ -> error $ "bindPat - illegal value for TagNode: " ++ show v
  _ | p == v -> env
    | otherwise -> error $ "bindPat - pattern mismatch" ++ show (v,p)

lookupEnv :: Name -> Env -> Val
lookupEnv n env = Map.findWithDefault (error $ "missing variable: " ++ n) n env

lookupStore :: Int -> Store -> Val
lookupStore i s = IntMap.findWithDefault (error $ "missing location: " ++ show i) i s

evalVal :: Env -> Val -> Val
evalVal env = \case
  v@Lit{}     -> v
  Var n       -> lookupEnv n env
  TagNode t a -> TagNode t $ map (evalVal env) a
  VarNode n a -> case lookupEnv n env of
                  Var n     -> VarNode n $ map (evalVal env) a
                  ValTag t  -> TagNode t $ map (evalVal env) a
                  x -> error $ "evalVal - invalid VarNode tag: " ++ show x
  v@ValTag{}  -> v
  v@Unit      -> v
  v@Loc{}     -> v
  x -> error $ "evalVal: " ++ show x

evalSimpleExp :: Env -> SimpleExp -> GrinM Val
evalSimpleExp env = \case
  App n a -> do
              let args = map (evalVal env) a
                  go a [] [] = a
                  go a (x:xs) (y:ys) = go (Map.insert x y a) xs ys
                  go _ x y = error $ "invalid pattern for function: " ++ show (n,x,y)
              case n of
                "add" -> primAdd args
                "mul" -> primMul args
                "intPrint" -> primIntPrint args
                "intGT" -> primIntGT args
                "intAdd" -> primAdd args
                _ -> do
                  Def _ vars body <- reader $ Map.findWithDefault (error $ "unknown function: " ++ n) n
                  evalExp (go env vars args) body
  Return v -> return $ evalVal env v
  Store v -> do
              l <- gets IntMap.size
              let v' = evalVal env v
              modify' (IntMap.insert l v')
              return $ Loc l
  Fetch n -> case lookupEnv n env of
              Loc l -> gets $ lookupStore l
              x -> error $ "evalSimpleExp - Fetch expected location, got: " ++ show x
--  | FetchI  Name Int -- fetch node component
  Update n v -> do
              let v' = evalVal env v
              case lookupEnv n env of
                Loc l -> get >>= \s -> case IntMap.member l s of
                            False -> error $ "evalSimpleExp - Update unknown location: " ++ show l
                            True  -> modify' (IntMap.insert l v') >> return Unit
                x -> error $ "evalSimpleExp - Update expected location, got: " ++ show x
--  | Block   Exp
  x -> error $ "evalSimpleExp: " ++ show x

evalExp :: Env -> Exp -> GrinM Val
evalExp env = \case
  Bind op pat exp -> evalSimpleExp env op >>= \v -> evalExp (bindPat env v pat) exp
  Case v alts -> case evalVal env v of
    TagNode t l -> let (vars,exp) = head $ [(b,exp) | Alt (NodePat a b) exp <- alts, a == t] ++ error ("evalExp - missing Case Node alternative for: " ++ show t)
                       go a [] [] = a
                       go a (x:xs) (y:ys) = go (Map.insert x y a) xs ys
                       go _ x y = error $ "invalid pattern and constructor: " ++ show (t,x,y)
                   in  evalExp (go env vars l) exp
    ValTag t    -> evalExp env $ head $ [exp | Alt (TagPat a) exp <- alts, a == t] ++ error ("evalExp - missing Case Tag alternative for: " ++ show t)
    Lit l       -> evalExp env $ head $ [exp | Alt (LitPat a) exp <- alts, a == l] ++ error ("evalExp - missing Case Lit alternative for: " ++ show l)
    x -> error $ "evalExp - invalid Case dispatch value: " ++ show x
  SExp exp -> evalSimpleExp env exp
  x -> error $ "evalExp: " ++ show x

-- primitive functions
primIntGT [Lit (LFloat a), Lit (LFloat b)] = return $ ValTag $ Tag C (if a > b then "True" else "False") 0
primIntGT x = error $ "primIntGT - invalid arguments: " ++ show x

primIntPrint [Lit (LFloat a)] = return $ Lit $ LFloat $ a
primIntPrint x = error $ "primIntPrint - invalid arguments: " ++ show x

primAdd [Lit (LFloat a), Lit (LFloat b)] = return $ Lit $ LFloat $ a + b
primAdd x = error $ "primAdd - invalid arguments: " ++ show x

primMul [Lit (LFloat a), Lit (LFloat b)] = return $ Lit $ LFloat $ a * b
primMul x = error $ "primMul - invalid arguments: " ++ show x

reduce :: Exp -> Val
reduce e = evalState (runReaderT (evalExp mempty e) mempty) mempty

reduceFun :: [Def] -> String -> Val
reduceFun l n = evalState (runReaderT (evalExp mempty e) m) mempty where
  m = Map.fromList [(n,d) | d@(Def n _ _) <- l]
  e = case Map.lookup n m of
        Nothing -> error $ "missing function: " ++ n
        Just (Def _ [] a) -> a
        _ -> error $ "function " ++ n ++ " has arguments"
{-
TODO:
  done - execute GRIN (reduction)
  done - simple example: sum upto
  done - optimised example: sum upto
  - fast ST monad based interpreter
  - heap points to analysis
  - implement simplification transformations
      -- phase 1
      inlining calls to eval
      inlining calls to apply
      -- phase 2
      specialize update specialisation
      vectorisation
      case simplification
      -- phase 3
      split fetch operations
      right hoist fetch operations
      register introduction
  compile to GRIN
    - lambda lifting
    - generate eval
    - generate apply
-}
sadd = App "add" [Lit $ LFloat 3, Lit $ LFloat 2]
test = SExp sadd
test2 = Bind sadd (Var "a") $ SExp $ App "mul" [Var "a", Var "a"]

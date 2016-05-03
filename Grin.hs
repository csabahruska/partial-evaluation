{-# LANGUAGE LambdaCase #-}
module Grin where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Control.Monad.State

type Name = String

type Prog = Map Name Def

data Def = Def Name [Name] Exp

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
  | FetchI  Name Int -- fetch node component
  | Update  Name Val
  | Block   Exp
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
  deriving Show

data Lit = LFloat Float
  deriving Show

data Alt = Alt CPat Exp
  deriving Show

data CPat
  = NodePat Tag [Name]
  | TagPat  Tag
  | LitPat  Lit
  deriving Show

data TagType = C | F | P
  deriving Show

data Tag = Tag TagType Name Int
  deriving Show

{-
TODO:
  compile to GRIN
  execute GRIN (reduction)
-}
type Store = IntMap Val
type Env = Map Name Val
type GrinM = State Store

bind :: Env -> Val -> LPat -> Env
bind env v p = env -- TODO

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
  Unit        -> Unit
  v@Loc{}     -> v
  x -> error $ "evalVal: " ++ show x

evalSimpleExp :: Env -> SimpleExp -> GrinM Val
evalSimpleExp env = \case
--  = App     Name [SimpleVal]
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
  Bind op pat exp -> evalSimpleExp env op >>= \v -> evalExp (bind env v pat) exp
  -- | Case  Val [Alt]
  SExp exp -> evalSimpleExp env exp
  x -> error $ "evalExp: " ++ show x

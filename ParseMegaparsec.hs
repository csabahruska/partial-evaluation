{-# LANGUAGE TupleSections #-}

module Main where

import Control.Applicative (empty)
import Control.Monad (void)
import Text.Megaparsec
import Text.Megaparsec.String
import qualified Text.Megaparsec.Lexer as L
import Curry hiding (test)

lineComment :: Parser ()
lineComment = L.skipLineComment "--"

blockComment :: Parser ()
blockComment = L.skipBlockComment "{-" "-}"

sc :: Parser ()
sc = L.space (void spaceChar) lineComment blockComment

sc' :: Parser ()
sc' = L.space (void $ oneOf " \t") lineComment blockComment

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc'

symbol = L.symbol sc'
parens = between (symbol "(") (symbol ")")

kw w = L.symbol sc' w

op w = L.symbol sc' w

var :: Parser String
var = lexeme $ some (alphaNumChar)

lit :: Parser Lit
lit = LFloat <$ try L.float <|> LInt <$ L.integer

letin :: Parser Exp
letin = do
  (i,l) <- L.indentBlock sc $ do
    i <- L.indentLevel
    kw "let"
    return (L.IndentSome Nothing (return . (i,)) def)
  L.indentGuard sc (== i)
  kw "in"
  a <- expr
  return $ foldr ($) a l

def :: Parser (Exp -> Exp)
def = (\n a d e -> ELet n (foldr ELam (EBody d) a) e) <$> var <*> many var <* kw "=" <*> do L.indentLevel >>= \i -> L.indentGuard sc (>= i) >> expr

expr :: Parser Exp
expr = lam <|> letin <|> formula

formula = (\l -> foldl1 EApp l) <$> some atom

atom =
  (\f -> EPrimFun f) <$> primFun <|>
  (\l -> ELit l) <$> lit <|>
  (\v -> EVar v) <$> var <|>
--  (\p1 v p2 -> if length v == 1 then head v else ETuple (p1,p2) v) <$> getPosition <*> parens (commaSep expr) <*> getPosition <|>
  parens expr

primFun = PMulF <$ kw "mul" <|>
          PAddI <$ kw "add" <|>
          PAnd <$ kw "and"

lam :: Parser Exp
lam = (\n e -> ELam n e) <$ op "\\" <*> var <* op "->" <*> expr

test' = test "def02.lc"

test :: String -> IO ()
test fname = do
  result <- parseFromFile (expr <* sc <* eof) fname
  case result of
    Left err -> print err
    Right e  -> do
      print e
      case inference e of
        Right t   -> putStrLn $ show t
        Left m    -> putStrLn $ "error: " ++ m

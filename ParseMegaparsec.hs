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

{-
lcCommentStyle = haskellCommentStyle

lcIdents = haskell98Idents { _styleReserved = HashSet.fromList reservedIdents }
  where
    reservedIdents =
      [ "let"
      , "upper"
      , "in"
      , "add"
      , "show"
      , "read"
      ]
-}
kw w = L.symbol sc' w

op w = L.symbol sc' w

var :: Parser String
var = lexeme $ some (alphaNumChar)

lit :: Parser Lit
lit = LFloat <$ try L.float <|> LInt <$ L.integer <|> LChar <$ L.charLiteral

{-
pItemList = L.nonIndented sc (L.indentBlock sc p)
  where p = do
          header <- pItem
          return (L.IndentMany Nothing (return . (header, )) pItem)
-}
{-
letin :: Parser Exp
letin = L.indentBlock sc $ do 
  l <- kw "let" *> (localIndentation Gt $ localAbsoluteIndentation $ some def) -- WORKS
  a <- kw "in" *> (localIndentation Gt expr)
    return $ foldr ($) a l

def :: Parser (Exp -> Exp)
def = (\p1 n a d p2 e -> ELet (p1,p2) n (foldr (args (p1,p2)) d a) e) <$> getPosition <*> var <*> many var <* kw "=" <*> localIndentation Gt expr <*> getPosition
  where
    args r n e = ELam r n e
-}
expr :: Parser Exp
expr = lam <|> {-letin <|> -}formula

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

test' = test "example01.lc"

test :: String -> IO ()
test fname = do
  result <- parseFromFile (expr <* eof) fname
  case result of
    Left err -> print err
    Right e  -> do
      print e
      case inference e of
        Right t   -> putStrLn $ show t
        Left m    -> putStrLn $ "error: " ++ m

{-# LANGUAGE TupleSections #-}

module ParseMegaparsec where

import Data.Void
import Control.Applicative (empty)
import Control.Monad (void)
import Text.Megaparsec as L
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Curry hiding (test)
import ToReduce
import qualified Reduce as R
import qualified Data.Set as Set

type Parser = Parsec Void String

keywords = Set.fromList ["let","in","case","of"]

lineComment :: Parser ()
lineComment = L.skipLineComment "--"

blockComment :: Parser ()
blockComment = L.skipBlockCommentNested "{-" "-}"

sc :: Parser ()
sc = L.space (void spaceChar) lineComment blockComment

sc' :: Parser ()
sc' = L.space (void $ oneOf " \t") lineComment blockComment

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc'

symbol = L.symbol sc'
parens = between (symbol "(") (symbol ")")

kw w = lexeme $ string w

op w = L.symbol sc' w

var :: Parser String
var = try $ lexeme ((:) <$> lowerChar <*> many (alphaNumChar)) >>= \x -> case Set.member x keywords of
  True -> fail $ "keyword: " ++ x
  False -> return x

con :: Parser String
con = lexeme $ (:) <$> upperChar <*> many (alphaNumChar)

integer = lexeme L.decimal
signedInteger = L.signed sc' integer

float = lexeme L.float
signedFloat = L.signed sc' float

lit :: Parser Lit
lit = LFloat . realToFrac <$> try signedFloat <|> LFloat . fromIntegral <$> signedInteger

letin :: Parser Exp
letin = do
  (i,l) <- L.indentBlock sc $ do
    i <- L.indentLevel
    kw "let"
    return (L.IndentSome Nothing (return . (i,)) def)
  L.indentGuard sc EQ i
  kw "in"
  a <- expr
  return $ foldr ($) a l

def :: Parser (Exp -> Exp)
def = (\n a d e -> ELet n (foldr ELam (EBody d) a) e) <$> var <*> many var <*> (do L.indentLevel >>= \i -> kw "=" >> L.indentGuard sc GT i >> expr)

caseof :: Parser Exp
caseof = uncurry ECase <$> L.indentBlock sc (do
  kw "case"
  e <- expr
  kw "of"
  return (L.IndentSome Nothing (return . (e,)) pat))

pat :: Parser Pat
pat =
  PatCon <$> con <*> many var <* op "->" <*> expr <|>
  PatLit <$> lit <* op "->" <*> expr <|>
  PatWildcard <$ op "_" <* op "->" <*> expr

expr :: Parser Exp
expr = lam <|> try letin <|> try caseof <|> constr <|> formula

formula = foldl1 EApp <$> some atom
constr = ECon <$> con <*> many atom

atom =
  EPrimFun <$> primFun <|>
  ELit <$> lit <|>
  EVar <$> var <|>
  ECon <$> con <*> pure [] <|>
  parens expr

primFun = PMulF <$ kw "mul" <|>
          PAddI <$ kw "add" <|>
          PAnd <$ kw "and"

lam :: Parser Exp
lam = (\n e -> ELam n e) <$ op "\\" <*> var <* op "->" <*> expr

test' = test "def02.lc"

parseFromFile p file = runParser p file <$> readFile file

test :: String -> IO ()
test fname = do
  result <- parseFromFile (sc *> expr <* sc <* eof) fname
  case result of
    Left err -> print err
    Right e  -> do
      print e
      case inference e of
        Right t   -> putStrLn $ show t
        Left m    -> putStrLn $ "error: " ++ m

eval :: String -> IO ()
eval fname = do
  result <- parseFromFile (L.nonIndented sc expr <* sc <* eof) fname
  case result of
    Left err -> print err
    Right e  -> do
      --print e
      --putStrLn "-----------------"
      let exp = toExp' e
          re = R.runReduce exp
      print exp
      putStrLn "-----------------"
      print re
{-
      case inference e of
        Right t   -> do
                      --putStrLn $ show t
                      let exp = toExp t
                          re = R.runReduce exp
                      print exp
                      putStrLn "-----------------"
                      print re
        Left m    -> putStrLn $ "error: " ++ m
-}
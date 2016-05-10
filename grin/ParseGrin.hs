{-# LANGUAGE TupleSections #-}

module ParseGrin where

import Control.Applicative (empty)
import Control.Monad (void)
import Text.Megaparsec
import Text.Megaparsec.String
import qualified Text.Megaparsec.Lexer as L
import qualified Data.Set as Set
import Grin

keywords = Set.fromList ["case","of","return","fetch","store","update","if","then","else"]

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

kw w = lexeme $ string w

op w = L.symbol sc' w

var :: Parser String
var = try $ lexeme ((:) <$> lowerChar <*> many (alphaNumChar <|> oneOf "'_")) >>= \x -> case Set.member x keywords of
  True -> unexpected $ "keyword: " ++ x
  False -> return x

con :: Parser String
con = lexeme $ (:) <$> upperChar <*> many (alphaNumChar)

integer = lexeme L.integer
signedInteger = L.signed sc' integer

float = lexeme L.float
signedFloat = L.signed sc' float

-- grin syntax

def = Def <$> try (L.indentGuard sc (1 ==) *> var) <*> many var <* op "=" <*> (L.indentGuard sc (1 <) >>= expr)

expr i = L.indentGuard sc (i ==) >>
  (\pat e b -> Bind e pat b) <$> try (value <* op "<-") <*> simpleExp <*> expr i <|>
  Case <$ kw "case" <*> value <* kw "of" <*> (L.indentGuard sc (i <) >>= some . alternative) <|>
  ifThenElse i <|>
  try ((\n v e -> Bind (Update n v) Unit e) <$ kw "update" <*> var <*> value <*> expr i) <|>
  SExp <$> simpleExp

ifThenElse i = do
  kw "if"
  v <- value
  kw "then"
  t <- (L.indentGuard sc (i <) >>= expr)
  L.indentGuard sc (i ==)
  kw "else"
  e <- (L.indentGuard sc (i <) >>= expr)
  return $ Case v [ Alt (NodePat (Tag C "True"  0) []) t
                  , Alt (NodePat (Tag C "False" 0) []) e
                  ]

simpleExp = Return <$ kw "return" <*> value <|>
            Store <$ kw "store" <*> value <|>
            Fetch <$ kw "fetch" <*> var <|>
            Update <$ kw "update" <*> var <*> value <|>
            App <$> var <*> some simpleValue

alternative i = Alt <$> try (L.indentGuard sc (i ==) *> altPat) <* op "->" <*> (L.indentGuard sc (i <) >>= expr)

altPat = parens (NodePat <$> tag <*> many var) <|>
         TagPat <$> tag <|>
         LitPat <$> literal

--data Tag = Tag TagType Name Int
tag = Tag C <$> con <*> pure 0 -- TODO

simpleValue = Lit <$> literal <|>
              Var <$> var

value = Unit <$ op "()" <|>
        parens (TagNode <$> tag <*> many simpleValue) <|>
        parens (VarNode <$> var <*> many simpleValue) <|>
        ValTag <$> tag <|>
        simpleValue

literal :: Parser Lit
literal = LFloat . realToFrac <$> try signedFloat <|> LFloat . fromIntegral <$> signedInteger

eval :: String -> IO ()
eval fname = do
  result <- parseFromFile (some def <* sc <* eof) fname
  case result of
    Left err -> print err
    Right e  -> do
      print e

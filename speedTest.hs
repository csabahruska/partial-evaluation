import ParseMegaparsec
import System.Environment

main = do
  [n] <- getArgs
  eval n

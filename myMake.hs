module Main where

import System.Process (createProcess,shell)
import System.Environment (getArgs)
import Text.Parsec.Prim
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token 
import Control.Monad (void)

main :: IO ()
main = do
  args <- getArgs
  putStrLn $ show args
  contents <- readFile "makeFile"
  let lblist = either (error.show) id (parser (myTry $ many labelParser) contents)  
  if length args == 0 then
    mapM_ (\x-> createProcess $ shell x) (concat $ map cmds lblist)
    else do
    mapM_ (\x-> createProcess $ shell x) $ concat $ zipWith (\lb list -> (concat $ map cmds (filter (\x-> labelM x == lb) list))) args (repeat lblist)
    
  putStrLn $ "Compiled Successfully\n"

data MkLabel = Mk { labelM :: String,
                    cmds :: [String] } deriving (Eq,Show)
               
labelParser :: Parser MkLabel
labelParser = do
  var <- whiteSpace >> Token.identifier lexer
  char ':'
  eol
  cmdList <- many (myTry (whiteSpace >> (many1 (noneOf "\n:")) <* eol))
  return $ Mk var cmdList

myTry = Text.ParserCombinators.Parsec.try

languageDef :: LanguageDef ()
languageDef = emptyDef { Token.identStart = letter <|> satisfy (=='_')
                       , Token.identLetter = alphaNum
                       , Token.reservedNames = []
                       , Token.caseSensitive = True
                       }


lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser languageDef
eol :: Parser ()
eol = void (char '\n') <|> eof
reserved :: String -> Parser ()
reserved  = Token.reserved lexer
whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer
parser :: Parser a -> String -> Either ParseError a
parser p x = parse p "" x
                       

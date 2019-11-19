{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

import Text.ParserCombinators.ReadP;
import Prelude;
import Data.Char;

parseInt :: ReadP Int
parseInt = do
  n <- many1 $ satisfy isDigit
  return $ read n

(<++>) :: ReadP a -> ReadP b -> ReadP (a, b)
a <++> b = do
  x <- a
  y <- b
  return (x, y)


var_separator :: Char -> Bool
var_separator x = (x /= ';' && x /= ',' && x /= '*'  && x /= '-'  && x /= '+')

parseVar :: ReadP String
parseVar = many1 $ satisfy (var_separator)

parseSignedInt :: ReadP Int
parseSignedInt = do
  sgn <- option '+' (char '+' <++ char '-')
  n <- parseInt
  return $ if sgn == '+' then n else -n

parseIntDef :: Int -> ReadP Int
parseIntDef def = do
  n <- many $ satisfy isDigit
  return $ if n == [] then def else read n


parseSignedIntDef :: Int -> ReadP Int
parseSignedIntDef def = do
  sgn <- option '+' (char '+' <++ char '-')
  n <- parseIntDef def
  return $ if sgn == '+' then n else -n


parseVars :: ReadP [String]
parseVars = option [] (many (optional (string "*") *> parseVar))

parseMonom :: ReadP (Int, [String])
parseMonom =
  (parseIntDef 0 <++> (optional (string "*") *> parseVars))



main =
  putStrLn "hello, world"  
  
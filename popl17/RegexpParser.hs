{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

-- a quasiqoter for regular expressions
module RegexpParser(module Regexp, re) where


-- this QQ works with all three interfaces
-- because it generates the output at compile time
--import Regexp as Regexp
import RegexpDependent as Regexp

import Language.Haskell.TH hiding (match)
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import Instances.TH.Lift

import Text.Parsec hiding (void, Empty,char)
import qualified Text.Parsec as P
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad hiding (void,join)

import Data.Singletons (Sing(..), SingI(..))
import GHC.TypeLits
import Data.Proxy

import Data.List as List

data RegExp
  = Char (Set Char)    -- [a], [abc], [a-z]; matches a single character from the specified class
  | Alt RegExp RegExp  -- r1 | r2 (alternation); matches either r1 or r2
  | Seq RegExp RegExp  -- r1 r2 (concatenation); matches r1 followed by r2
  | Star RegExp        -- r* (Kleene star); matches r zero or more times
  | Empty              -- matches only the empty string
  | Void               -- matches nothing (always fails)
  | Var String         -- a variable holding another regexp (explained later)
  | Not (Set Char)
  | Any 
  | Mark String RegExp 
  deriving Show

rmaybe r = Alt Empty r

chars_whitespace = " \t\n\r\f\v"
chars_digit      = ['0' .. '9']
chars_word       = ('_':['a' .. 'z']++['A' .. 'Z']++['0' .. '9'])

------------------------------------------------
-- This is a *very* simplistic parser for regular expressions
type Parser = Parsec String ()
regexParser :: Parsec String () RegExp
regexParser = alts <* eof where
  atom       = try paren <|> try var <|> try dot <|> try esc_char <|> char
  paren      = P.char '(' *> alts <* P.char ')'
  var        = Var <$> (string "${" *> many1 (noneOf "}") <* P.char '}')
  dot        = return Any <* P.char '.'
  esc_char   =  (Char . Set.singleton) <$> try esc_char_p
            <|> (Char . Set.fromList <$> manychar)
  esc_char_p :: Parser Char
  esc_char_p = P.char '\\' >> 
                             (try (P.char 't' >> return '\t')
                          <|> try (P.char 'r' >> return '\r')
                          <|> try (P.char 'n' >> return '\n')
                          <|> try (oneOf specials))
  manychar :: Parser [Char]
  manychar   = P.char '\\' >>
                             (try (P.char 'd' >> return chars_digit)
                          <|> try (P.char 's' >> return chars_whitespace)
                          <|> (P.char 'w' >> return chars_word))
   
  char       = try charclass <|> singlechar
  singlechar = (Char . Set.singleton) <$> noneOf specials
  charclass  = P.char '[' >> ((Not  <$> try (P.char '^' *> enum))
                          <|> (Char <$> enum))
  enum       = Set.fromList <$> content <* P.char ']'
  content :: Parser [Char]
  content    = try (concat <$> many1 range)
                 <|> many1 charset
  charset :: Parser Char
  charset    = (try esc_char_p <|> noneOf "]") >>= \c -> do
                  when (c == '-') $ do
                    atEnd <- (P.lookAhead (P.char ']') >>
                              (return True)) <|> (return False)
                    when (not atEnd) $ P.unexpected "a dash must be last"
                  return c
  range      = enumFromTo
                 <$> (try esc_char_p <|> noneOf "]-" <* P.char '-')
                 <*> (try esc_char_p <|> noneOf "]") 
  alts       = try (Alt <$> seqs <*> (P.char '|' *> alts)) <|> seqs
  seqs       = try (Seq <$> star <*> seqs)                 <|> star
  star       = try (Star <$> (atom <* P.char '*'))         <|> maybe
  maybe      = try (rmaybe <$> (atom <* P.char '?'))        <|> mark
  mark       = try (Mark <$> (P.char '?' *> P.char 'P' *> P.char '<'
                                         *> many1 (noneOf ">") <* P.char '>')
                                        <*> alts)
               <|> atom
  specials   = ".[{}()\\*+?|^$" 

pp :: String -> Either ParseError RegExp
pp = runParser regexParser () "" 

--------------------------------------

re :: QuasiQuoter
re = QuasiQuoter {
    quoteExp  = compile
  , quotePat  = notHandled "patterns"
  , quoteType = notHandled "types"
  , quoteDec  = notHandled "declarations"
  }
  where notHandled things = error $
          things ++ " are not handled by the regex quasiquoter."
 
compile :: String -> Q Exp
compile s =
  case P.parse regexParser "" s of
    Left  err    -> fail (show err)
    Right regexp -> [e| regexp |]

--instance Lift a => Lift (Set a) where
--  lift set = appE (varE 'Set.fromList) (lift (Set.toList set))


  
instance Lift RegExp where
  -- lift :: RegExp -> Q Exp
  lift (Char cs)     = apply 'Rchar [lift cs]
  lift (Alt r1 r2)   = apply 'Ralt   (map lift [r1, r2])
  lift (Seq r1 r2)   = apply 'Rseq   (map lift [r1, r2])
  lift (Star r1)     = apply 'Rstar  (map lift [r1])
  lift Empty         = apply 'Rempty []
  lift Void          = return $ VarE 'rvoid
  lift Any           = apply 'Rany []
  lift (Not cs)       = apply 'Rnot [lift cs]
  lift (Mark s r)    = do e2 <- lift r
                          return $ AppE (AppE (VarE 'rmarkSing) p) e2 where
                             p = SigE (ConE 'Proxy) (AppT (ConT ''Proxy)
                                      (LitT (StrTyLit s)))
  lift (Var vars)    = foldl1 appE $ map (varE . mkName) (words vars)
 
apply :: Name -> [Q Exp] -> Q Exp
apply n = foldl appE (conE n)

------------------------------------------------------

-- Some higher-level regexp functions

{-
-- | Does this string start with the given regexp?
startsWith :: _ -> String -> Bool
startsWith r s = nullable r || not (null (fst (rinit r s)))

-- | Given r, split the string into the part that matches
-- r and the part that doesn't
rinit :: _ -> String -> (String, String)
rinit r (x:xs) = let r' = deriv r x in
                 if isVoid r' then ("", x:xs) else
                   case rinit r' xs of
                     (hd,tl) -> (x:hd, tl)                     
rinit r [] = ("","") 

ccons :: a -> [[a]] -> [[a]]
ccons x []     = (x:[]):[]
ccons x (y:ys) = (x:y) :ys

-- | Divide a string using r as a separator
split :: _ -> String -> [String]
split r [] = []
split r s@(x:xs) = case rinit r s of
  ("",_)  -> ccons x (split r xs)
  (ys,zs) -> [] : split r zs


-- | Does this string contain the given regexp
contains :: _ -> String -> Bool
contains r s = any (startsWith r) (List.tails s)
-}




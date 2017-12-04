module Sugar where

import Control.Monad (guard, liftM2)
import Data.Char (isLower, isUpper)
import Data.List (sortBy)
import Text.Parsec hiding (parse)
import Text.Parsec.Language
import qualified Text.Parsec.Token as T

import Core

parse :: String -> Either ParseError Core
parse = runParser (terminal (T.whiteSpace l >> exprp)) () ""


l = T.makeTokenParser $
    haskellDef { T.commentLine = "--"
               , T.reservedNames = ["True", "False", "if", "then", "else",
                                    "let", "in", "Int", "Bool",
                                    "case", "of", "Inl", "Inr"]
               , T.reservedOpNames = ["+", "*", "\\", "->", ":", ",", ";", "|"] }

terminal p = do x <- p
                eof
                return x
identifier = T.identifier l
reserved = T.reserved l
reservedOp = T.reservedOp l
parens = T.parens l
brackets = T.brackets l
lexeme = T.lexeme l
comma = T.comma l
commaSep = T.commaSep l

variable = try (do v <- identifier
                   guard (isLower (head v))
                   return v) <?> "identifier"

exprp = lamp

lamp = chainl1 lamp' (reservedOp ";" >> return CLetUnit)
    where lamp' = (do reservedOp "\\"
                      x <- identifier
                      reservedOp "->"
                      e <- exprp
                      return (CLam x e)) <|>
                  (do reserved "if"
                      e1 <- exprp
                      reserved "then"
                      e2 <- exprp
                      reserved "else"
                      e3 <- exprp
                      return (CIf e1 e2 e3)) <|>
                  try (do reserved "let"
                          x <- identifier
                          reservedOp "="
                          e1 <- exprp
                          reserved "in"
                          e2 <- exprp
                          return (CLet x e1 e2)) <|>
                 (do reserved "let"
                     reservedOp "("
                     x1 <- identifier
                     reservedOp ","
                     x2 <- identifier
                     reservedOp ")"
                     reservedOp "="
                     e1 <- exprp
                     reserved "in"
                     e2 <- exprp
                     return (CLetPair x1 x2 e1 e2)) <|>
                 (do reserved "case"
                     e <- exprp
                     reserved "of"
                     reserved "Inl"
                     x1 <- identifier
                     reservedOp "->"
                     e1 <- exprp
                     reservedOp "|"
                     reserved "Inr"
                     x2 <- identifier
                     reservedOp "->"
                     e2 <- exprp
                     return (CCase e (x1, e1) (x2, e2))) <|>
                  addp

addp = chainl1 multp ((reservedOp "+" >> return CAdd) <|>
                      (reservedOp "-" >> return (\e1 e2 -> CAdd e1 (CMult e2 (CInt (-1))))))

multp = chainl1 applp (reservedOp "*" >> return CMult)

applp = (do es <- many1 atomp
            case es of
              [CVar "isz", e] -> return (CIs0 e)
              (CVar "fix" : e : es) -> return (foldl CApp (CFix e) es)
              _ -> return (foldl1 CApp es))

atomp = choice [ CInt `fmap` lexeme intConst
               , CBool `fmap` boolConst
               , CVar `fmap` identifier
               , reserved "Inl" >> (CInl `fmap` exprp)
               , reserved "Inr" >> (CInr `fmap` exprp)
               , do es <- parens (commaSep exprp)
                    case es of
                      []  -> return CUnit
                      [e] -> return e
                      _   -> return (foldr1 CPair es)]

intConst = do ds <- many1 digit
              return (read ds)

boolConst = (reserved "True" >> return True) <|>
            (reserved "False" >> return False)

typep = chainr1 multyp (reservedOp "->" >> return CTFun)

addtyp = chainl1 multyp (reservedOp "+" >> return CTSum)

multyp = chainl1 atomtp (reservedOp "*" >> return CTProd)

atomtp = (reserved "Int" >> return CTInt) <|>
         (reserved "Bool" >> return CTBool) <|>
         (reserved "1" >> return CTOne) <|>
         parens typep

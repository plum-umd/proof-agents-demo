import Std.Internal.Parsec
import Semantics.Arithmetic.Syntax

namespace Semantics.Arithmetic

namespace Parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def token (p : Parser α) : Parser α :=
  ws *> p <* ws

def symbol (s : String) : Parser Unit :=
  token (skipString s)

def integer : Parser Int :=
  token do
    let negative ← (skipChar '-' *> pure true) <|> pure false
    let n ← digits
    return if negative then -Int.ofNat n else Int.ofNat n

mutual
  partial def expr : Parser Expr :=
    plus

  partial def plus : Parser Expr := do
    let lhs ← times
    plusRest lhs

  partial def plusRest (lhs : Expr) : Parser Expr :=
    (do
      symbol "+"
      let rhs ← times
      plusRest (.plus lhs rhs)) <|> pure lhs

  partial def times : Parser Expr := do
    let lhs ← unary
    timesRest lhs

  partial def timesRest (lhs : Expr) : Parser Expr :=
    (do
      symbol "*"
      let rhs ← unary
      timesRest (.times lhs rhs)) <|> pure lhs

  partial def unary : Parser Expr :=
    (do
      symbol "succ"
      return .succ (← unary)) <|>
    (do
      symbol "pred"
      return .pred (← unary)) <|>
    atom

  partial def atom : Parser Expr :=
    (return .int (← integer)) <|>
    (do
      symbol "("
      let e ← expr
      symbol ")"
      return e)
end

def parseExpr (input : String) : Except String Expr :=
  Parser.run (ws *> expr <* eof) input

def parsesAs (input : String) (expected : Expr) : Bool :=
  match parseExpr input with
  | .ok actual => actual == expected
  | .error _ => false

example : parsesAs "7" (.int 7) = true := by native_decide

example : parsesAs "succ 7" (.succ (.int 7)) = true := by native_decide

example : parsesAs "2 + 3 * pred 5" (.plus (.int 2) (.times (.int 3) (.pred (.int 5)))) =
    true := by native_decide

end Parser

end Semantics.Arithmetic

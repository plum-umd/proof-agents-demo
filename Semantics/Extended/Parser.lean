import Std.Internal.Parsec
import Semantics.Extended.Syntax

namespace Semantics.Extended

namespace Parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String

def token (p : Parser α) : Parser α :=
  ws *> p <* ws

def symbol (s : String) : Parser Unit :=
  token (skipString s)

def isIdentStart (c : Char) : Bool :=
  ('A' ≤ c ∧ c ≤ 'Z') || ('a' ≤ c ∧ c ≤ 'z') || c == '_'

def isIdentRest (c : Char) : Bool :=
  isIdentStart c || ('0' ≤ c ∧ c ≤ '9')

def keywordName : String → Bool
  | "true" => true
  | "false" => true
  | "if" => true
  | "then" => true
  | "else" => true
  | "let" => true
  | "in" => true
  | "succ" => true
  | "pred" => true
  | _ => false

def keyword (s : String) : Parser Unit :=
  token (attempt (skipString s *> notFollowedBy (satisfy isIdentRest)))

def identifier : Parser String :=
  token do
    let first ← satisfy isIdentStart
    let rest ← manyChars (satisfy isIdentRest)
    let name := first.toString ++ rest
    if keywordName name then
      fail s!"reserved word: {name}"
    else
      return name

def integer : Parser Int :=
  token do
    let negative ← (skipChar '-' *> pure true) <|> pure false
    let n ← digits
    return if negative then -Int.ofNat n else Int.ofNat n

mutual
  partial def expr : Parser Expr :=
    letExpr <|> ifExpr <|> equality

  partial def letExpr : Parser Expr := attempt do
    keyword "let"
    let x ← identifier
    symbol "="
    let rhs ← expr
    keyword "in"
    let body ← expr
    return .letE x rhs body

  partial def ifExpr : Parser Expr := attempt do
    keyword "if"
    let c ← expr
    keyword "then"
    let t ← expr
    keyword "else"
    let f ← expr
    return .ite c t f

  partial def equality : Parser Expr := do
    let lhs ← plus
    equalityRest lhs

  partial def equalityRest (lhs : Expr) : Parser Expr :=
    (do
      symbol "=="
      let rhs ← plus
      equalityRest (.numEq lhs rhs)) <|> pure lhs

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
      keyword "succ"
      return .succ (← unary)) <|>
    (do
      keyword "pred"
      return .pred (← unary)) <|>
    atom

  partial def atom : Parser Expr :=
    (do
      keyword "true"
      return .bool true) <|>
    (do
      keyword "false"
      return .bool false) <|>
    (return .int (← integer)) <|>
    (return .var (← identifier)) <|>
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

example : parsesAs "true" (.bool true) = true := by native_decide

example : parsesAs "x" (.var "x") = true := by native_decide

example : parsesAs "2 + 3 * pred 5" (.plus (.int 2) (.times (.int 3) (.pred (.int 5)))) =
    true := by native_decide

example : parsesAs "2 + 3 == 5" (.numEq (.plus (.int 2) (.int 3)) (.int 5)) =
    true := by native_decide

example : parsesAs "if 2 == 3 then 4 else 5"
    (.ite (.numEq (.int 2) (.int 3)) (.int 4) (.int 5)) = true := by native_decide

example : parsesAs "let x = 4 in x + 3" (.letE "x" (.int 4) (.plus (.var "x") (.int 3))) =
    true := by native_decide

end Parser

end Semantics.Extended

import Semantics.Extended.Definitional
import Semantics.Extended.Parser

open Semantics.Extended

def usage : String :=
  "usage: semantics EXPR\nexample: semantics \"let x = 4 in if x == 4 then succ x else 0\""

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln usage
      return 1
  | parts =>
      let input := String.intercalate " " parts
      match Parser.parseExpr input with
      | .ok e =>
          match denote e with
          | some v =>
              IO.println s!"{v}"
              return 0
          | none =>
              IO.eprintln "runtime type error"
              return 1
      | .error msg =>
          IO.eprintln s!"parse error: {msg}"
          return 1

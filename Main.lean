import Semantics.Definitional
import Semantics.Parser

open Semantics

def usage : String :=
  "usage: semantics EXPR\nexample: semantics \"succ (2 + 3) * pred 5\""

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln usage
      return 1
  | parts =>
      let input := String.intercalate " " parts
      match Parser.parseExpr input with
      | .ok e =>
          IO.println s!"{denote e}"
          return 0
      | .error msg =>
          IO.eprintln s!"parse error: {msg}"
          return 1

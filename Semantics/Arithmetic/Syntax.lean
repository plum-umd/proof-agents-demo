namespace Semantics.Arithmetic

inductive Expr where
  | int : Int → Expr
  | succ : Expr → Expr
  | pred : Expr → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr, DecidableEq

end Semantics.Arithmetic

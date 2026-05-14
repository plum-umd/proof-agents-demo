namespace Semantics.Extended

inductive Expr where
  | int : Int → Expr
  | bool : Bool → Expr
  | var : String → Expr
  | succ : Expr → Expr
  | pred : Expr → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  | numEq : Expr → Expr → Expr
  | ite : Expr → Expr → Expr → Expr
  | letE : String → Expr → Expr → Expr
  deriving Repr, DecidableEq

end Semantics.Extended

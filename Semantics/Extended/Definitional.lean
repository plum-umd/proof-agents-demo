import Semantics.Extended.Syntax

namespace Semantics.Extended

inductive Value where
  | int : Int → Value
  | bool : Bool → Value
  deriving Repr, DecidableEq

instance : ToString Value where
  toString
    | .int n => toString n
    | .bool true => "true"
    | .bool false => "false"

abbrev Env := List (String × Value)

def Env.lookup (ρ : Env) (x : String) : Option Value :=
  match ρ with
  | [] => none
  | (y, v) :: ρ => if x == y then some v else lookup ρ x

def Env.extend (ρ : Env) (x : String) (v : Value) : Env :=
  (x, v) :: ρ

def eval (ρ : Env) : Expr → Option Value
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | .var x => ρ.lookup x
  | .succ e =>
      match eval ρ e with
      | some (.int n) => some (.int (n + 1))
      | _ => none
  | .pred e =>
      match eval ρ e with
      | some (.int n) => some (.int (n - 1))
      | _ => none
  | .plus e₁ e₂ =>
      match eval ρ e₁, eval ρ e₂ with
      | some (.int n₁), some (.int n₂) => some (.int (n₁ + n₂))
      | _, _ => none
  | .times e₁ e₂ =>
      match eval ρ e₁, eval ρ e₂ with
      | some (.int n₁), some (.int n₂) => some (.int (n₁ * n₂))
      | _, _ => none
  | .numEq e₁ e₂ =>
      match eval ρ e₁, eval ρ e₂ with
      | some (.int n₁), some (.int n₂) => some (.bool (n₁ == n₂))
      | _, _ => none
  | .ite e₁ e₂ e₃ =>
      match eval ρ e₁ with
      | some (.bool true) => eval ρ e₂
      | some (.bool false) => eval ρ e₃
      | _ => none
  | .letE x e₁ e₂ =>
      match eval ρ e₁ with
      | some v => eval (ρ.extend x v) e₂
      | none => none

def denote (e : Expr) : Option Value :=
  eval [] e

example : denote (.int 7) = some (.int 7) := rfl

example : denote (.bool true) = some (.bool true) := rfl

example : denote (.succ (.int 7)) = some (.int 8) := rfl

example : denote (.plus (.int 2) (.int 3)) = some (.int 5) := rfl

example : denote (.numEq (.plus (.int 2) (.int 3)) (.int 5)) = some (.bool true) := rfl

example : denote (.ite (.bool true) (.int 1) (.int 2)) = some (.int 1) := rfl

example : denote (.letE "x" (.int 4) (.plus (.var "x") (.int 3))) = some (.int 7) := rfl

example : denote (.succ (.bool true)) = none := rfl

example : denote (.var "x") = none := rfl

end Semantics.Extended

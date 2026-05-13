import Semantics.Syntax

namespace Semantics

def denote : Expr → Int
  | .int n => n
  | .succ e => denote e + 1
  | .pred e => denote e - 1
  | .plus e₁ e₂ => denote e₁ + denote e₂
  | .times e₁ e₂ => denote e₁ * denote e₂

example : denote (.int 7) = 7 := rfl

example : denote (.succ (.int 7)) = 8 := rfl

example : denote (.pred (.int 7)) = 6 := rfl

example : denote (.plus (.int 2) (.int 3)) = 5 := rfl

example : denote (.times (.plus (.int 2) (.int 3)) (.pred (.int 5))) = 20 := rfl

end Semantics

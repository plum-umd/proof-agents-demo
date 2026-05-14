import Semantics.Extended.SmallStep

namespace Semantics.Extended

inductive EvalContext where
  | hole : EvalContext
  | succ : EvalContext → EvalContext
  | pred : EvalContext → EvalContext
  | plus_left : EvalContext → Expr → EvalContext
  | plus_right_int : Int → EvalContext → EvalContext
  | plus_right_bool : Bool → EvalContext → EvalContext
  | times_left : EvalContext → Expr → EvalContext
  | times_right_int : Int → EvalContext → EvalContext
  | times_right_bool : Bool → EvalContext → EvalContext
  | numEq_left : EvalContext → Expr → EvalContext
  | numEq_right_int : Int → EvalContext → EvalContext
  | numEq_right_bool : Bool → EvalContext → EvalContext
  | ite : EvalContext → Expr → Expr → EvalContext
  | letE : String → EvalContext → Expr → EvalContext
  deriving Repr, DecidableEq

def EvalContext.plug : EvalContext → Expr → Expr
  | .hole, e => e
  | .succ c, e => .succ (plug c e)
  | .pred c, e => .pred (plug c e)
  | .plus_left c e₂, e => .plus (plug c e) e₂
  | .plus_right_int n₁ c, e => .plus (.int n₁) (plug c e)
  | .plus_right_bool b₁ c, e => .plus (.bool b₁) (plug c e)
  | .times_left c e₂, e => .times (plug c e) e₂
  | .times_right_int n₁ c, e => .times (.int n₁) (plug c e)
  | .times_right_bool b₁ c, e => .times (.bool b₁) (plug c e)
  | .numEq_left c e₂, e => .numEq (plug c e) e₂
  | .numEq_right_int n₁ c, e => .numEq (.int n₁) (plug c e)
  | .numEq_right_bool b₁ c, e => .numEq (.bool b₁) (plug c e)
  | .ite c e₂ e₃, e => .ite (plug c e) e₂ e₃
  | .letE x c e₂, e => .letE x (plug c e) e₂

inductive Contract : Expr → Expr → Prop where
  | succ : Contract (.succ (.int n)) (.int (n + 1))
  | pred : Contract (.pred (.int n)) (.int (n - 1))
  | plus : Contract (.plus (.int n₁) (.int n₂)) (.int (n₁ + n₂))
  | times : Contract (.times (.int n₁) (.int n₂)) (.int (n₁ * n₂))
  | numEq : Contract (.numEq (.int n₁) (.int n₂)) (.bool (n₁ == n₂))
  | ite_true : Contract (.ite (.bool true) e₂ e₃) e₂
  | ite_false : Contract (.ite (.bool false) e₂ e₃) e₃
  | let_int : Contract (.letE x (.int n) e) (substValue x (.int n) e)
  | let_bool : Contract (.letE x (.bool b) e) (substValue x (.bool b) e)

inductive Reduce : Expr → Expr → Prop where
  | in_context :
      Contract r r' →
      Reduce (EvalContext.plug c r) (EvalContext.plug c r')

theorem EvalContext.lift_step (c : EvalContext) : Step e e' → Step (c.plug e) (c.plug e') := by
  intro h
  induction c with
  | hole =>
      exact h
  | succ c ih =>
      exact Step.succ_step ih
  | pred c ih =>
      exact Step.pred_step ih
  | plus_left c e₂ ih =>
      exact Step.plus_left ih
  | plus_right_int n₁ c ih =>
      exact Step.plus_right IsValue.int ih
  | plus_right_bool b₁ c ih =>
      exact Step.plus_right IsValue.bool ih
  | times_left c e₂ ih =>
      exact Step.times_left ih
  | times_right_int n₁ c ih =>
      exact Step.times_right IsValue.int ih
  | times_right_bool b₁ c ih =>
      exact Step.times_right IsValue.bool ih
  | numEq_left c e₂ ih =>
      exact Step.numEq_left ih
  | numEq_right_int n₁ c ih =>
      exact Step.numEq_right IsValue.int ih
  | numEq_right_bool b₁ c ih =>
      exact Step.numEq_right IsValue.bool ih
  | ite c e₂ e₃ ih =>
      exact Step.ite_cond ih
  | letE x c e₂ ih =>
      exact Step.let_step ih

theorem Contract.step : Contract e e' → Step e e' := by
  intro h
  cases h with
  | succ => exact Step.succ
  | pred => exact Step.pred
  | plus => exact Step.plus
  | times => exact Step.times
  | numEq => exact Step.numEq
  | ite_true => exact Step.ite_true
  | ite_false => exact Step.ite_false
  | let_int => exact Step.let_int
  | let_bool => exact Step.let_bool

theorem Reduce.step : Reduce e e' → Step e e' := by
  intro h
  cases h with
  | in_context hcontract =>
      exact EvalContext.lift_step _ hcontract.step

theorem Step.reduce : Step e e' → Reduce e e' := by
  intro h
  induction h with
  | succ =>
      exact Reduce.in_context (c := .hole) Contract.succ
  | pred =>
      exact Reduce.in_context (c := .hole) Contract.pred
  | plus =>
      exact Reduce.in_context (c := .hole) Contract.plus
  | times =>
      exact Reduce.in_context (c := .hole) Contract.times
  | numEq =>
      exact Reduce.in_context (c := .hole) Contract.numEq
  | ite_true =>
      exact Reduce.in_context (c := .hole) Contract.ite_true
  | ite_false =>
      exact Reduce.in_context (c := .hole) Contract.ite_false
  | let_int =>
      exact Reduce.in_context (c := .hole) Contract.let_int
  | let_bool =>
      exact Reduce.in_context (c := .hole) Contract.let_bool
  | succ_step _ ih =>
      cases ih with
      | in_context hcontract =>
          exact Reduce.in_context (c := .succ _) hcontract
  | pred_step _ ih =>
      cases ih with
      | in_context hcontract =>
          exact Reduce.in_context (c := .pred _) hcontract
  | plus_left _ ih =>
      cases ih with
      | in_context hcontract =>
          exact Reduce.in_context (c := .plus_left _ _) hcontract
  | plus_right hv _ ih =>
      cases ih with
      | in_context hcontract =>
          cases hv with
          | int =>
              exact Reduce.in_context (c := .plus_right_int _ _) hcontract
          | bool =>
              exact Reduce.in_context (c := .plus_right_bool _ _) hcontract
  | times_left _ ih =>
      cases ih with
      | in_context hcontract =>
          exact Reduce.in_context (c := .times_left _ _) hcontract
  | times_right hv _ ih =>
      cases ih with
      | in_context hcontract =>
          cases hv with
          | int =>
              exact Reduce.in_context (c := .times_right_int _ _) hcontract
          | bool =>
              exact Reduce.in_context (c := .times_right_bool _ _) hcontract
  | numEq_left _ ih =>
      cases ih with
      | in_context hcontract =>
          exact Reduce.in_context (c := .numEq_left _ _) hcontract
  | numEq_right hv _ ih =>
      cases ih with
      | in_context hcontract =>
          cases hv with
          | int =>
              exact Reduce.in_context (c := .numEq_right_int _ _) hcontract
          | bool =>
              exact Reduce.in_context (c := .numEq_right_bool _ _) hcontract
  | ite_cond _ ih =>
      cases ih with
      | in_context hcontract =>
          exact Reduce.in_context (c := .ite _ _ _) hcontract
  | let_step _ ih =>
      cases ih with
      | in_context hcontract =>
          exact Reduce.in_context (c := .letE _ _ _) hcontract

theorem Reduce.iff_step : Reduce e e' ↔ Step e e' :=
  ⟨Reduce.step, Step.reduce⟩

def ReduceEval (e : Expr) (v : Value) : Prop :=
  Steps e v.toExpr

theorem ReduceEval.iff_StepEval : ReduceEval e v ↔ StepEval e v :=
  Iff.rfl

theorem ReduceEval.iff_Eval : ReduceEval e v ↔ Eval [] e v :=
  StepEval.iff_Eval

example :
    Reduce (.plus (.int 1) (.plus (.int 2) (.int 3))) (.plus (.int 1) (.int 5)) :=
  Reduce.in_context (c := .plus_right_int 1 .hole) Contract.plus

example :
    Reduce (.letE "x" (.plus (.int 1) (.int 2)) (.succ (.var "x")))
      (.letE "x" (.int 3) (.succ (.var "x"))) :=
  Reduce.in_context (c := .letE "x" .hole (.succ (.var "x"))) Contract.plus

example :
    Reduce (.letE "x" (.int 3) (.succ (.var "x"))) (.succ (.int 3)) :=
  Reduce.in_context (c := .hole) Contract.let_int

end Semantics.Extended

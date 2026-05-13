import Semantics.SmallStep

namespace Semantics

inductive Context where
  | hole : Context
  | succ : Context → Context
  | pred : Context → Context
  | plus_left : Context → Expr → Context
  | plus_right : Expr → Context → Context
  | times_left : Context → Expr → Context
  | times_right : Expr → Context → Context
  deriving Repr, DecidableEq

inductive EvalContext where
  | hole : EvalContext
  | succ : EvalContext → EvalContext
  | pred : EvalContext → EvalContext
  | plus_left : EvalContext → Expr → EvalContext
  | plus_right : Int → EvalContext → EvalContext
  | times_left : EvalContext → Expr → EvalContext
  | times_right : Int → EvalContext → EvalContext
  deriving Repr, DecidableEq

inductive EvalFrame where
  | succ : EvalFrame
  | pred : EvalFrame
  | plus_left : Expr → EvalFrame
  | plus_right : Int → EvalFrame
  | times_left : Expr → EvalFrame
  | times_right : Int → EvalFrame
  deriving Repr, DecidableEq

abbrev InsideOutContext :=
  List EvalFrame

inductive Plug : Context → Expr → Expr → Prop where
  | hole : Plug .hole e e
  | succ : Plug c e e' → Plug (.succ c) e (.succ e')
  | pred : Plug c e e' → Plug (.pred c) e (.pred e')
  | plus_left : Plug c e e' → Plug (.plus_left c e₂) e (.plus e' e₂)
  | plus_right : Plug c e e' → Plug (.plus_right e₁ c) e (.plus e₁ e')
  | times_left : Plug c e e' → Plug (.times_left c e₂) e (.times e' e₂)
  | times_right : Plug c e e' → Plug (.times_right e₁ c) e (.times e₁ e')

inductive EvalPlug : EvalContext → Expr → Expr → Prop where
  | hole : EvalPlug .hole e e
  | succ : EvalPlug c e e' → EvalPlug (.succ c) e (.succ e')
  | pred : EvalPlug c e e' → EvalPlug (.pred c) e (.pred e')
  | plus_left : EvalPlug c e e' → EvalPlug (.plus_left c e₂) e (.plus e' e₂)
  | plus_right : EvalPlug c e e' → EvalPlug (.plus_right n₁ c) e (.plus (.int n₁) e')
  | times_left : EvalPlug c e e' → EvalPlug (.times_left c e₂) e (.times e' e₂)
  | times_right : EvalPlug c e e' → EvalPlug (.times_right n₁ c) e (.times (.int n₁) e')

inductive Contract : Expr → Expr → Prop where
  | succ_int : Contract (.succ (.int n)) (.int (n + 1))
  | pred_int : Contract (.pred (.int n)) (.int (n - 1))
  | plus_int : Contract (.plus (.int n₁) (.int n₂)) (.int (n₁ + n₂))
  | times_int : Contract (.times (.int n₁) (.int n₂)) (.int (n₁ * n₂))

inductive Reduce : Expr → Expr → Prop where
  | context :
      Plug c e₁ whole₁ →
      Contract e₁ e₂ →
      Plug c e₂ whole₂ →
      Reduce whole₁ whole₂

inductive StandardReduce : Expr → Expr → Prop where
  | context :
      EvalPlug c e₁ whole₁ →
      Contract e₁ e₂ →
      EvalPlug c e₂ whole₂ →
      StandardReduce whole₁ whole₂

inductive ReduceSteps : Expr → Expr → Prop where
  | refl : ReduceSteps e e
  | step : Reduce e₁ e₂ → ReduceSteps e₂ e₃ → ReduceSteps e₁ e₃

inductive StandardReduceSteps : Expr → Expr → Prop where
  | refl : StandardReduceSteps e e
  | step : StandardReduce e₁ e₂ → StandardReduceSteps e₂ e₃ → StandardReduceSteps e₁ e₃

def EvalReduce (e : Expr) (n : Int) : Prop :=
  ReduceSteps e (.int n)

def EvalStandardReduce (e : Expr) (n : Int) : Prop :=
  StandardReduceSteps e (.int n)

def contract : Expr → Option Expr
  | .succ (.int n) => some (.int (n + 1))
  | .pred (.int n) => some (.int (n - 1))
  | .plus (.int n₁) (.int n₂) => some (.int (n₁ + n₂))
  | .times (.int n₁) (.int n₂) => some (.int (n₁ * n₂))
  | _ => none

def plug : EvalContext → Expr → Expr
  | .hole, e => e
  | .succ c, e => .succ (plug c e)
  | .pred c, e => .pred (plug c e)
  | .plus_left c e₂, e => .plus (plug c e) e₂
  | .plus_right n₁ c, e => .plus (.int n₁) (plug c e)
  | .times_left c e₂, e => .times (plug c e) e₂
  | .times_right n₁ c, e => .times (.int n₁) (plug c e)

def plugFrame : EvalFrame → Expr → Expr
  | .succ, e => .succ e
  | .pred, e => .pred e
  | .plus_left e₂, e => .plus e e₂
  | .plus_right n₁, e => .plus (.int n₁) e
  | .times_left e₂, e => .times e e₂
  | .times_right n₁, e => .times (.int n₁) e

def plugInsideOut (c : InsideOutContext) (e : Expr) : Expr :=
  c.foldl (fun e frame => plugFrame frame e) e

def decompose : Expr → Option (EvalContext × Expr)
  | .int _ => none
  | .succ (.int n) => some (.hole, .succ (.int n))
  | .succ e =>
      match decompose e with
      | some (c, redex) => some (.succ c, redex)
      | none => none
  | .pred (.int n) => some (.hole, .pred (.int n))
  | .pred e =>
      match decompose e with
      | some (c, redex) => some (.pred c, redex)
      | none => none
  | .plus (.int n₁) (.int n₂) => some (.hole, .plus (.int n₁) (.int n₂))
  | .plus (.int n₁) e₂ =>
      match decompose e₂ with
      | some (c, redex) => some (.plus_right n₁ c, redex)
      | none => none
  | .plus e₁ e₂ =>
      match decompose e₁ with
      | some (c, redex) => some (.plus_left c e₂, redex)
      | none => none
  | .times (.int n₁) (.int n₂) => some (.hole, .times (.int n₁) (.int n₂))
  | .times (.int n₁) e₂ =>
      match decompose e₂ with
      | some (c, redex) => some (.times_right n₁ c, redex)
      | none => none
  | .times e₁ e₂ =>
      match decompose e₁ with
      | some (c, redex) => some (.times_left c e₂, redex)
      | none => none

mutual
  partial def decompose' : Expr → InsideOutContext → Expr
    | .int n, c => plug' (.int n) c
    | .succ (.int n), c => decompose' (.int (n + 1)) c
    | .succ e, c => decompose' e (.succ :: c)
    | .pred (.int n), c => decompose' (.int (n - 1)) c
    | .pred e, c => decompose' e (.pred :: c)
    | .plus (.int n₁) (.int n₂), c => decompose' (.int (n₁ + n₂)) c
    | .plus (.int n₁) e₂, c => decompose' e₂ (.plus_right n₁ :: c)
    | .plus e₁ e₂, c => decompose' e₁ (.plus_left e₂ :: c)
    | .times (.int n₁) (.int n₂), c => decompose' (.int (n₁ * n₂)) c
    | .times (.int n₁) e₂, c => decompose' e₂ (.times_right n₁ :: c)
    | .times e₁ e₂, c => decompose' e₁ (.times_left e₂ :: c)

  partial def plug' : Expr → InsideOutContext → Expr
    | e, [] => e
    | e, .succ :: c => decompose' (.succ e) c
    | e, .pred :: c => decompose' (.pred e) c
    | e, .plus_left e₂ :: c => decompose' (.plus e e₂) c
    | e, .plus_right n₁ :: c => decompose' (.plus (.int n₁) e) c
    | e, .times_left e₂ :: c => decompose' (.times e e₂) c
    | e, .times_right n₁ :: c => decompose' (.times (.int n₁) e) c
end

def eval_reduce' (e : Expr) : Expr :=
  decompose' e []

inductive MachineState where
  | decompose : Expr → InsideOutContext → MachineState
  | plug : Expr → InsideOutContext → MachineState
  deriving Repr, DecidableEq

inductive MachineStep : MachineState → MachineState → Prop where
  | decompose_int :
      MachineStep (.decompose (.int n) c) (.plug (.int n) c)
  | decompose_succ_int :
      MachineStep (.decompose (.succ (.int n)) c) (.decompose (.int (n + 1)) c)
  | decompose_succ_succ :
      MachineStep (.decompose (.succ (.succ e)) c) (.decompose (.succ e) (.succ :: c))
  | decompose_succ_pred :
      MachineStep (.decompose (.succ (.pred e)) c) (.decompose (.pred e) (.succ :: c))
  | decompose_succ_plus :
      MachineStep (.decompose (.succ (.plus e₁ e₂)) c) (.decompose (.plus e₁ e₂) (.succ :: c))
  | decompose_succ_times :
      MachineStep (.decompose (.succ (.times e₁ e₂)) c) (.decompose (.times e₁ e₂) (.succ :: c))
  | decompose_pred_int :
      MachineStep (.decompose (.pred (.int n)) c) (.decompose (.int (n - 1)) c)
  | decompose_pred_succ :
      MachineStep (.decompose (.pred (.succ e)) c) (.decompose (.succ e) (.pred :: c))
  | decompose_pred_pred :
      MachineStep (.decompose (.pred (.pred e)) c) (.decompose (.pred e) (.pred :: c))
  | decompose_pred_plus :
      MachineStep (.decompose (.pred (.plus e₁ e₂)) c) (.decompose (.plus e₁ e₂) (.pred :: c))
  | decompose_pred_times :
      MachineStep (.decompose (.pred (.times e₁ e₂)) c) (.decompose (.times e₁ e₂) (.pred :: c))
  | decompose_plus_int :
      MachineStep
        (.decompose (.plus (.int n₁) (.int n₂)) c)
        (.decompose (.int (n₁ + n₂)) c)
  | decompose_plus_right_succ :
      MachineStep
        (.decompose (.plus (.int n₁) (.succ e₂)) c)
        (.decompose (.succ e₂) (.plus_right n₁ :: c))
  | decompose_plus_right_pred :
      MachineStep
        (.decompose (.plus (.int n₁) (.pred e₂)) c)
        (.decompose (.pred e₂) (.plus_right n₁ :: c))
  | decompose_plus_right_plus :
      MachineStep
        (.decompose (.plus (.int n₁) (.plus e₂₁ e₂₂)) c)
        (.decompose (.plus e₂₁ e₂₂) (.plus_right n₁ :: c))
  | decompose_plus_right_times :
      MachineStep
        (.decompose (.plus (.int n₁) (.times e₂₁ e₂₂)) c)
        (.decompose (.times e₂₁ e₂₂) (.plus_right n₁ :: c))
  | decompose_plus_left_succ :
      MachineStep
        (.decompose (.plus (.succ e₁) e₂) c)
        (.decompose (.succ e₁) (.plus_left e₂ :: c))
  | decompose_plus_left_pred :
      MachineStep
        (.decompose (.plus (.pred e₁) e₂) c)
        (.decompose (.pred e₁) (.plus_left e₂ :: c))
  | decompose_plus_left_plus :
      MachineStep
        (.decompose (.plus (.plus e₁₁ e₁₂) e₂) c)
        (.decompose (.plus e₁₁ e₁₂) (.plus_left e₂ :: c))
  | decompose_plus_left_times :
      MachineStep
        (.decompose (.plus (.times e₁₁ e₁₂) e₂) c)
        (.decompose (.times e₁₁ e₁₂) (.plus_left e₂ :: c))
  | decompose_times_int :
      MachineStep
        (.decompose (.times (.int n₁) (.int n₂)) c)
        (.decompose (.int (n₁ * n₂)) c)
  | decompose_times_right_succ :
      MachineStep
        (.decompose (.times (.int n₁) (.succ e₂)) c)
        (.decompose (.succ e₂) (.times_right n₁ :: c))
  | decompose_times_right_pred :
      MachineStep
        (.decompose (.times (.int n₁) (.pred e₂)) c)
        (.decompose (.pred e₂) (.times_right n₁ :: c))
  | decompose_times_right_plus :
      MachineStep
        (.decompose (.times (.int n₁) (.plus e₂₁ e₂₂)) c)
        (.decompose (.plus e₂₁ e₂₂) (.times_right n₁ :: c))
  | decompose_times_right_times :
      MachineStep
        (.decompose (.times (.int n₁) (.times e₂₁ e₂₂)) c)
        (.decompose (.times e₂₁ e₂₂) (.times_right n₁ :: c))
  | decompose_times_left_succ :
      MachineStep
        (.decompose (.times (.succ e₁) e₂) c)
        (.decompose (.succ e₁) (.times_left e₂ :: c))
  | decompose_times_left_pred :
      MachineStep
        (.decompose (.times (.pred e₁) e₂) c)
        (.decompose (.pred e₁) (.times_left e₂ :: c))
  | decompose_times_left_plus :
      MachineStep
        (.decompose (.times (.plus e₁₁ e₁₂) e₂) c)
        (.decompose (.plus e₁₁ e₁₂) (.times_left e₂ :: c))
  | decompose_times_left_times :
      MachineStep
        (.decompose (.times (.times e₁₁ e₁₂) e₂) c)
        (.decompose (.times e₁₁ e₁₂) (.times_left e₂ :: c))
  | plug_succ :
      MachineStep (.plug e (.succ :: c)) (.decompose (.succ e) c)
  | plug_pred :
      MachineStep (.plug e (.pred :: c)) (.decompose (.pred e) c)
  | plug_plus_left :
      MachineStep (.plug e (.plus_left e₂ :: c)) (.decompose (.plus e e₂) c)
  | plug_plus_right :
      MachineStep (.plug e (.plus_right n₁ :: c)) (.decompose (.plus (.int n₁) e) c)
  | plug_times_left :
      MachineStep (.plug e (.times_left e₂ :: c)) (.decompose (.times e e₂) c)
  | plug_times_right :
      MachineStep (.plug e (.times_right n₁ :: c)) (.decompose (.times (.int n₁) e) c)

inductive MachineSteps : MachineState → MachineState → Prop where
  | refl : MachineSteps s s
  | step : MachineStep s₁ s₂ → MachineSteps s₂ s₃ → MachineSteps s₁ s₃

def MachineEval (e : Expr) (n : Int) : Prop :=
  MachineSteps (.decompose e []) (.plug (.int n) [])

def machine_step : MachineState → Option MachineState
  | .decompose (.int n) c => some (.plug (.int n) c)
  | .decompose (.succ (.int n)) c => some (.decompose (.int (n + 1)) c)
  | .decompose (.succ e) c => some (.decompose e (.succ :: c))
  | .decompose (.pred (.int n)) c => some (.decompose (.int (n - 1)) c)
  | .decompose (.pred e) c => some (.decompose e (.pred :: c))
  | .decompose (.plus (.int n₁) (.int n₂)) c => some (.decompose (.int (n₁ + n₂)) c)
  | .decompose (.plus (.int n₁) e₂) c => some (.decompose e₂ (.plus_right n₁ :: c))
  | .decompose (.plus e₁ e₂) c => some (.decompose e₁ (.plus_left e₂ :: c))
  | .decompose (.times (.int n₁) (.int n₂)) c => some (.decompose (.int (n₁ * n₂)) c)
  | .decompose (.times (.int n₁) e₂) c => some (.decompose e₂ (.times_right n₁ :: c))
  | .decompose (.times e₁ e₂) c => some (.decompose e₁ (.times_left e₂ :: c))
  | .plug _ [] => none
  | .plug e (.succ :: c) => some (.decompose (.succ e) c)
  | .plug e (.pred :: c) => some (.decompose (.pred e) c)
  | .plug e (.plus_left e₂ :: c) => some (.decompose (.plus e e₂) c)
  | .plug e (.plus_right n₁ :: c) => some (.decompose (.plus (.int n₁) e) c)
  | .plug e (.times_left e₂ :: c) => some (.decompose (.times e e₂) c)
  | .plug e (.times_right n₁ :: c) => some (.decompose (.times (.int n₁) e) c)

def run_machine : Nat → MachineState → MachineState
  | 0, s => s
  | fuel + 1, s =>
      match machine_step s with
      | some s' => run_machine fuel s'
      | none => s

def run_machine_for : Nat → MachineState → Option MachineState
  | 0, s => some s
  | fuel + 1, s =>
      match machine_step s with
      | some s' => run_machine_for fuel s'
      | none => none

def eval_machine (fuel : Nat) (e : Expr) : Expr :=
  match run_machine fuel (.decompose e []) with
  | .plug result [] => result
  | .decompose result [] => result
  | .decompose result stack => plugInsideOut stack result
  | .plug result stack => plugInsideOut stack result

def MachineState.expr : MachineState → Expr
  | .decompose e c => plugInsideOut c e
  | .plug e c => plugInsideOut c e

theorem MachineSteps.trans :
    MachineSteps s₁ s₂ → MachineSteps s₂ s₃ → MachineSteps s₁ s₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl =>
      exact h₂
  | step h hrest ih =>
      exact MachineSteps.step h (ih h₂)

theorem machine_step_iff : machine_step s = some s' ↔ MachineStep s s' := by
  constructor
  · intro h
    cases s with
    | decompose e c =>
        cases e with
        | int n =>
            simp [machine_step] at h
            cases h
            exact MachineStep.decompose_int
        | succ e =>
            cases e with
            | int n =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_succ_int
            | succ e =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_succ_succ
            | pred e =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_succ_pred
            | plus e₁ e₂ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_succ_plus
            | times e₁ e₂ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_succ_times
        | pred e =>
            cases e with
            | int n =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_pred_int
            | succ e =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_pred_succ
            | pred e =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_pred_pred
            | plus e₁ e₂ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_pred_plus
            | times e₁ e₂ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_pred_times
        | plus e₁ e₂ =>
            cases e₁ with
            | int n₁ =>
                cases e₂ with
                | int n₂ =>
                    simp [machine_step] at h
                    cases h
                    exact MachineStep.decompose_plus_int
                | succ e₂ =>
                    simp [machine_step] at h
                    cases h
                    exact MachineStep.decompose_plus_right_succ
                | pred e₂ =>
                    simp [machine_step] at h
                    cases h
                    exact MachineStep.decompose_plus_right_pred
                | plus e₂₁ e₂₂ =>
                    simp [machine_step] at h
                    cases h
                    exact MachineStep.decompose_plus_right_plus
                | times e₂₁ e₂₂ =>
                    simp [machine_step] at h
                    cases h
                    exact MachineStep.decompose_plus_right_times
            | succ e₁ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_plus_left_succ
            | pred e₁ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_plus_left_pred
            | plus e₁₁ e₁₂ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_plus_left_plus
            | times e₁₁ e₁₂ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_plus_left_times
        | times e₁ e₂ =>
            cases e₁ with
            | int n₁ =>
                cases e₂ with
                | int n₂ =>
                    simp [machine_step] at h
                    cases h
                    exact MachineStep.decompose_times_int
                | succ e₂ =>
                    simp [machine_step] at h
                    cases h
                    exact MachineStep.decompose_times_right_succ
                | pred e₂ =>
                    simp [machine_step] at h
                    cases h
                    exact MachineStep.decompose_times_right_pred
                | plus e₂₁ e₂₂ =>
                    simp [machine_step] at h
                    cases h
                    exact MachineStep.decompose_times_right_plus
                | times e₂₁ e₂₂ =>
                    simp [machine_step] at h
                    cases h
                    exact MachineStep.decompose_times_right_times
            | succ e₁ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_times_left_succ
            | pred e₁ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_times_left_pred
            | plus e₁₁ e₁₂ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_times_left_plus
            | times e₁₁ e₁₂ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.decompose_times_left_times
    | plug e c =>
        cases c with
        | nil =>
            simp [machine_step] at h
        | cons frame c =>
            cases frame with
            | succ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.plug_succ
            | pred =>
                simp [machine_step] at h
                cases h
                exact MachineStep.plug_pred
            | plus_left e₂ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.plug_plus_left
            | plus_right n₁ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.plug_plus_right
            | times_left e₂ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.plug_times_left
            | times_right n₁ =>
                simp [machine_step] at h
                cases h
                exact MachineStep.plug_times_right
  · intro h
    cases h <;> rfl

theorem MachineStep.to_machine_step_result : MachineStep s s' → machine_step s = some s' :=
  machine_step_iff.mpr

theorem MachineStep.of_machine_step_result : machine_step s = some s' → MachineStep s s' :=
  machine_step_iff.mp

theorem run_machine_for_sound :
    run_machine_for fuel s = some s' → MachineSteps s s' := by
  intro h
  induction fuel generalizing s with
  | zero =>
      simp [run_machine_for] at h
      cases h
      exact MachineSteps.refl
  | succ fuel ih =>
      simp [run_machine_for] at h
      split at h
      · rename_i next hstep
        exact MachineSteps.step (MachineStep.of_machine_step_result hstep) (ih h)
      · simp at h

theorem run_machine_for_complete :
    MachineSteps s s' → ∃ fuel, run_machine_for fuel s = some s' := by
  intro h
  induction h with
  | refl =>
      exact ⟨0, rfl⟩
  | step hstep _ ih =>
      rcases ih with ⟨fuel, hrun⟩
      exact ⟨fuel + 1, by simp [run_machine_for, hstep.to_machine_step_result, hrun]⟩

theorem run_machine_for_iff :
    (∃ fuel, run_machine_for fuel s = some s') ↔ MachineSteps s s' := by
  constructor
  · intro h
    rcases h with ⟨fuel, hrun⟩
    exact run_machine_for_sound hrun
  · exact run_machine_for_complete

theorem StandardStep.plugInsideOut :
    StandardStep e e' → StandardStep (plugInsideOut c e) (plugInsideOut c e') := by
  intro h
  induction c generalizing e e' with
  | nil =>
      exact h
  | cons frame c ih =>
      apply ih
      cases frame with
      | succ =>
          exact StandardStep.succ_step h
      | pred =>
          exact StandardStep.pred_step h
      | plus_left e₂ =>
          exact StandardStep.plus_left h
      | plus_right n₁ =>
          exact StandardStep.plus_right h
      | times_left e₂ =>
          exact StandardStep.times_left h
      | times_right n₁ =>
          exact StandardStep.times_right h

theorem StandardStep.preserve_Eval : StandardStep e e' → Eval e' n → Eval e n := by
  intro h
  exact h.toStep.preserve_Eval

theorem StandardSteps.preserve_Eval : StandardSteps e e' → Eval e' n → Eval e n := by
  intro h heval
  induction h generalizing n with
  | refl =>
      exact heval
  | step hstep _ ih =>
      exact hstep.preserve_Eval (ih heval)

theorem MachineStep.toStandardSteps :
    MachineStep s₁ s₂ → StandardSteps s₁.expr s₂.expr := by
  intro h
  cases h <;>
    first
    | exact StandardSteps.refl
    | exact (StandardStep.plugInsideOut (c := _) StandardStep.succ_int).toStandardSteps
    | exact (StandardStep.plugInsideOut (c := _) StandardStep.pred_int).toStandardSteps
    | exact (StandardStep.plugInsideOut (c := _) StandardStep.plus_int).toStandardSteps
    | exact (StandardStep.plugInsideOut (c := _) StandardStep.times_int).toStandardSteps

theorem MachineStep.preserve_Eval : MachineStep s₁ s₂ → Eval s₂.expr n → Eval s₁.expr n := by
  intro h heval
  exact h.toStandardSteps.preserve_Eval heval

theorem MachineSteps.preserve_Eval : MachineSteps s₁ s₂ → Eval s₂.expr n → Eval s₁.expr n := by
  intro h heval
  induction h generalizing n with
  | refl =>
      exact heval
  | step hstep _ ih =>
      exact hstep.preserve_Eval (ih heval)

theorem MachineEval.to_Eval : MachineEval e n → Eval e n := by
  intro h
  exact h.preserve_Eval Eval.int

def standard_reduce (e : Expr) : Option Expr :=
  match decompose e with
  | some (c, redex) =>
      match contract redex with
      | some contractum => some (plug c contractum)
      | none => none
  | none => none

partial def eval_reduce (e : Expr) : Expr :=
  match standard_reduce e with
  | some e' => eval_reduce e'
  | none => e

theorem Contract.of_contract : contract e = some e' → Contract e e' := by
  intro h
  cases e with
  | int n =>
      simp [contract] at h
  | succ e =>
      cases e with
      | int n =>
          simp [contract] at h
          cases h
          exact Contract.succ_int
      | succ e | pred e | plus e₁ e₂ | times e₁ e₂ =>
          simp [contract] at h
  | pred e =>
      cases e with
      | int n =>
          simp [contract] at h
          cases h
          exact Contract.pred_int
      | succ e | pred e | plus e₁ e₂ | times e₁ e₂ =>
          simp [contract] at h
  | plus e₁ e₂ =>
      cases e₁ <;> cases e₂ <;> simp [contract] at h
      cases h
      exact Contract.plus_int
  | times e₁ e₂ =>
      cases e₁ <;> cases e₂ <;> simp [contract] at h
      cases h
      exact Contract.times_int

theorem Contract.contract : Contract e e' → contract e = some e' := by
  intro h
  cases h with
  | succ_int =>
      rfl
  | pred_int =>
      rfl
  | plus_int =>
      rfl
  | times_int =>
      rfl

theorem EvalPlug.plug_rel : EvalPlug c e (plug c e) := by
  induction c with
  | hole =>
      exact EvalPlug.hole
  | succ c ih =>
      exact EvalPlug.succ ih
  | pred c ih =>
      exact EvalPlug.pred ih
  | plus_left c e₂ ih =>
      exact EvalPlug.plus_left ih
  | plus_right n₁ c ih =>
      exact EvalPlug.plus_right ih
  | times_left c e₂ ih =>
      exact EvalPlug.times_left ih
  | times_right n₁ c ih =>
      exact EvalPlug.times_right ih

theorem EvalPlug.eq_plug : EvalPlug c e whole → Semantics.plug c e = whole := by
  intro h
  induction h with
  | hole =>
      rfl
  | succ _ ih =>
      simp [plug, ih]
  | pred _ ih =>
      simp [plug, ih]
  | plus_left _ ih =>
      simp [plug, ih]
  | plus_right _ ih =>
      simp [plug, ih]
  | times_left _ ih =>
      simp [plug, ih]
  | times_right _ ih =>
      simp [plug, ih]

theorem map_contract_succ :
    (match contract redex with
      | some contractum => some (.succ (plug c contractum))
      | none => none) =
    Option.map Expr.succ
      (match contract redex with
      | some contractum => some (plug c contractum)
      | none => none) := by
  cases contract redex <;> rfl

theorem map_contract_pred :
    (match contract redex with
      | some contractum => some (.pred (plug c contractum))
      | none => none) =
    Option.map Expr.pred
      (match contract redex with
      | some contractum => some (plug c contractum)
      | none => none) := by
  cases contract redex <;> rfl

theorem map_contract_plus_left :
    (match contract redex with
      | some contractum => some (.plus (plug c contractum) e₂)
      | none => none) =
    Option.map (fun e₁ => Expr.plus e₁ e₂)
      (match contract redex with
      | some contractum => some (plug c contractum)
      | none => none) := by
  cases contract redex <;> rfl

theorem map_contract_plus_right :
    (match contract redex with
      | some contractum => some (.plus (.int n₁) (plug c contractum))
      | none => none) =
    Option.map (fun e₂ => Expr.plus (.int n₁) e₂)
      (match contract redex with
      | some contractum => some (plug c contractum)
      | none => none) := by
  cases contract redex <;> rfl

theorem map_contract_times_left :
    (match contract redex with
      | some contractum => some (.times (plug c contractum) e₂)
      | none => none) =
    Option.map (fun e₁ => Expr.times e₁ e₂)
      (match contract redex with
      | some contractum => some (plug c contractum)
      | none => none) := by
  cases contract redex <;> rfl

theorem map_contract_times_right :
    (match contract redex with
      | some contractum => some (.times (.int n₁) (plug c contractum))
      | none => none) =
    Option.map (fun e₂ => Expr.times (.int n₁) e₂)
      (match contract redex with
      | some contractum => some (plug c contractum)
      | none => none) := by
  cases contract redex <;> rfl

theorem standard_reduce_succ_eq :
    standard_reduce (.succ e) =
      match e with
      | .int n => some (.int (n + 1))
      | _ => Option.map Expr.succ (standard_reduce e) := by
  cases e <;> simp [standard_reduce, decompose, contract, plug]
  all_goals
    cases h : decompose _ <;> simp [plug]
    case some pair =>
      cases pair
      rename_i c redex
      exact map_contract_succ

theorem standard_reduce_pred_eq :
    standard_reduce (.pred e) =
      match e with
      | .int n => some (.int (n - 1))
      | _ => Option.map Expr.pred (standard_reduce e) := by
  cases e <;> simp [standard_reduce, decompose, contract, plug]
  all_goals
    cases h : decompose _ <;> simp [plug]
    case some pair =>
      cases pair
      rename_i c redex
      exact map_contract_pred

theorem standard_reduce_plus_eq :
    standard_reduce (.plus e₁ e₂) =
      match e₁ with
      | .int n₁ =>
          match e₂ with
          | .int n₂ => some (.int (n₁ + n₂))
          | _ => Option.map (fun e₂' => Expr.plus (.int n₁) e₂') (standard_reduce e₂)
      | _ => Option.map (fun e₁' => Expr.plus e₁' e₂) (standard_reduce e₁) := by
  cases e₁ <;> cases e₂ <;> simp [standard_reduce, decompose, contract, plug]
  all_goals
    cases h : decompose _ <;> simp [plug]
    case some pair =>
      cases pair
      rename_i c redex
      first
      | exact map_contract_plus_left
      | exact map_contract_plus_right

theorem standard_reduce_times_eq :
    standard_reduce (.times e₁ e₂) =
      match e₁ with
      | .int n₁ =>
          match e₂ with
          | .int n₂ => some (.int (n₁ * n₂))
          | _ => Option.map (fun e₂' => Expr.times (.int n₁) e₂') (standard_reduce e₂)
      | _ => Option.map (fun e₁' => Expr.times e₁' e₂) (standard_reduce e₁) := by
  cases e₁ <;> cases e₂ <;> simp [standard_reduce, decompose, contract, plug]
  all_goals
    cases h : decompose _ <;> simp [plug]
    case some pair =>
      cases pair
      rename_i c redex
      first
      | exact map_contract_times_left
      | exact map_contract_times_right

theorem StandardStep.to_standard_reduce_result : StandardStep e e' → standard_reduce e = some e' := by
  intro h
  induction h with
  | succ_step h ih =>
      rw [standard_reduce_succ_eq]
      cases h <;> simp [ih]
  | succ_int =>
      rw [standard_reduce_succ_eq]
  | pred_step h ih =>
      rw [standard_reduce_pred_eq]
      cases h <;> simp [ih]
  | pred_int =>
      rw [standard_reduce_pred_eq]
  | plus_left h ih =>
      rw [standard_reduce_plus_eq]
      cases h <;> simp [ih]
  | plus_right h ih =>
      rw [standard_reduce_plus_eq]
      cases h <;> simp [ih]
  | plus_int =>
      rw [standard_reduce_plus_eq]
  | times_left h ih =>
      rw [standard_reduce_times_eq]
      cases h <;> simp [ih]
  | times_right h ih =>
      rw [standard_reduce_times_eq]
      cases h <;> simp [ih]
  | times_int =>
      rw [standard_reduce_times_eq]

theorem StandardStep.of_standard_reduce_result : standard_reduce e = some e' → StandardStep e e' := by
  intro h
  induction e generalizing e' with
  | int n =>
      simp [standard_reduce, decompose] at h
  | succ e ih =>
      rw [standard_reduce_succ_eq] at h
      cases e with
      | int n =>
          simp at h
          cases h
          exact StandardStep.succ_int
      | succ e | pred e | plus e₁ e₂ | times e₁ e₂ =>
          simp at h
          rcases h with ⟨e₀, hreduce, rfl⟩
          exact StandardStep.succ_step (ih hreduce)
  | pred e ih =>
      rw [standard_reduce_pred_eq] at h
      cases e with
      | int n =>
          simp at h
          cases h
          exact StandardStep.pred_int
      | succ e | pred e | plus e₁ e₂ | times e₁ e₂ =>
          simp at h
          rcases h with ⟨e₀, hreduce, rfl⟩
          exact StandardStep.pred_step (ih hreduce)
  | plus e₁ e₂ ih₁ ih₂ =>
      rw [standard_reduce_plus_eq] at h
      cases e₁ with
      | int n₁ =>
          cases e₂ with
          | int n₂ =>
              simp at h
              cases h
              exact StandardStep.plus_int
          | succ e₂ | pred e₂ | plus e₂₁ e₂₂ | times e₂₁ e₂₂ =>
              simp at h
              rcases h with ⟨e₂', hreduce, rfl⟩
              exact StandardStep.plus_right (ih₂ hreduce)
      | succ e₁ | pred e₁ | plus e₁₁ e₁₂ | times e₁₁ e₁₂ =>
          simp at h
          rcases h with ⟨e₁', hreduce, rfl⟩
          exact StandardStep.plus_left (ih₁ hreduce)
  | times e₁ e₂ ih₁ ih₂ =>
      rw [standard_reduce_times_eq] at h
      cases e₁ with
      | int n₁ =>
          cases e₂ with
          | int n₂ =>
              simp at h
              cases h
              exact StandardStep.times_int
          | succ e₂ | pred e₂ | plus e₂₁ e₂₂ | times e₂₁ e₂₂ =>
              simp at h
              rcases h with ⟨e₂', hreduce, rfl⟩
              exact StandardStep.times_right (ih₂ hreduce)
      | succ e₁ | pred e₁ | plus e₁₁ e₁₂ | times e₁₁ e₁₂ =>
          simp at h
          rcases h with ⟨e₁', hreduce, rfl⟩
          exact StandardStep.times_left (ih₁ hreduce)

theorem standard_reduce_iff_standardStep :
    standard_reduce e = some e' ↔ StandardStep e e' := by
  constructor
  · exact StandardStep.of_standard_reduce_result
  · exact StandardStep.to_standard_reduce_result

theorem Contract.toStep : Contract e e' → Step e e' := by
  intro h
  cases h with
  | succ_int =>
      exact Step.succ_int
  | pred_int =>
      exact Step.pred_int
  | plus_int =>
      exact Step.plus_int
  | times_int =>
      exact Step.times_int

theorem Contract.toStandardStep : Contract e e' → StandardStep e e' := by
  intro h
  cases h with
  | succ_int =>
      exact StandardStep.succ_int
  | pred_int =>
      exact StandardStep.pred_int
  | plus_int =>
      exact StandardStep.plus_int
  | times_int =>
      exact StandardStep.times_int

theorem Plug.step :
    Plug c e whole → Plug c e' whole' → Step e e' → Step whole whole' := by
  intro hplug
  induction hplug generalizing e' whole' with
  | hole =>
      intro hplug' hstep
      cases hplug'
      exact hstep
  | succ hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | succ hplug' =>
          exact Step.succ_step (ih hplug' hstep)
  | pred hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | pred hplug' =>
          exact Step.pred_step (ih hplug' hstep)
  | plus_left hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | plus_left hplug' =>
          exact Step.plus_left (ih hplug' hstep)
  | plus_right hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | plus_right hplug' =>
          exact Step.plus_right (ih hplug' hstep)
  | times_left hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | times_left hplug' =>
          exact Step.times_left (ih hplug' hstep)
  | times_right hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | times_right hplug' =>
          exact Step.times_right (ih hplug' hstep)

theorem Reduce.toStep : Reduce e e' → Step e e' := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact hplug.step hplug' hcontract.toStep

theorem EvalPlug.standardStep :
    EvalPlug c e whole → EvalPlug c e' whole' → StandardStep e e' →
      StandardStep whole whole' := by
  intro hplug
  induction hplug generalizing e' whole' with
  | hole =>
      intro hplug' hstep
      cases hplug'
      exact hstep
  | succ hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | succ hplug' =>
          exact StandardStep.succ_step (ih hplug' hstep)
  | pred hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | pred hplug' =>
          exact StandardStep.pred_step (ih hplug' hstep)
  | plus_left hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | plus_left hplug' =>
          exact StandardStep.plus_left (ih hplug' hstep)
  | plus_right hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | plus_right hplug' =>
          exact StandardStep.plus_right (ih hplug' hstep)
  | times_left hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | times_left hplug' =>
          exact StandardStep.times_left (ih hplug' hstep)
  | times_right hplug ih =>
      intro hplug' hstep
      cases hplug' with
      | times_right hplug' =>
          exact StandardStep.times_right (ih hplug' hstep)

theorem StandardReduce.toStandardStep : StandardReduce e e' → StandardStep e e' := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact hplug.standardStep hplug' hcontract.toStandardStep

theorem Reduce.succ : Reduce e e' → Reduce (.succ e) (.succ e') := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact Reduce.context (Plug.succ hplug) hcontract (Plug.succ hplug')

theorem Reduce.pred : Reduce e e' → Reduce (.pred e) (.pred e') := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact Reduce.context (Plug.pred hplug) hcontract (Plug.pred hplug')

theorem Reduce.plus_left : Reduce e₁ e₁' → Reduce (.plus e₁ e₂) (.plus e₁' e₂) := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact Reduce.context (Plug.plus_left hplug) hcontract (Plug.plus_left hplug')

theorem Reduce.plus_right : Reduce e₂ e₂' → Reduce (.plus e₁ e₂) (.plus e₁ e₂') := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact Reduce.context (Plug.plus_right hplug) hcontract (Plug.plus_right hplug')

theorem Reduce.times_left : Reduce e₁ e₁' → Reduce (.times e₁ e₂) (.times e₁' e₂) := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact Reduce.context (Plug.times_left hplug) hcontract (Plug.times_left hplug')

theorem Reduce.times_right : Reduce e₂ e₂' → Reduce (.times e₁ e₂) (.times e₁ e₂') := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact Reduce.context (Plug.times_right hplug) hcontract (Plug.times_right hplug')

theorem StandardReduce.succ :
    StandardReduce e e' → StandardReduce (.succ e) (.succ e') := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact StandardReduce.context (EvalPlug.succ hplug) hcontract (EvalPlug.succ hplug')

theorem StandardReduce.pred :
    StandardReduce e e' → StandardReduce (.pred e) (.pred e') := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact StandardReduce.context (EvalPlug.pred hplug) hcontract (EvalPlug.pred hplug')

theorem StandardReduce.plus_left :
    StandardReduce e₁ e₁' → StandardReduce (.plus e₁ e₂) (.plus e₁' e₂) := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact StandardReduce.context (EvalPlug.plus_left hplug) hcontract (EvalPlug.plus_left hplug')

theorem StandardReduce.plus_right :
    StandardReduce e₂ e₂' → StandardReduce (.plus (.int n₁) e₂) (.plus (.int n₁) e₂') := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact
        StandardReduce.context (EvalPlug.plus_right hplug) hcontract
          (EvalPlug.plus_right hplug')

theorem StandardReduce.times_left :
    StandardReduce e₁ e₁' → StandardReduce (.times e₁ e₂) (.times e₁' e₂) := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact
        StandardReduce.context (EvalPlug.times_left hplug) hcontract
          (EvalPlug.times_left hplug')

theorem StandardReduce.times_right :
    StandardReduce e₂ e₂' → StandardReduce (.times (.int n₁) e₂) (.times (.int n₁) e₂') := by
  intro h
  cases h with
  | context hplug hcontract hplug' =>
      exact
        StandardReduce.context (EvalPlug.times_right hplug) hcontract
          (EvalPlug.times_right hplug')

theorem Step.toReduce : Step e e' → Reduce e e' := by
  intro h
  induction h with
  | succ_step _ ih =>
      exact ih.succ
  | succ_int =>
      exact Reduce.context Plug.hole Contract.succ_int Plug.hole
  | pred_step _ ih =>
      exact ih.pred
  | pred_int =>
      exact Reduce.context Plug.hole Contract.pred_int Plug.hole
  | plus_left _ ih =>
      exact ih.plus_left
  | plus_right _ ih =>
      exact ih.plus_right
  | plus_int =>
      exact Reduce.context Plug.hole Contract.plus_int Plug.hole
  | times_left _ ih =>
      exact ih.times_left
  | times_right _ ih =>
      exact ih.times_right
  | times_int =>
      exact Reduce.context Plug.hole Contract.times_int Plug.hole

theorem StandardStep.toStandardReduce : StandardStep e e' → StandardReduce e e' := by
  intro h
  induction h with
  | succ_step _ ih =>
      exact ih.succ
  | succ_int =>
      exact StandardReduce.context EvalPlug.hole Contract.succ_int EvalPlug.hole
  | pred_step _ ih =>
      exact ih.pred
  | pred_int =>
      exact StandardReduce.context EvalPlug.hole Contract.pred_int EvalPlug.hole
  | plus_left _ ih =>
      exact ih.plus_left
  | plus_right _ ih =>
      exact ih.plus_right
  | plus_int =>
      exact StandardReduce.context EvalPlug.hole Contract.plus_int EvalPlug.hole
  | times_left _ ih =>
      exact ih.times_left
  | times_right _ ih =>
      exact ih.times_right
  | times_int =>
      exact StandardReduce.context EvalPlug.hole Contract.times_int EvalPlug.hole

theorem StandardReduce.iff_standardStep : StandardReduce e e' ↔ StandardStep e e' := by
  constructor
  · intro h
    exact h.toStandardStep
  · intro h
    exact h.toStandardReduce

theorem standard_reduce_iff_standardReduce :
    standard_reduce e = some e' ↔ StandardReduce e e' := by
  calc
    standard_reduce e = some e' ↔ StandardStep e e' :=
      standard_reduce_iff_standardStep
    _ ↔ StandardReduce e e' :=
      StandardReduce.iff_standardStep.symm

theorem ReduceSteps.toSteps : ReduceSteps e e' → Steps e e' := by
  intro h
  induction h with
  | refl =>
      exact Steps.refl
  | step h hrest ih =>
      exact Steps.step h.toStep ih

theorem Steps.toReduceSteps : Steps e e' → ReduceSteps e e' := by
  intro h
  induction h with
  | refl =>
      exact ReduceSteps.refl
  | step h hrest ih =>
      exact ReduceSteps.step h.toReduce ih

theorem StandardReduceSteps.toStandardSteps :
    StandardReduceSteps e e' → StandardSteps e e' := by
  intro h
  induction h with
  | refl =>
      exact StandardSteps.refl
  | step h hrest ih =>
      exact StandardSteps.step h.toStandardStep ih

theorem StandardSteps.toStandardReduceSteps :
    StandardSteps e e' → StandardReduceSteps e e' := by
  intro h
  induction h with
  | refl =>
      exact StandardReduceSteps.refl
  | step h hrest ih =>
      exact StandardReduceSteps.step h.toStandardReduce ih

theorem EvalReduce.iff_stepEval : EvalReduce e n ↔ StepEval e n := by
  constructor
  · intro h
    exact h.toSteps
  · intro h
    exact h.toReduceSteps

theorem EvalStandardReduce.iff_standardSteps :
    EvalStandardReduce e n ↔ StandardSteps e (.int n) := by
  constructor
  · intro h
    exact h.toStandardSteps
  · intro h
    exact h.toStandardReduceSteps

theorem EvalStandardReduce.iff_stepEval : EvalStandardReduce e n ↔ StepEval e n := by
  calc
    EvalStandardReduce e n ↔ StandardSteps e (.int n) :=
      EvalStandardReduce.iff_standardSteps
    _ ↔ Steps e (.int n) :=
      StandardSteps.iff_steps_int

end Semantics

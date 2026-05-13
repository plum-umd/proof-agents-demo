import Semantics.BigStep

namespace Semantics

inductive StandardStep : Expr → Expr → Prop where
  | succ_step : StandardStep e e' → StandardStep (.succ e) (.succ e')
  | succ_int : StandardStep (.succ (.int n)) (.int (n + 1))
  | pred_step : StandardStep e e' → StandardStep (.pred e) (.pred e')
  | pred_int : StandardStep (.pred (.int n)) (.int (n - 1))
  | plus_left : StandardStep e₁ e₁' → StandardStep (.plus e₁ e₂) (.plus e₁' e₂)
  | plus_right : StandardStep e₂ e₂' → StandardStep (.plus (.int n₁) e₂) (.plus (.int n₁) e₂')
  | plus_int : StandardStep (.plus (.int n₁) (.int n₂)) (.int (n₁ + n₂))
  | times_left : StandardStep e₁ e₁' → StandardStep (.times e₁ e₂) (.times e₁' e₂)
  | times_right :
      StandardStep e₂ e₂' → StandardStep (.times (.int n₁) e₂) (.times (.int n₁) e₂')
  | times_int : StandardStep (.times (.int n₁) (.int n₂)) (.int (n₁ * n₂))

inductive Step : Expr → Expr → Prop where
  | succ_step : Step e e' → Step (.succ e) (.succ e')
  | succ_int : Step (.succ (.int n)) (.int (n + 1))
  | pred_step : Step e e' → Step (.pred e) (.pred e')
  | pred_int : Step (.pred (.int n)) (.int (n - 1))
  | plus_left : Step e₁ e₁' → Step (.plus e₁ e₂) (.plus e₁' e₂)
  | plus_right : Step e₂ e₂' → Step (.plus e₁ e₂) (.plus e₁ e₂')
  | plus_int : Step (.plus (.int n₁) (.int n₂)) (.int (n₁ + n₂))
  | times_left : Step e₁ e₁' → Step (.times e₁ e₂) (.times e₁' e₂)
  | times_right : Step e₂ e₂' → Step (.times e₁ e₂) (.times e₁ e₂')
  | times_int : Step (.times (.int n₁) (.int n₂)) (.int (n₁ * n₂))

example :
    Step
      (.plus (.succ (.int 1)) (.pred (.int 4)))
      (.plus (.int 2) (.pred (.int 4))) :=
  Step.plus_left Step.succ_int

example :
    Step
      (.plus (.succ (.int 1)) (.pred (.int 4)))
      (.plus (.succ (.int 1)) (.int 3)) :=
  Step.plus_right Step.pred_int

def Joinable (e₁ e₂ : Expr) : Prop :=
  e₁ = e₂ ∨ ∃ e, Step e₁ e ∧ Step e₂ e

theorem Step.int_no_step : ¬ Step (.int n) e := by
  intro h
  cases h

theorem Step.strong_confluence : Step e e₁ → Step e e₂ → Joinable e₁ e₂ := by
  intro h₁
  induction h₁ generalizing e₂ with
  | succ_step h ih =>
      intro h₂
      cases h₂ with
      | succ_step h₂ =>
          cases ih h₂ with
          | inl h =>
              exact Or.inl (by rw [h])
          | inr h =>
              rcases h with ⟨e, h₁', h₂'⟩
              exact Or.inr ⟨.succ e, Step.succ_step h₁', Step.succ_step h₂'⟩
      | succ_int =>
          exact False.elim (Step.int_no_step h)
  | succ_int =>
      intro h₂
      cases h₂ with
      | succ_step h₂ =>
          exact False.elim (Step.int_no_step h₂)
      | succ_int =>
          exact Or.inl rfl
  | pred_step h ih =>
      intro h₂
      cases h₂ with
      | pred_step h₂ =>
          cases ih h₂ with
          | inl h =>
              exact Or.inl (by rw [h])
          | inr h =>
              rcases h with ⟨e, h₁', h₂'⟩
              exact Or.inr ⟨.pred e, Step.pred_step h₁', Step.pred_step h₂'⟩
      | pred_int =>
          exact False.elim (Step.int_no_step h)
  | pred_int =>
      intro h₂
      cases h₂ with
      | pred_step h₂ =>
          exact False.elim (Step.int_no_step h₂)
      | pred_int =>
          exact Or.inl rfl
  | plus_left h ih =>
      intro h₂
      cases h₂ with
      | plus_left h₂ =>
          cases ih h₂ with
          | inl h =>
              exact Or.inl (by rw [h])
          | inr h =>
              rcases h with ⟨e, h₁', h₂'⟩
              exact Or.inr ⟨.plus e _, Step.plus_left h₁', Step.plus_left h₂'⟩
      | plus_right h₂ =>
          exact Or.inr ⟨.plus _ _, Step.plus_right h₂, Step.plus_left h⟩
      | plus_int =>
          exact False.elim (Step.int_no_step h)
  | plus_right h ih =>
      intro h₂
      cases h₂ with
      | plus_left h₂ =>
          exact Or.inr ⟨.plus _ _, Step.plus_left h₂, Step.plus_right h⟩
      | plus_right h₂ =>
          cases ih h₂ with
          | inl h =>
              exact Or.inl (by rw [h])
          | inr h =>
              rcases h with ⟨e, h₁', h₂'⟩
              exact Or.inr ⟨.plus _ e, Step.plus_right h₁', Step.plus_right h₂'⟩
      | plus_int =>
          exact False.elim (Step.int_no_step h)
  | plus_int =>
      intro h₂
      cases h₂ with
      | plus_left h₂ =>
          exact False.elim (Step.int_no_step h₂)
      | plus_right h₂ =>
          exact False.elim (Step.int_no_step h₂)
      | plus_int =>
          exact Or.inl rfl
  | times_left h ih =>
      intro h₂
      cases h₂ with
      | times_left h₂ =>
          cases ih h₂ with
          | inl h =>
              exact Or.inl (by rw [h])
          | inr h =>
              rcases h with ⟨e, h₁', h₂'⟩
              exact Or.inr ⟨.times e _, Step.times_left h₁', Step.times_left h₂'⟩
      | times_right h₂ =>
          exact Or.inr ⟨.times _ _, Step.times_right h₂, Step.times_left h⟩
      | times_int =>
          exact False.elim (Step.int_no_step h)
  | times_right h ih =>
      intro h₂
      cases h₂ with
      | times_left h₂ =>
          exact Or.inr ⟨.times _ _, Step.times_left h₂, Step.times_right h⟩
      | times_right h₂ =>
          cases ih h₂ with
          | inl h =>
              exact Or.inl (by rw [h])
          | inr h =>
              rcases h with ⟨e, h₁', h₂'⟩
              exact Or.inr ⟨.times _ e, Step.times_right h₁', Step.times_right h₂'⟩
      | times_int =>
          exact False.elim (Step.int_no_step h)
  | times_int =>
      intro h₂
      cases h₂ with
      | times_left h₂ =>
          exact False.elim (Step.int_no_step h₂)
      | times_right h₂ =>
          exact False.elim (Step.int_no_step h₂)
      | times_int =>
          exact Or.inl rfl

inductive Steps : Expr → Expr → Prop where
  | refl : Steps e e
  | step : Step e₁ e₂ → Steps e₂ e₃ → Steps e₁ e₃

inductive StandardSteps : Expr → Expr → Prop where
  | refl : StandardSteps e e
  | step : StandardStep e₁ e₂ → StandardSteps e₂ e₃ → StandardSteps e₁ e₃

def StepEval (e : Expr) (n : Int) : Prop :=
  Steps e (.int n)

def StandardStepEval (e : Expr) (n : Int) : Prop :=
  StandardSteps e (.int n)

theorem StandardStep.toStep : StandardStep e e' → Step e e' := by
  intro h
  induction h with
  | succ_step _ ih =>
      exact Step.succ_step ih
  | succ_int =>
      exact Step.succ_int
  | pred_step _ ih =>
      exact Step.pred_step ih
  | pred_int =>
      exact Step.pred_int
  | plus_left _ ih =>
      exact Step.plus_left ih
  | plus_right _ ih =>
      exact Step.plus_right ih
  | plus_int =>
      exact Step.plus_int
  | times_left _ ih =>
      exact Step.times_left ih
  | times_right _ ih =>
      exact Step.times_right ih
  | times_int =>
      exact Step.times_int

theorem Step.toSteps : Step e e' → Steps e e' := by
  intro h
  exact Steps.step h Steps.refl

theorem Steps.trans : Steps e₁ e₂ → Steps e₂ e₃ → Steps e₁ e₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl =>
      exact h₂
  | step h hrest ih =>
      exact Steps.step h (ih h₂)

theorem StandardStep.toStandardSteps : StandardStep e e' → StandardSteps e e' := by
  intro h
  exact StandardSteps.step h StandardSteps.refl

theorem StandardSteps.trans :
    StandardSteps e₁ e₂ → StandardSteps e₂ e₃ → StandardSteps e₁ e₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl =>
      exact h₂
  | step h hrest ih =>
      exact StandardSteps.step h (ih h₂)

theorem StandardSteps.toSteps : StandardSteps e e' → Steps e e' := by
  intro h
  induction h with
  | refl =>
      exact Steps.refl
  | step h hrest ih =>
      exact Steps.step h.toStep ih

theorem Steps.succ : Steps e e' → Steps (.succ e) (.succ e') := by
  intro h
  induction h with
  | refl =>
      exact Steps.refl
  | step h hrest ih =>
      exact Steps.step (Step.succ_step h) ih

theorem Steps.pred : Steps e e' → Steps (.pred e) (.pred e') := by
  intro h
  induction h with
  | refl =>
      exact Steps.refl
  | step h hrest ih =>
      exact Steps.step (Step.pred_step h) ih

theorem Steps.plus_left : Steps e₁ e₁' → Steps (.plus e₁ e₂) (.plus e₁' e₂) := by
  intro h
  induction h with
  | refl =>
      exact Steps.refl
  | step h hrest ih =>
      exact Steps.step (Step.plus_left h) ih

theorem Steps.plus_right : Steps e₂ e₂' → Steps (.plus e₁ e₂) (.plus e₁ e₂') := by
  intro h
  induction h with
  | refl =>
      exact Steps.refl
  | step h hrest ih =>
      exact Steps.step (Step.plus_right h) ih

theorem Steps.times_left : Steps e₁ e₁' → Steps (.times e₁ e₂) (.times e₁' e₂) := by
  intro h
  induction h with
  | refl =>
      exact Steps.refl
  | step h hrest ih =>
      exact Steps.step (Step.times_left h) ih

theorem Steps.times_right : Steps e₂ e₂' → Steps (.times e₁ e₂) (.times e₁ e₂') := by
  intro h
  induction h with
  | refl =>
      exact Steps.refl
  | step h hrest ih =>
      exact Steps.step (Step.times_right h) ih

theorem StandardSteps.succ : StandardSteps e e' → StandardSteps (.succ e) (.succ e') := by
  intro h
  induction h with
  | refl =>
      exact StandardSteps.refl
  | step h hrest ih =>
      exact StandardSteps.step (StandardStep.succ_step h) ih

theorem StandardSteps.pred : StandardSteps e e' → StandardSteps (.pred e) (.pred e') := by
  intro h
  induction h with
  | refl =>
      exact StandardSteps.refl
  | step h hrest ih =>
      exact StandardSteps.step (StandardStep.pred_step h) ih

theorem StandardSteps.plus_left :
    StandardSteps e₁ e₁' → StandardSteps (.plus e₁ e₂) (.plus e₁' e₂) := by
  intro h
  induction h with
  | refl =>
      exact StandardSteps.refl
  | step h hrest ih =>
      exact StandardSteps.step (StandardStep.plus_left h) ih

theorem StandardSteps.plus_right :
    StandardSteps e₂ e₂' → StandardSteps (.plus (.int n₁) e₂) (.plus (.int n₁) e₂') := by
  intro h
  induction h with
  | refl =>
      exact StandardSteps.refl
  | step h hrest ih =>
      exact StandardSteps.step (StandardStep.plus_right h) ih

theorem StandardSteps.times_left :
    StandardSteps e₁ e₁' → StandardSteps (.times e₁ e₂) (.times e₁' e₂) := by
  intro h
  induction h with
  | refl =>
      exact StandardSteps.refl
  | step h hrest ih =>
      exact StandardSteps.step (StandardStep.times_left h) ih

theorem StandardSteps.times_right :
    StandardSteps e₂ e₂' → StandardSteps (.times (.int n₁) e₂) (.times (.int n₁) e₂') := by
  intro h
  induction h with
  | refl =>
      exact StandardSteps.refl
  | step h hrest ih =>
      exact StandardSteps.step (StandardStep.times_right h) ih

theorem StepEval.of_Eval : Eval e n → StepEval e n := by
  intro h
  induction h with
  | int =>
      exact Steps.refl
  | succ h ih =>
      exact (Steps.succ ih).trans (Step.succ_int.toSteps)
  | pred h ih =>
      exact (Steps.pred ih).trans (Step.pred_int.toSteps)
  | plus h₁ h₂ ih₁ ih₂ =>
      exact
        (Steps.plus_left ih₁).trans
          ((Steps.plus_right ih₂).trans Step.plus_int.toSteps)
  | times h₁ h₂ ih₁ ih₂ =>
      exact
        (Steps.times_left ih₁).trans
          ((Steps.times_right ih₂).trans Step.times_int.toSteps)

theorem StandardStepEval.of_Eval : Eval e n → StandardStepEval e n := by
  intro h
  induction h with
  | int =>
      exact StandardSteps.refl
  | succ h ih =>
      exact (StandardSteps.succ ih).trans StandardStep.succ_int.toStandardSteps
  | pred h ih =>
      exact (StandardSteps.pred ih).trans StandardStep.pred_int.toStandardSteps
  | plus h₁ h₂ ih₁ ih₂ =>
      exact
        (StandardSteps.plus_left ih₁).trans
          ((StandardSteps.plus_right ih₂).trans StandardStep.plus_int.toStandardSteps)
  | times h₁ h₂ ih₁ ih₂ =>
      exact
        (StandardSteps.times_left ih₁).trans
          ((StandardSteps.times_right ih₂).trans StandardStep.times_int.toStandardSteps)

theorem Step.preserve_Eval : Step e e' → Eval e' n → Eval e n := by
  intro hstep heval
  induction hstep generalizing n with
  | succ_step h ih =>
      cases heval with
      | succ heval =>
          exact Eval.succ (ih heval)
  | succ_int =>
      cases heval with
      | int =>
          exact Eval.succ Eval.int
  | pred_step h ih =>
      cases heval with
      | pred heval =>
          exact Eval.pred (ih heval)
  | pred_int =>
      cases heval with
      | int =>
          exact Eval.pred Eval.int
  | plus_left h ih =>
      cases heval with
      | plus heval₁ heval₂ =>
          exact Eval.plus (ih heval₁) heval₂
  | plus_right h ih =>
      cases heval with
      | plus heval₁ heval₂ =>
          exact Eval.plus heval₁ (ih heval₂)
  | plus_int =>
      cases heval with
      | int =>
          exact Eval.plus Eval.int Eval.int
  | times_left h ih =>
      cases heval with
      | times heval₁ heval₂ =>
          exact Eval.times (ih heval₁) heval₂
  | times_right h ih =>
      cases heval with
      | times heval₁ heval₂ =>
          exact Eval.times heval₁ (ih heval₂)
  | times_int =>
      cases heval with
      | int =>
          exact Eval.times Eval.int Eval.int

theorem Eval.of_StepEval : StepEval e n → Eval e n := by
  intro h
  have preserve_steps : ∀ {e e' n}, Steps e e' → Eval e' n → Eval e n := by
    intro e e' n hsteps heval
    induction hsteps generalizing n with
    | refl =>
        exact heval
    | step hstep _ ih =>
        exact hstep.preserve_Eval (ih heval)
  exact preserve_steps h Eval.int

theorem StandardSteps.iff_steps_int : StandardSteps e (.int n) ↔ Steps e (.int n) := by
  constructor
  · intro h
    exact h.toSteps
  · intro h
    exact StandardStepEval.of_Eval (Eval.of_StepEval h)

theorem Joinable.toSteps : Joinable e₁ e₂ → ∃ e, Steps e₁ e ∧ Steps e₂ e := by
  intro h
  cases h with
  | inl h =>
      subst h
      exact ⟨_, Steps.refl, Steps.refl⟩
  | inr h =>
      rcases h with ⟨e, h₁, h₂⟩
      exact ⟨e, h₁.toSteps, h₂.toSteps⟩

theorem Step.join_steps : Step e e₁ → Steps e e₂ → ∃ e₃, Steps e₁ e₃ ∧ Steps e₂ e₃ := by
  intro h s
  induction s generalizing e₁ with
  | refl =>
      exact ⟨e₁, Steps.refl, h.toSteps⟩
  | step h₂ s ih =>
      cases Step.strong_confluence h h₂ with
      | inl hsame =>
          exact ⟨_, by rw [hsame]; exact s, Steps.refl⟩
      | inr hjoin =>
          rcases hjoin with ⟨e, h₁', h₂'⟩
          rcases ih h₂' with ⟨e', hleft, hright⟩
          exact ⟨e', Steps.step h₁' hleft, hright⟩

theorem Steps.confluent : Steps e e₁ → Steps e e₂ → ∃ e₃, Steps e₁ e₃ ∧ Steps e₂ e₃ := by
  intro h₁ h₂
  induction h₁ generalizing e₂ with
  | refl =>
      exact ⟨e₂, h₂, Steps.refl⟩
  | step h hrest ih =>
      rcases Step.join_steps h h₂ with ⟨e', hleft, hright⟩
      rcases ih hleft with ⟨e₃, hend, hjoin⟩
      exact ⟨e₃, hend, hright.trans hjoin⟩

end Semantics

import Semantics.Extended.Definitional

namespace Semantics.Extended

inductive Eval : Env → Expr → Value → Prop where
  | int : Eval ρ (.int n) (.int n)
  | bool : Eval ρ (.bool b) (.bool b)
  | var : ρ.lookup x = some v → Eval ρ (.var x) v
  | succ : Eval ρ e (.int n) → Eval ρ (.succ e) (.int (n + 1))
  | pred : Eval ρ e (.int n) → Eval ρ (.pred e) (.int (n - 1))
  | plus :
      Eval ρ e₁ (.int n₁) → Eval ρ e₂ (.int n₂) → Eval ρ (.plus e₁ e₂) (.int (n₁ + n₂))
  | times :
      Eval ρ e₁ (.int n₁) → Eval ρ e₂ (.int n₂) →
        Eval ρ (.times e₁ e₂) (.int (n₁ * n₂))
  | numEq :
      Eval ρ e₁ (.int n₁) → Eval ρ e₂ (.int n₂) →
        Eval ρ (.numEq e₁ e₂) (.bool (n₁ == n₂))
  | ite_true : Eval ρ e₁ (.bool true) → Eval ρ e₂ v → Eval ρ (.ite e₁ e₂ e₃) v
  | ite_false : Eval ρ e₁ (.bool false) → Eval ρ e₃ v → Eval ρ (.ite e₁ e₂ e₃) v
  | letE : Eval ρ e₁ v₁ → Eval (ρ.extend x v₁) e₂ v₂ → Eval ρ (.letE x e₁ e₂) v₂

theorem Eval.eval_eq : Eval ρ e v → eval ρ e = some v := by
  intro h
  induction h with
  | int => rfl
  | bool => rfl
  | var h => exact h
  | succ _ ih => simp [eval, ih]
  | pred _ ih => simp [eval, ih]
  | plus _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | times _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | numEq _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | ite_true _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | ite_false _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | letE _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]

theorem Eval.of_eval_eq : eval ρ e = some v → Eval ρ e v := by
  intro h
  induction e generalizing ρ v with
  | int n =>
      simp [eval] at h
      rw [← h]
      exact Eval.int
  | bool b =>
      simp [eval] at h
      rw [← h]
      exact Eval.bool
  | var x =>
      exact Eval.var h
  | succ e ih =>
      simp only [eval] at h
      split at h
      next n he =>
        cases h
        exact Eval.succ (ih he)
      next b he =>
        cases h
  | pred e ih =>
      simp only [eval] at h
      split at h
      next n he =>
        cases h
        exact Eval.pred (ih he)
      next b he =>
        cases h
  | plus e₁ e₂ ih₁ ih₂ =>
      simp only [eval] at h
      split at h
      next n₁ n₂ he₁ he₂ =>
        cases h
        exact Eval.plus (ih₁ he₁) (ih₂ he₂)
      all_goals cases h
  | times e₁ e₂ ih₁ ih₂ =>
      simp only [eval] at h
      split at h
      next n₁ n₂ he₁ he₂ =>
        cases h
        exact Eval.times (ih₁ he₁) (ih₂ he₂)
      all_goals cases h
  | numEq e₁ e₂ ih₁ ih₂ =>
      simp only [eval] at h
      split at h
      next n₁ n₂ he₁ he₂ =>
        cases h
        exact Eval.numEq (ih₁ he₁) (ih₂ he₂)
      all_goals cases h
  | ite e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
      simp only [eval] at h
      split at h
      next he₁ =>
        exact Eval.ite_true (ih₁ he₁) (ih₂ h)
      next he₁ =>
        exact Eval.ite_false (ih₁ he₁) (ih₃ h)
      next n he₁ =>
        cases h
  | letE x e₁ e₂ ih₁ ih₂ =>
      simp only [eval] at h
      split at h
      next v₁ he₁ =>
        exact Eval.letE (ih₁ he₁) (ih₂ h)
      next he₁ =>
        cases h

theorem Eval.iff_eval_eq : Eval ρ e v ↔ eval ρ e = some v :=
  ⟨Eval.eval_eq, Eval.of_eval_eq⟩

theorem Eval.deterministic : Eval ρ e v → Eval ρ e v' → v = v' := by
  intro h h'
  have hv : some v = some v' := by
    rw [← h.eval_eq, ← h'.eval_eq]
  cases hv
  rfl

theorem denote_eq_some_iff : Eval [] e v ↔ denote e = some v := by
  simp [denote, Eval.iff_eval_eq]

end Semantics.Extended

import Semantics.Definitional

namespace Semantics

inductive Eval : Expr → Int → Prop where
  | int : Eval (.int n) n
  | succ : Eval e n → Eval (.succ e) (n + 1)
  | pred : Eval e n → Eval (.pred e) (n - 1)
  | plus : Eval e₁ n₁ → Eval e₂ n₂ → Eval (.plus e₁ e₂) (n₁ + n₂)
  | times : Eval e₁ n₁ → Eval e₂ n₂ → Eval (.times e₁ e₂) (n₁ * n₂)

theorem Eval.deterministic : Eval e n → Eval e n' → n = n' := by
  intro h
  induction h generalizing n' with
  | int =>
      intro h'
      cases h'
      rfl
  | succ h ih =>
      intro h'
      cases h' with
      | succ h' =>
          exact congrArg (fun n => n + 1) (ih h')
  | pred h ih =>
      intro h'
      cases h' with
      | pred h' =>
          exact congrArg (fun n => n - 1) (ih h')
  | plus h₁ h₂ ih₁ ih₂ =>
      intro h'
      cases h' with
      | plus h₁' h₂' =>
          rw [ih₁ h₁', ih₂ h₂']
  | times h₁ h₂ ih₁ ih₂ =>
      intro h'
      cases h' with
      | times h₁' h₂' =>
          rw [ih₁ h₁', ih₂ h₂']

theorem Eval.denote_eq : Eval e n → denote e = n := by
  intro h
  induction h with
  | int => rfl
  | succ _ ih => simp [denote, ih]
  | pred _ ih => simp [denote, ih]
  | plus _ _ ih₁ ih₂ => simp [denote, ih₁, ih₂]
  | times _ _ ih₁ ih₂ => simp [denote, ih₁, ih₂]

theorem Eval.of_denote_eq : denote e = n → Eval e n := by
  intro h
  induction e generalizing n with
  | int m =>
      rw [← h]
      exact Eval.int
  | succ e ih =>
      rw [← h]
      exact Eval.succ (ih rfl)
  | pred e ih =>
      rw [← h]
      exact Eval.pred (ih rfl)
  | plus e₁ e₂ ih₁ ih₂ =>
      rw [← h]
      exact Eval.plus (ih₁ rfl) (ih₂ rfl)
  | times e₁ e₂ ih₁ ih₂ =>
      rw [← h]
      exact Eval.times (ih₁ rfl) (ih₂ rfl)

end Semantics

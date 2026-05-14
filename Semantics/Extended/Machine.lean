import Semantics.Extended.SmallStep

namespace Semantics.Extended

inductive Frame where
  | succ : Frame
  | pred : Frame
  | plus_left : Expr → Env → Frame
  | plus_right : Value → Frame
  | times_left : Expr → Env → Frame
  | times_right : Value → Frame
  | numEq_left : Expr → Env → Frame
  | numEq_right : Value → Frame
  | ite : Expr → Expr → Env → Frame
  | letE : String → Expr → Env → Frame
  deriving Repr, DecidableEq

abbrev Stack := List Frame

inductive State where
  | eval : Env → Expr → Stack → State
  | ret : Value → Stack → State
  deriving Repr, DecidableEq

inductive MachineStep : State → State → Prop where
  | int :
      MachineStep (.eval ρ (.int n) κ) (.ret (.int n) κ)
  | bool :
      MachineStep (.eval ρ (.bool b) κ) (.ret (.bool b) κ)
  | var :
      ρ.lookup x = some v →
      MachineStep (.eval ρ (.var x) κ) (.ret v κ)
  | succ :
      MachineStep (.eval ρ (.succ e) κ) (.eval ρ e (.succ :: κ))
  | pred :
      MachineStep (.eval ρ (.pred e) κ) (.eval ρ e (.pred :: κ))
  | plus :
      MachineStep (.eval ρ (.plus e₁ e₂) κ) (.eval ρ e₁ (.plus_left e₂ ρ :: κ))
  | times :
      MachineStep (.eval ρ (.times e₁ e₂) κ) (.eval ρ e₁ (.times_left e₂ ρ :: κ))
  | numEq :
      MachineStep (.eval ρ (.numEq e₁ e₂) κ) (.eval ρ e₁ (.numEq_left e₂ ρ :: κ))
  | ite :
      MachineStep (.eval ρ (.ite e₁ e₂ e₃) κ) (.eval ρ e₁ (.ite e₂ e₃ ρ :: κ))
  | letE :
      MachineStep (.eval ρ (.letE x e₁ e₂) κ) (.eval ρ e₁ (.letE x e₂ ρ :: κ))
  | succ_int :
      MachineStep (.ret (.int n) (.succ :: κ)) (.ret (.int (n + 1)) κ)
  | pred_int :
      MachineStep (.ret (.int n) (.pred :: κ)) (.ret (.int (n - 1)) κ)
  | plus_left :
      MachineStep (.ret v₁ (.plus_left e₂ ρ :: κ)) (.eval ρ e₂ (.plus_right v₁ :: κ))
  | plus_right_int :
      MachineStep (.ret (.int n₂) (.plus_right (.int n₁) :: κ)) (.ret (.int (n₁ + n₂)) κ)
  | times_left :
      MachineStep (.ret v₁ (.times_left e₂ ρ :: κ)) (.eval ρ e₂ (.times_right v₁ :: κ))
  | times_right_int :
      MachineStep (.ret (.int n₂) (.times_right (.int n₁) :: κ)) (.ret (.int (n₁ * n₂)) κ)
  | numEq_left :
      MachineStep (.ret v₁ (.numEq_left e₂ ρ :: κ)) (.eval ρ e₂ (.numEq_right v₁ :: κ))
  | numEq_right_int :
      MachineStep (.ret (.int n₂) (.numEq_right (.int n₁) :: κ)) (.ret (.bool (n₁ == n₂)) κ)
  | ite_true :
      MachineStep (.ret (.bool true) (.ite e₂ e₃ ρ :: κ)) (.eval ρ e₂ κ)
  | ite_false :
      MachineStep (.ret (.bool false) (.ite e₂ e₃ ρ :: κ)) (.eval ρ e₃ κ)
  | let_body :
      MachineStep (.ret v (.letE x e₂ ρ :: κ)) (.eval (ρ.extend x v) e₂ κ)

inductive MachineSteps : State → State → Prop where
  | refl : MachineSteps s s
  | trans : MachineStep s₁ s₂ → MachineSteps s₂ s₃ → MachineSteps s₁ s₃

def MachineEval (e : Expr) (v : Value) : Prop :=
  MachineSteps (.eval [] e []) (.ret v [])

theorem MachineSteps.append : MachineSteps s₁ s₂ → MachineSteps s₂ s₃ → MachineSteps s₁ s₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl =>
      exact h₂
  | trans h _ ih =>
      exact MachineSteps.trans h (ih h₂)

theorem Eval.machine_run : Eval ρ e v → MachineSteps (.eval ρ e κ) (.ret v κ) := by
  intro h
  induction h generalizing κ with
  | int =>
      exact MachineSteps.trans MachineStep.int MachineSteps.refl
  | bool =>
      exact MachineSteps.trans MachineStep.bool MachineSteps.refl
  | var hlookup =>
      exact MachineSteps.trans (MachineStep.var hlookup) MachineSteps.refl
  | succ _ ih =>
      exact (MachineSteps.trans MachineStep.succ (ih)).append
        (MachineSteps.trans MachineStep.succ_int MachineSteps.refl)
  | pred _ ih =>
      exact (MachineSteps.trans MachineStep.pred (ih)).append
        (MachineSteps.trans MachineStep.pred_int MachineSteps.refl)
  | plus _ _ ih₁ ih₂ =>
      exact (MachineSteps.trans MachineStep.plus ih₁).append
        ((MachineSteps.trans MachineStep.plus_left ih₂).append
          (MachineSteps.trans MachineStep.plus_right_int MachineSteps.refl))
  | times _ _ ih₁ ih₂ =>
      exact (MachineSteps.trans MachineStep.times ih₁).append
        ((MachineSteps.trans MachineStep.times_left ih₂).append
          (MachineSteps.trans MachineStep.times_right_int MachineSteps.refl))
  | numEq _ _ ih₁ ih₂ =>
      exact (MachineSteps.trans MachineStep.numEq ih₁).append
        ((MachineSteps.trans MachineStep.numEq_left ih₂).append
          (MachineSteps.trans MachineStep.numEq_right_int MachineSteps.refl))
  | ite_true _ _ ih₁ ih₂ =>
      exact (MachineSteps.trans MachineStep.ite ih₁).append
        (MachineSteps.trans MachineStep.ite_true ih₂)
  | ite_false _ _ ih₁ ih₂ =>
      exact (MachineSteps.trans MachineStep.ite ih₁).append
        (MachineSteps.trans MachineStep.ite_false ih₂)
  | letE _ _ ih₁ ih₂ =>
      exact (MachineSteps.trans MachineStep.letE ih₁).append
        (MachineSteps.trans MachineStep.let_body ih₂)

theorem Eval.to_MachineEval : Eval [] e v → MachineEval e v := by
  intro h
  exact h.machine_run

theorem StepEval.to_MachineEval : StepEval e v → MachineEval e v := by
  intro h
  exact h.to_Eval.to_MachineEval

inductive StackEval : Stack → Value → Value → Prop where
  | nil : StackEval [] v v
  | succ :
      StackEval κ (.int (n + 1)) v →
      StackEval (.succ :: κ) (.int n) v
  | pred :
      StackEval κ (.int (n - 1)) v →
      StackEval (.pred :: κ) (.int n) v
  | plus_left :
      Eval ρ e₂ (.int n₂) →
      StackEval κ (.int (n₁ + n₂)) v →
      StackEval (.plus_left e₂ ρ :: κ) (.int n₁) v
  | plus_right :
      StackEval κ (.int (n₁ + n₂)) v →
      StackEval (.plus_right (.int n₁) :: κ) (.int n₂) v
  | times_left :
      Eval ρ e₂ (.int n₂) →
      StackEval κ (.int (n₁ * n₂)) v →
      StackEval (.times_left e₂ ρ :: κ) (.int n₁) v
  | times_right :
      StackEval κ (.int (n₁ * n₂)) v →
      StackEval (.times_right (.int n₁) :: κ) (.int n₂) v
  | numEq_left :
      Eval ρ e₂ (.int n₂) →
      StackEval κ (.bool (n₁ == n₂)) v →
      StackEval (.numEq_left e₂ ρ :: κ) (.int n₁) v
  | numEq_right :
      StackEval κ (.bool (n₁ == n₂)) v →
      StackEval (.numEq_right (.int n₁) :: κ) (.int n₂) v
  | ite_true :
      Eval ρ e₂ v₂ →
      StackEval κ v₂ v →
      StackEval (.ite e₂ e₃ ρ :: κ) (.bool true) v
  | ite_false :
      Eval ρ e₃ v₃ →
      StackEval κ v₃ v →
      StackEval (.ite e₂ e₃ ρ :: κ) (.bool false) v
  | letE :
      Eval (ρ.extend x v₁) e₂ v₂ →
      StackEval κ v₂ v →
      StackEval (.letE x e₂ ρ :: κ) v₁ v

def StateEval : State → Value → Prop
  | .eval ρ e κ, v => ∃ v', Eval ρ e v' ∧ StackEval κ v' v
  | .ret v' κ, v => StackEval κ v' v

theorem MachineStep.sound (h : MachineStep s s') : StateEval s' v → StateEval s v := by
  intro hs'
  cases h with
  | int =>
      exact ⟨.int _, Eval.int, hs'⟩
  | bool =>
      exact ⟨.bool _, Eval.bool, hs'⟩
  | var hlookup =>
      exact ⟨_, Eval.var hlookup, hs'⟩
  | succ =>
      rcases hs' with ⟨_, he, hκ⟩
      cases hκ with
      | succ hκ =>
          exact ⟨_, Eval.succ he, hκ⟩
  | pred =>
      rcases hs' with ⟨_, he, hκ⟩
      cases hκ with
      | pred hκ =>
          exact ⟨_, Eval.pred he, hκ⟩
  | plus =>
      rcases hs' with ⟨_, he₁, hκ⟩
      cases hκ with
      | plus_left he₂ hκ =>
          exact ⟨_, Eval.plus he₁ he₂, hκ⟩
  | times =>
      rcases hs' with ⟨_, he₁, hκ⟩
      cases hκ with
      | times_left he₂ hκ =>
          exact ⟨_, Eval.times he₁ he₂, hκ⟩
  | numEq =>
      rcases hs' with ⟨_, he₁, hκ⟩
      cases hκ with
      | numEq_left he₂ hκ =>
          exact ⟨_, Eval.numEq he₁ he₂, hκ⟩
  | ite =>
      rcases hs' with ⟨_, he₁, hκ⟩
      cases hκ with
      | ite_true he₂ hκ =>
          exact ⟨_, Eval.ite_true he₁ he₂, hκ⟩
      | ite_false he₃ hκ =>
          exact ⟨_, Eval.ite_false he₁ he₃, hκ⟩
  | letE =>
      rcases hs' with ⟨_, he₁, hκ⟩
      cases hκ with
      | letE he₂ hκ =>
          exact ⟨_, Eval.letE he₁ he₂, hκ⟩
  | succ_int =>
      exact StackEval.succ hs'
  | pred_int =>
      exact StackEval.pred hs'
  | plus_left =>
      rcases hs' with ⟨_, he₂, hκ⟩
      cases hκ with
      | plus_right hκ =>
          exact StackEval.plus_left he₂ hκ
  | plus_right_int =>
      exact StackEval.plus_right hs'
  | times_left =>
      rcases hs' with ⟨_, he₂, hκ⟩
      cases hκ with
      | times_right hκ =>
          exact StackEval.times_left he₂ hκ
  | times_right_int =>
      exact StackEval.times_right hs'
  | numEq_left =>
      rcases hs' with ⟨_, he₂, hκ⟩
      cases hκ with
      | numEq_right hκ =>
          exact StackEval.numEq_left he₂ hκ
  | numEq_right_int =>
      exact StackEval.numEq_right hs'
  | ite_true =>
      rcases hs' with ⟨_, he₂, hκ⟩
      exact StackEval.ite_true he₂ hκ
  | ite_false =>
      rcases hs' with ⟨_, he₃, hκ⟩
      exact StackEval.ite_false he₃ hκ
  | let_body =>
      rcases hs' with ⟨_, he₂, hκ⟩
      exact StackEval.letE he₂ hκ

theorem MachineSteps.sound (h : MachineSteps s s') : StateEval s' v → StateEval s v := by
  intro hs'
  induction h with
  | refl =>
      exact hs'
  | trans h _ ih =>
      exact h.sound (ih hs')

theorem MachineEval.to_Eval : MachineEval e v → Eval [] e v := by
  intro h
  have hs : StateEval (.eval [] e []) v :=
    h.sound (StackEval.nil : StateEval (.ret v []) v)
  rcases hs with ⟨v', he, hκ⟩
  cases hκ
  exact he

theorem MachineEval.iff_Eval : MachineEval e v ↔ Eval [] e v :=
  ⟨MachineEval.to_Eval, Eval.to_MachineEval⟩

theorem MachineEval.iff_StepEval : MachineEval e v ↔ StepEval e v := by
  rw [MachineEval.iff_Eval, StepEval.iff_Eval]

example : MachineEval (.plus (.int 1) (.int 2)) (.int 3) :=
  MachineSteps.trans MachineStep.plus
    (MachineSteps.trans MachineStep.int
      (MachineSteps.trans MachineStep.plus_left
        (MachineSteps.trans MachineStep.int
          (MachineSteps.trans MachineStep.plus_right_int MachineSteps.refl))))

example : MachineEval (.letE "x" (.int 4) (.plus (.var "x") (.int 3))) (.int 7) :=
  MachineSteps.trans MachineStep.letE
    (MachineSteps.trans MachineStep.int
      (MachineSteps.trans MachineStep.let_body
        (MachineSteps.trans MachineStep.plus
          (MachineSteps.trans (MachineStep.var rfl)
            (MachineSteps.trans MachineStep.plus_left
              (MachineSteps.trans MachineStep.int
                (MachineSteps.trans MachineStep.plus_right_int MachineSteps.refl)))))))

example : MachineEval
    (.ite (.numEq (.int 2) (.int 2)) (.succ (.int 4)) (.int 0)) (.int 5) :=
  MachineSteps.trans MachineStep.ite
    (MachineSteps.trans MachineStep.numEq
      (MachineSteps.trans MachineStep.int
        (MachineSteps.trans MachineStep.numEq_left
          (MachineSteps.trans MachineStep.int
            (MachineSteps.trans MachineStep.numEq_right_int
              (MachineSteps.trans MachineStep.ite_true
                (MachineSteps.trans MachineStep.succ
                  (MachineSteps.trans MachineStep.int
                    (MachineSteps.trans MachineStep.succ_int MachineSteps.refl)))))))))

end Semantics.Extended

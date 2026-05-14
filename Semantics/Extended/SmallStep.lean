import Semantics.Extended.BigStep

namespace Semantics.Extended

inductive IsValue : Expr → Prop where
  | int : IsValue (.int n)
  | bool : IsValue (.bool b)

def Value.toExpr : Value → Expr
  | .int n => .int n
  | .bool b => .bool b

def substValue (x : String) (v : Value) : Expr → Expr
  | .int n => .int n
  | .bool b => .bool b
  | .var y => if y == x then v.toExpr else .var y
  | .succ e => .succ (substValue x v e)
  | .pred e => .pred (substValue x v e)
  | .plus e₁ e₂ => .plus (substValue x v e₁) (substValue x v e₂)
  | .times e₁ e₂ => .times (substValue x v e₁) (substValue x v e₂)
  | .numEq e₁ e₂ => .numEq (substValue x v e₁) (substValue x v e₂)
  | .ite e₁ e₂ e₃ => .ite (substValue x v e₁) (substValue x v e₂) (substValue x v e₃)
  | .letE y e₁ e₂ =>
      if y == x then
        .letE y (substValue x v e₁) e₂
      else
        .letE y (substValue x v e₁) (substValue x v e₂)

inductive Step : Expr → Expr → Prop where
  | succ : Step (.succ (.int n)) (.int (n + 1))
  | pred : Step (.pred (.int n)) (.int (n - 1))
  | plus : Step (.plus (.int n₁) (.int n₂)) (.int (n₁ + n₂))
  | times : Step (.times (.int n₁) (.int n₂)) (.int (n₁ * n₂))
  | numEq : Step (.numEq (.int n₁) (.int n₂)) (.bool (n₁ == n₂))
  | ite_true : Step (.ite (.bool true) e₂ e₃) e₂
  | ite_false : Step (.ite (.bool false) e₂ e₃) e₃
  | let_int : Step (.letE x (.int n) e) (substValue x (.int n) e)
  | let_bool : Step (.letE x (.bool b) e) (substValue x (.bool b) e)
  | succ_step : Step e e' → Step (.succ e) (.succ e')
  | pred_step : Step e e' → Step (.pred e) (.pred e')
  | plus_left : Step e₁ e₁' → Step (.plus e₁ e₂) (.plus e₁' e₂)
  | plus_right : IsValue v₁ → Step e₂ e₂' → Step (.plus v₁ e₂) (.plus v₁ e₂')
  | times_left : Step e₁ e₁' → Step (.times e₁ e₂) (.times e₁' e₂)
  | times_right : IsValue v₁ → Step e₂ e₂' → Step (.times v₁ e₂) (.times v₁ e₂')
  | numEq_left : Step e₁ e₁' → Step (.numEq e₁ e₂) (.numEq e₁' e₂)
  | numEq_right : IsValue v₁ → Step e₂ e₂' → Step (.numEq v₁ e₂) (.numEq v₁ e₂')
  | ite_cond : Step e₁ e₁' → Step (.ite e₁ e₂ e₃) (.ite e₁' e₂ e₃)
  | let_step : Step e₁ e₁' → Step (.letE x e₁ e₂) (.letE x e₁' e₂)

inductive Steps : Expr → Expr → Prop where
  | refl : Steps e e
  | trans : Step e₁ e₂ → Steps e₂ e₃ → Steps e₁ e₃

theorem Steps.single (h : Step e e') : Steps e e' :=
  Steps.trans h Steps.refl

theorem Steps.append : Steps e₁ e₂ → Steps e₂ e₃ → Steps e₁ e₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl =>
      exact h₂
  | trans h _ ih =>
      exact Steps.trans h (ih h₂)

theorem Steps.succ : Steps e e' → Steps (.succ e) (.succ e') := by
  intro h
  induction h with
  | refl => exact Steps.refl
  | trans h _ ih => exact Steps.trans (Step.succ_step h) ih

theorem Steps.pred : Steps e e' → Steps (.pred e) (.pred e') := by
  intro h
  induction h with
  | refl => exact Steps.refl
  | trans h _ ih => exact Steps.trans (Step.pred_step h) ih

theorem Steps.plus_left : Steps e₁ e₁' → Steps (.plus e₁ e₂) (.plus e₁' e₂) := by
  intro h
  induction h with
  | refl => exact Steps.refl
  | trans h _ ih => exact Steps.trans (Step.plus_left h) ih

theorem Steps.plus_right :
    IsValue v₁ → Steps e₂ e₂' → Steps (.plus v₁ e₂) (.plus v₁ e₂') := by
  intro hv h
  induction h with
  | refl => exact Steps.refl
  | trans h _ ih => exact Steps.trans (Step.plus_right hv h) ih

theorem Steps.times_left : Steps e₁ e₁' → Steps (.times e₁ e₂) (.times e₁' e₂) := by
  intro h
  induction h with
  | refl => exact Steps.refl
  | trans h _ ih => exact Steps.trans (Step.times_left h) ih

theorem Steps.times_right :
    IsValue v₁ → Steps e₂ e₂' → Steps (.times v₁ e₂) (.times v₁ e₂') := by
  intro hv h
  induction h with
  | refl => exact Steps.refl
  | trans h _ ih => exact Steps.trans (Step.times_right hv h) ih

theorem Steps.numEq_left : Steps e₁ e₁' → Steps (.numEq e₁ e₂) (.numEq e₁' e₂) := by
  intro h
  induction h with
  | refl => exact Steps.refl
  | trans h _ ih => exact Steps.trans (Step.numEq_left h) ih

theorem Steps.numEq_right :
    IsValue v₁ → Steps e₂ e₂' → Steps (.numEq v₁ e₂) (.numEq v₁ e₂') := by
  intro hv h
  induction h with
  | refl => exact Steps.refl
  | trans h _ ih => exact Steps.trans (Step.numEq_right hv h) ih

theorem Steps.ite_cond : Steps e₁ e₁' → Steps (.ite e₁ e₂ e₃) (.ite e₁' e₂ e₃) := by
  intro h
  induction h with
  | refl => exact Steps.refl
  | trans h _ ih => exact Steps.trans (Step.ite_cond h) ih

theorem Steps.let_step : Steps e₁ e₁' → Steps (.letE x e₁ e₂) (.letE x e₁' e₂) := by
  intro h
  induction h with
  | refl => exact Steps.refl
  | trans h _ ih => exact Steps.trans (Step.let_step h) ih

theorem Value.eval_toExpr (ρ : Env) : eval ρ v.toExpr = some v := by
  cases v <;> rfl

theorem Value.toExpr_isValue (v : Value) : IsValue v.toExpr := by
  cases v <;> constructor

theorem substValue_toExpr (x : String) (v w : Value) :
    substValue x v w.toExpr = w.toExpr := by
  cases w <;> rfl

theorem Env.lookup_shadow (ρ : Env) (x y : String) (v w : Value) :
    Env.lookup ((x, v) :: (x, w) :: ρ) y = Env.lookup ((x, v) :: ρ) y := by
  by_cases h : y = x
  · subst h
    simp [Env.lookup]
  · simp [Env.lookup, h]

theorem Env.lookup_swap (ρ : Env) (x y z : String) (v w : Value) (hxy : x ≠ y) :
    Env.lookup ((x, v) :: (y, w) :: ρ) z = Env.lookup ((y, w) :: (x, v) :: ρ) z := by
  by_cases hzx : z = x
  · subst hzx
    simp [Env.lookup, hxy]
  · by_cases hzy : z = y
    · subst hzy
      simp [Env.lookup, hzx]
    · simp [Env.lookup, hzx, hzy]

theorem eval_congr_env {ρ ρ' : Env} (hρ : ∀ x, Env.lookup ρ x = Env.lookup ρ' x) :
    eval ρ e = eval ρ' e := by
  induction e generalizing ρ ρ' with
  | int n =>
      rfl
  | bool b =>
      rfl
  | var x =>
      exact hρ x
  | succ e ih =>
      simp [eval, ih hρ]
  | pred e ih =>
      simp [eval, ih hρ]
  | plus e₁ e₂ ih₁ ih₂ =>
      simp [eval, ih₁ hρ, ih₂ hρ]
  | times e₁ e₂ ih₁ ih₂ =>
      simp [eval, ih₁ hρ, ih₂ hρ]
  | numEq e₁ e₂ ih₁ ih₂ =>
      simp [eval, ih₁ hρ, ih₂ hρ]
  | ite e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
      simp [eval, ih₁ hρ, ih₂ hρ, ih₃ hρ]
  | letE x e₁ e₂ ih₁ ih₂ =>
      simp only [eval]
      rw [ih₁ hρ]
      cases h : eval ρ' e₁ with
      | none =>
          rfl
      | some v =>
        exact ih₂ (fun y => by
          by_cases hyx : y = x
          · subst hyx
            simp [Env.extend, Env.lookup]
          · simp [Env.extend, Env.lookup, hyx, hρ y])

theorem eval_substValue (ρ : Env) (x : String) (v : Value) (e : Expr) :
    eval ρ (substValue x v e) = eval (ρ.extend x v) e := by
  induction e generalizing ρ x v with
  | int n =>
      rfl
  | bool b =>
      rfl
  | var y =>
      by_cases h : y = x
      · subst h
        simp [substValue, eval, Env.extend, Env.lookup, Value.eval_toExpr]
      · simp [substValue, eval, Env.extend, Env.lookup, h]
  | succ e ih =>
      simp [substValue, eval, ih]
  | pred e ih =>
      simp [substValue, eval, ih]
  | plus e₁ e₂ ih₁ ih₂ =>
      simp [substValue, eval, ih₁, ih₂]
  | times e₁ e₂ ih₁ ih₂ =>
      simp [substValue, eval, ih₁, ih₂]
  | numEq e₁ e₂ ih₁ ih₂ =>
      simp [substValue, eval, ih₁, ih₂]
  | ite e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
      simp [substValue, eval, ih₁, ih₂, ih₃]
  | letE y e₁ e₂ ih₁ ih₂ =>
      by_cases hyx : y = x
      · subst hyx
        simp [substValue, eval, ih₁]
        split
        · next v₁ _ =>
          exact eval_congr_env (e := e₂) (fun z => by
            exact (Env.lookup_shadow ρ y z v₁ v).symm)
        · rfl
      · simp [substValue, eval, hyx, ih₁, ih₂, Env.extend]
        split
        · next v₁ _ =>
          exact eval_congr_env (e := e₂) (fun z => by
            exact Env.lookup_swap ρ x y z v v₁ (fun h => hyx h.symm))
        · rfl

theorem Step.eval_eq (h : Step e e') : eval ρ e = eval ρ e' := by
  induction h generalizing ρ with
  | succ =>
      rfl
  | pred =>
      rfl
  | plus =>
      rfl
  | times =>
      rfl
  | numEq =>
      rfl
  | ite_true =>
      rfl
  | ite_false =>
      rfl
  | let_int =>
      exact (eval_substValue ρ _ (.int _) _).symm
  | let_bool =>
      exact (eval_substValue ρ _ (.bool _) _).symm
  | succ_step _ ih =>
      simp [eval, ih]
  | pred_step _ ih =>
      simp [eval, ih]
  | plus_left _ ih =>
      simp [eval, ih]
  | plus_right hv _ ih =>
      cases hv with
      | int => simp [eval, ih]
      | bool => simp [eval]
  | times_left _ ih =>
      simp [eval, ih]
  | times_right hv _ ih =>
      cases hv with
      | int => simp [eval, ih]
      | bool => simp [eval]
  | numEq_left _ ih =>
      simp [eval, ih]
  | numEq_right hv _ ih =>
      cases hv with
      | int => simp [eval, ih]
      | bool => simp [eval]
  | ite_cond _ ih =>
      simp [eval, ih]
  | let_step _ ih =>
      simp [eval, ih]

theorem Steps.eval_eq (h : Steps e e') : eval ρ e = eval ρ e' := by
  induction h with
  | refl =>
      rfl
  | trans h _ ih =>
      exact h.eval_eq.trans ih

def StepEval (e : Expr) (v : Value) : Prop :=
  Steps e v.toExpr

theorem StepEval.to_Eval : StepEval e v → Eval [] e v := by
  intro h
  apply Eval.of_eval_eq
  rw [h.eval_eq]
  exact Value.eval_toExpr []

def Env.erase (ρ : Env) (x : String) : Env :=
  match ρ with
  | [] => []
  | (y, v) :: ρ => if y = x then erase ρ x else (y, v) :: erase ρ x

def substEnv (ρ : Env) : Expr → Expr
  | .int n => .int n
  | .bool b => .bool b
  | .var x =>
      match ρ.lookup x with
      | some v => v.toExpr
      | none => .var x
  | .succ e => .succ (substEnv ρ e)
  | .pred e => .pred (substEnv ρ e)
  | .plus e₁ e₂ => .plus (substEnv ρ e₁) (substEnv ρ e₂)
  | .times e₁ e₂ => .times (substEnv ρ e₁) (substEnv ρ e₂)
  | .numEq e₁ e₂ => .numEq (substEnv ρ e₁) (substEnv ρ e₂)
  | .ite e₁ e₂ e₃ => .ite (substEnv ρ e₁) (substEnv ρ e₂) (substEnv ρ e₃)
  | .letE x e₁ e₂ => .letE x (substEnv ρ e₁) (substEnv (ρ.erase x) e₂)

theorem Env.erase_cons_same (ρ : Env) (x : String) (v : Value) :
    Env.erase ((x, v) :: ρ) x = ρ.erase x := by
  simp [Env.erase]

theorem Env.erase_cons_ne (ρ : Env) {x y : String} (v : Value) (hxy : x ≠ y) :
    Env.erase ((x, v) :: ρ) y = (x, v) :: ρ.erase y := by
  simp [Env.erase, hxy]

theorem Env.erase_idem (ρ : Env) (x : String) :
    (ρ.erase x).erase x = ρ.erase x := by
  induction ρ with
  | nil =>
      rfl
  | cons xv ρ ih =>
      cases xv with
      | mk y v =>
          by_cases hyx : y = x
          · subst hyx
            simp [Env.erase, ih]
          · simp [Env.erase, hyx, ih]

theorem Env.erase_comm (ρ : Env) (x y : String) :
    (ρ.erase x).erase y = (ρ.erase y).erase x := by
  induction ρ with
  | nil =>
      rfl
  | cons xv ρ ih =>
      cases xv with
      | mk z v =>
          by_cases hzx : z = x
          · subst hzx
            by_cases hzy : z = y
            · subst hzy
              simp [Env.erase]
            · simp [Env.erase, hzy, ih]
          · by_cases hzy : z = y
            · subst hzy
              simp [Env.erase, hzx, ih]
            · simp [Env.erase, hzx, hzy, ih]

theorem Env.lookup_erase_same (ρ : Env) (x : String) :
    (ρ.erase x).lookup x = none := by
  induction ρ with
  | nil =>
      rfl
  | cons xv ρ ih =>
      cases xv with
      | mk y v =>
          by_cases hyx : y = x
          · subst hyx
            simp [Env.erase, ih]
          · have hxy : x ≠ y := fun h => hyx h.symm
            simp [Env.erase, Env.lookup, hyx, hxy, ih]

theorem Env.lookup_erase_ne (ρ : Env) {x y : String} (hyx : y ≠ x) :
    (ρ.erase x).lookup y = ρ.lookup y := by
  induction ρ with
  | nil =>
      rfl
  | cons xv ρ ih =>
      cases xv with
      | mk z v =>
          by_cases hzx : z = x
          · subst hzx
            simp [Env.erase, Env.lookup, hyx, ih]
          · simp [Env.erase, Env.lookup, hzx, ih]

theorem substEnv_extend (ρ : Env) (x : String) (v : Value) (e : Expr) :
    substEnv ((x, v) :: ρ) e = substValue x v (substEnv (ρ.erase x) e) := by
  induction e generalizing ρ x v with
  | int n =>
      rfl
  | bool b =>
      rfl
  | var y =>
      by_cases hyx : y = x
      · subst hyx
        simp [substEnv, substValue, Env.lookup, Env.lookup_erase_same]
      · cases hlookup : ρ.lookup y with
        | none =>
            have hcons : Env.lookup ((x, v) :: ρ) y = none := by
              simp [Env.lookup, hyx, hlookup]
            have herase : (ρ.erase x).lookup y = none := by
              rw [Env.lookup_erase_ne ρ hyx, hlookup]
            simp [substEnv, hcons, herase, substValue, hyx]
        | some w =>
            have hcons : Env.lookup ((x, v) :: ρ) y = some w := by
              simp [Env.lookup, hyx, hlookup]
            have herase : (ρ.erase x).lookup y = some w := by
              rw [Env.lookup_erase_ne ρ hyx, hlookup]
            simp [substEnv, hcons, herase, substValue_toExpr]
  | succ e ih =>
      simp [substEnv, substValue, ih]
  | pred e ih =>
      simp [substEnv, substValue, ih]
  | plus e₁ e₂ ih₁ ih₂ =>
      simp [substEnv, substValue, ih₁, ih₂]
  | times e₁ e₂ ih₁ ih₂ =>
      simp [substEnv, substValue, ih₁, ih₂]
  | numEq e₁ e₂ ih₁ ih₂ =>
      simp [substEnv, substValue, ih₁, ih₂]
  | ite e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
      simp [substEnv, substValue, ih₁, ih₂, ih₃]
  | letE y e₁ e₂ ih₁ ih₂ =>
      by_cases hyx : y = x
      · subst hyx
        simp [substEnv, substValue, ih₁, Env.erase_cons_same, Env.erase_idem]
      · simp [substEnv, substValue, hyx, ih₁]
        have hxy : x ≠ y := fun h => hyx h.symm
        rw [Env.erase_cons_ne (x := x) (y := y) ρ v hxy]
        rw [ih₂ (ρ.erase y) x v]
        rw [Env.erase_comm]

theorem substEnv_nil (e : Expr) : substEnv [] e = e := by
  induction e with
  | int n =>
      rfl
  | bool b =>
      rfl
  | var x =>
      rfl
  | succ e ih =>
      simp [substEnv, ih]
  | pred e ih =>
      simp [substEnv, ih]
  | plus e₁ e₂ ih₁ ih₂ =>
      simp [substEnv, ih₁, ih₂]
  | times e₁ e₂ ih₁ ih₂ =>
      simp [substEnv, ih₁, ih₂]
  | numEq e₁ e₂ ih₁ ih₂ =>
      simp [substEnv, ih₁, ih₂]
  | ite e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
      simp [substEnv, ih₁, ih₂, ih₃]
  | letE x e₁ e₂ ih₁ ih₂ =>
      simp [substEnv, Env.erase, ih₁, ih₂]

theorem Eval.to_Steps_substEnv : Eval ρ e v → Steps (substEnv ρ e) v.toExpr := by
  intro h
  induction h with
  | int =>
      exact Steps.refl
  | bool =>
      exact Steps.refl
  | var hlookup =>
      simp [substEnv, hlookup]
      exact Steps.refl
  | succ _ ih =>
      exact (Steps.succ ih).append (Steps.single Step.succ)
  | pred _ ih =>
      exact (Steps.pred ih).append (Steps.single Step.pred)
  | plus _ _ ih₁ ih₂ =>
      exact ((Steps.plus_left ih₁).append
        (Steps.plus_right (Value.toExpr_isValue _) ih₂)).append (Steps.single Step.plus)
  | times _ _ ih₁ ih₂ =>
      exact ((Steps.times_left ih₁).append
        (Steps.times_right (Value.toExpr_isValue _) ih₂)).append (Steps.single Step.times)
  | numEq _ _ ih₁ ih₂ =>
      exact ((Steps.numEq_left ih₁).append
        (Steps.numEq_right (Value.toExpr_isValue _) ih₂)).append (Steps.single Step.numEq)
  | ite_true _ _ ih₁ ih₂ =>
      exact (Steps.ite_cond ih₁).append ((Steps.single Step.ite_true).append ih₂)
  | ite_false _ _ ih₁ ih₂ =>
      exact (Steps.ite_cond ih₁).append ((Steps.single Step.ite_false).append ih₂)
  | letE h₁ h₂ ih₁ ih₂ =>
      rename_i ρ e₁ v₁ x e₂ v₂
      simp [substEnv]
      cases v₁ with
      | int n =>
          exact (Steps.let_step ih₁).append
            ((Steps.single Step.let_int).append (by
              rw [← substEnv_extend]
              exact ih₂))
      | bool b =>
          exact (Steps.let_step ih₁).append
            ((Steps.single Step.let_bool).append (by
              rw [← substEnv_extend]
              exact ih₂))

theorem Eval.to_StepEval : Eval [] e v → StepEval e v := by
  intro h
  simpa [StepEval, substEnv_nil] using h.to_Steps_substEnv

theorem StepEval.iff_Eval : StepEval e v ↔ Eval [] e v :=
  ⟨StepEval.to_Eval, Eval.to_StepEval⟩

example : substValue "x" (.int 4) (.plus (.var "x") (.int 3)) = .plus (.int 4) (.int 3) :=
  rfl

example : Step (.letE "x" (.int 4) (.plus (.var "x") (.int 3))) (.plus (.int 4) (.int 3)) :=
  Step.let_int

example : Steps (.letE "x" (.int 4) (.plus (.var "x") (.int 3))) (.int 7) :=
  Steps.trans Step.let_int (Steps.trans Step.plus Steps.refl)

example :
    Step (.letE "x" (.plus (.int 1) (.int 2)) (.succ (.var "x")))
      (.letE "x" (.int 3) (.succ (.var "x"))) :=
  Step.let_step Step.plus

end Semantics.Extended

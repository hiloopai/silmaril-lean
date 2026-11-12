module

public import Silmaril.Raw.SSA.Isotope.Morphism.SSAIter.Sum
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Structural

/-!
# Finite-sum operational semantics

Injection adds a finite label to a value without performing instructions.
Dispatch evaluates its scrutinee once, then evaluates the selected arm with its
payload in the newest slot. Intermediate sum binders leave ambient variables
unchanged.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.Morphism.SSAIter

open LetIter.LocallyNameless
open LetIter.Semantics

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q} {n k : Nat}

/-- The runtime representation of a finite label and its payload. -/
def tagValue : {k : Nat} → Fin k → Value α → Value α
  | _ + 1, i, value => Fin.cases (.inl value) (fun j => .inr (tagValue j value)) i

@[simp] theorem tagValue_zero (value : Value α) :
    tagValue (0 : Fin (k + 1)) value = .inl value := rfl

@[simp] theorem tagValue_succ (i : Fin k) (value : Value α) :
    tagValue i.succ value = .inr (tagValue i value) := rfl

variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}

/-- Tagging preserves the payload computation and its state transitions. -/
theorem inject_eval (i : Fin k) {bound : BoundEnv α n} {a : Tm ν Φ n}
    {s s' : σ} {value : Value α} (h : Eval instr free bound a s value s') :
    Eval instr free bound (inject i a) s (tagValue i value) s' := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact .inl h
      · exact .inr (ih j)

/-- Every result of an injection has exactly the chosen finite label. -/
theorem inject_eval_iff (i : Fin k) {bound : BoundEnv α n} {a : Tm ν Φ n}
    {s s' : σ} {result : Value α} :
    Eval instr free bound (inject i a) s result s' ↔
      ∃ value, Eval instr free bound a s value s' ∧ result = tagValue i value := by
  induction k generalizing result with
  | zero => exact i.elim0
  | succ k ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · constructor
        · intro h
          cases h with | inl arg => exact ⟨_, arg, rfl⟩
        · rintro ⟨value, h, rfl⟩
          exact inject_eval 0 h
      · constructor
        · intro h
          cases h with
          | inr arg =>
              obtain ⟨value, hv, he⟩ := (ih j).mp arg
              exact ⟨value, hv, congrArg Value.inr he⟩
        · rintro ⟨value, h, rfl⟩
          exact inject_eval j.succ h

/-- Weakening below the payload skips an intermediate sum value. -/
theorem eval_underBinder {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
    {payload intermediate result : Value α} {s s' : σ}
    (h : Eval instr free (extend bound payload) body s result s') :
    Eval instr free (extend (extend bound intermediate) payload)
      body.underBinder s result s' :=
  h.rename (Fin.cases 0 (fun i => i.succ.succ)) _
    (Fin.cases rfl (fun _ => rfl))

theorem eval_underBinder_iff {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
    {payload intermediate result : Value α} {s s' : σ} :
    Eval instr free (extend (extend bound intermediate) payload)
      body.underBinder s result s' ↔
      Eval instr free (extend bound payload) body s result s' :=
  Eval.rename_iff (Fin.cases rfl (fun _ => rfl))

/-- Finite dispatch executes only the selected arm, after the scrutinee. -/
theorem dispatch_eval (i : Fin k) {bound : BoundEnv α n} {a : Tm ν Φ n}
    {bs : Fin k → Tm ν Φ (n + 1)} {s s₁ s₂ : σ} {payload result : Value α}
    (ha : Eval instr free bound a s (tagValue i payload) s₁)
    (hb : Eval instr free (extend bound payload) (bs i) s₁ result s₂) :
    Eval instr free bound (dispatch a bs) s result s₂ := by
  induction k generalizing n s with
  | zero => exact i.elim0
  | succ k ih =>
      revert ha hb
      refine Fin.cases (fun ha hb => ?_) (fun j ha hb => ?_) i
      · exact .case_inl ha hb
      · exact .case_inr ha (ih j .bv (eval_underBinder hb))

/-- Every finite dispatch run chooses an actual finite label and runs precisely
its arm. This also excludes malformed tags, without instruction determinism. -/
theorem dispatch_eval_iff {bound : BoundEnv α n} {a : Tm ν Φ n}
    {bs : Fin k → Tm ν Φ (n + 1)} {s s' : σ} {result : Value α} :
    Eval instr free bound (dispatch a bs) s result s' ↔
      ∃ (i : Fin k) (payload : Value α) (mid : σ),
        Eval instr free bound a s (tagValue i payload) mid ∧
        Eval instr free (extend bound payload) (bs i) mid result s' := by
  constructor
  · intro h
    induction k generalizing n s with
    | zero => cases h
    | succ k ih =>
        cases h with
        | case_inl arg branch => exact ⟨0, _, _, arg, branch⟩
        | case_inr arg branch =>
            obtain ⟨i, payload, mid, lookup, chosen⟩ := ih branch
            cases lookup
            exact ⟨i.succ, payload, _, arg, eval_underBinder_iff.mp chosen⟩
  · rintro ⟨i, payload, mid, arg, branch⟩
    exact dispatch_eval i arg branch

/-- Reaching the third arm preserves the ambient value below its payload; the
two unselected arms may be stuck, and the scrutinee performs one instruction. -/
example (f : Φ) (input payload : Value α) (s s' : σ)
    (step : instr f input s payload s') :
    let arms : Fin 3 → Tm ν Φ 2 :=
      Fin.cases (.abort .unit) (Fin.cases (.abort .unit) (fun _ => .pair (.bv 0) (.bv 1)))
    Eval instr free (fun _ : Fin 1 => input)
      (dispatch (inject (2 : Fin 3) (.op f (.bv 0))) arms)
      s (.pair payload input) s' :=
  dispatch_eval (2 : Fin 3) (inject_eval _ (.op .bv step)) (.pair .bv .bv)

end Silmaril.Isotope.Morphism.SSAIter

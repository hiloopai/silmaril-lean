module

public import Silmaril.Compiler.C.Sem.C0.Defs
@[expose] public section

/-!
# Stability of C0 under additional fuel

The flat approximation relation below treats exhaustion as the only unfinished result.
It preserves all other errors as well as successful values, including the complete store
and output. Its bind and list-loop laws allow one simultaneous induction for the five
mutually recursive interpreter functions.
-/

namespace Silmaril.Compile.C.Sem.C0

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C

/-- A computation may become more defined only when it exhausted its fuel. -/
def Approx {α : Type} (a b : Except Stop α) : Prop :=
  a ≠ .error .outOfFuel → b = a

private theorem approx_refl {α : Type} (a : Except Stop α) : Approx a a :=
  fun _ => rfl

private theorem approx_bottom {α : Type} (a : Except Stop α) :
    Approx (.error .outOfFuel) a := fun h => False.elim (h rfl)

private theorem approx_bind {α β : Type} {a b : Except Stop α}
    {f g : α → Except Stop β} (ha : Approx a b) (hf : ∀ x, Approx (f x) (g x)) :
    Approx (a >>= f) (b >>= g) := by
  cases a with
  | error e =>
    cases e <;> simp_all [Approx, Bind.bind, Except.bind]
  | ok x =>
    have hb := ha (by intro h; cases h)
    subst b
    exact hf x

private theorem approx_forIn {α β : Type} (xs : List α) (b : β)
    (f g : α → β → Except Stop (ForInStep β))
    (h : ∀ x b, Approx (f x b) (g x b)) :
    Approx (forIn xs b f) (forIn xs b g) := by
  induction xs generalizing b with
  | nil => exact approx_refl _
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply approx_bind (h x b)
    intro s
    cases s with
    | done b => exact approx_refl _
    | yield b => exact ih b

local macro "fuel_mono" : tactic => `(tactic|
  repeat' first
    | exact approx_refl _
    | assumption
    | solve_by_elim (maxDepth := 3)
    | apply approx_bind
    | apply approx_forIn
    | split
    | intro
)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
private theorem mutual_mono (P : Prog) (n k : Nat) :
    (∀ fd e env, Approx (evalE P n fd e env) (evalE P (n + k) fd e env)) ∧
    (∀ fd pts es env, Approx (evalArgs P n fd pts es env) (evalArgs P (n + k) fd pts es env)) ∧
    (∀ g vs env, Approx (callFn P n g vs env) (callFn P (n + k) g vs env)) ∧
    (∀ fd focus c env, Approx (loop P n fd focus c env) (loop P (n + k) fd focus c env)) ∧
    (∀ fd focus c env, Approx (step P n fd focus c env) (step P (n + k) fd focus c env)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> exact approx_bottom _
  | succ n ih =>
    rcases ih with ⟨he, ha, hc, hl, hs⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro fd e env
      cases h : e.node <;> simp only [Nat.succ_add, evalE, h]
      all_goals fuel_mono
    · intro fd pts es env
      cases es <;> simp only [Nat.succ_add, evalArgs]
      all_goals fuel_mono
    · intro g vs env
      simp only [Nat.succ_add, callFn]
      fuel_mono
    · intro fd focus c env
      simp only [Nat.succ_add, loop]
      have h := hs fd focus c env
      cases hstep : step P n fd focus c env with
      | error e =>
        by_cases hf : e = .outOfFuel
        · subst e
          exact approx_bottom _
        · have eq := h (by simp [hstep, hf])
          simp only [eq, hstep]
          exact approx_refl _
      | ok x =>
        have eq := h (by simp [hstep])
        simp only [eq, hstep]
        rcases x with ⟨next, env'⟩
        cases next with
        | running focus c => exact hl fd focus c env'
        | returned v => exact approx_refl _
    · intro fd focus c env
      cases focus <;> simp only [Nat.succ_add, step]
      all_goals fuel_mono

/-- Expression evaluation preserves every result other than exhaustion. -/
theorem evalE_mono (P : Prog) (n k : Nat) (fd : FunDef) (e : TypedExpression) (env : Env) :
    Approx (evalE P n fd e env) (evalE P (n + k) fd e env) :=
  (mutual_mono P n k).1 fd e env

/-- Statement execution preserves every result other than exhaustion. -/
theorem loop_mono (P : Prog) (n k : Nat) (fd : FunDef)
    (focus : Option TypedStatement) (c : Kont) (env : Env) :
    Approx (loop P n fd focus c env) (loop P (n + k) fd focus c env) :=
  (mutual_mono P n k).2.2.2.1 fd focus c env

/-- A call preserves every result other than exhaustion. -/
theorem callFn_mono (P : Prog) (n k : Nat) (g : Silmaril.Cerberus.Sym) (vs : List Int) (env : Env) :
    Approx (callFn P n g vs env) (callFn P (n + k) g vs env) :=
  (mutual_mono P n k).2.2.1 g vs env

/-- One step of the statement machine preserves every result other than exhaustion. -/
theorem step_mono (P : Prog) (n k : Nat) (fd : FunDef)
    (focus : Option TypedStatement) (c : Kont) (env : Env) :
    Approx (step P n fd focus c env) (step P (n + k) fd focus c env) :=
  (mutual_mono P n k).2.2.2.2 fd focus c env

private theorem initGlobals_mono (P : Prog) (n k : Nat)
    (gs : List (Nat × CType × Option TypedExpression)) (env : Env) :
    Approx (initGlobals P n gs env) (initGlobals P (n + k) gs env) := by
  induction gs generalizing env with
  | nil => exact approx_refl _
  | cons g gs ih =>
    rcases g with ⟨x, t, init⟩
    simp only [initGlobals]
    have he := evalE_mono P n k
    fuel_mono

private def finish : Except Stop (Int × Env) → Result
  | .ok (v, env) => .done ⟨env.out.toList, toStatus v⟩
  | .error (.exit c out) => .done ⟨out.toList, toStatus c⟩
  | .error (.abort out) => .done ⟨out.toList, .signal 6⟩
  | .error (.undefined why) => .undefined why
  | .error .outOfFuel => .outOfFuel
  | .error (.unsupported why) => .unsupported why

private theorem finish_mono {a b : Except Stop (Int × Env)} (h : Approx a b)
    (hn : finish a ≠ .outOfFuel) : finish b = finish a := by
  apply congrArg finish (h ?_)
  intro he
  subst a
  exact hn rfl

/-- Additional fuel leaves a completed result (including errors) unchanged. -/
theorem run_mono (n k : Nat) (p : TypedProgram) (r : Result)
    (hr : run n p = r) (hn : r ≠ .outOfFuel) : run (n + k) p = r := by
  subst r
  apply finish_mono ?_ hn
  -- The outer observation map is definitionally `finish`; only its input uses fuel.
  apply approx_bind (initGlobals_mono (prepare p) n k _ _)
  intro env
  have hl := loop_mono (prepare p) n k
  fuel_mono

/-- Two non-exhausted runs agree by extending both to the sum of their fuel bounds. -/
theorem run_agree {n m : Nat} {p : TypedProgram} {r s : Result}
    (hr : run n p = r) (hs : run m p = s)
    (hn : r ≠ .outOfFuel) (hm : s ≠ .outOfFuel) : r = s := by
  have h₁ := run_mono n m p r hr hn
  have h₂ := run_mono m n p s hs hm
  rw [Nat.add_comm m n] at h₂
  exact h₁.symm.trans h₂

/-- C0 has at most one observation, unless it encounters undefined behaviour. -/
theorem beh_subsingleton_or_univ (p : TypedProgram) :
    (beh p).Subsingleton ∨ beh p = Set.univ := by
  by_cases hu : ∃ n why, run n p = .undefined why
  · obtain ⟨n, why, h⟩ := hu
    exact .inr (beh_of_undefined h)
  · left
    intro o ho o' ho'
    rcases ho with ⟨n, hn⟩ | hu' | ⟨rfl, hn⟩
    · rcases ho' with ⟨m, hm⟩ | hu' | ⟨rfl, hm⟩
      · have h := run_agree hn hm (by intro h; cases h) (by intro h; cases h)
        cases h
        rfl
      · exact False.elim (hu hu')
      · have h := hn.symm.trans (hm n)
        cases h
    · exact False.elim (hu hu')
    · rcases ho' with ⟨m, hm⟩ | hu' | ⟨rfl, _⟩
      · have h := hm.symm.trans (hn m)
        cases h
      · exact False.elim (hu hu')
      · rfl

end Silmaril.Compile.C.Sem.C0

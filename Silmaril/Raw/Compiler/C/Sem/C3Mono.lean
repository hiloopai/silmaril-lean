module

public import Silmaril.Compiler.C.Sem.C3.Defs
public import Silmaril.Compiler.C.Sem.FuelMono.Defs
@[expose] public section

/-!
# Stability of C3 under additional fuel

One simultaneous induction for the nine mutually recursive interpreter functions, with the
approximation laws of `FuelMono`; then `run_mono`, `run_agree` and determinism. Each
function's inductive step is its own lemma over the bundled hypothesis `Mono P n k`.
-/

namespace Silmaril.Compile.C.Sem.C3

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C
open C0 (Stop Result Kont)
open C1 (Env FunDef)
open C2 (Val)
open FuelMono

/-- Every interpreter function at fuel `n` approximates itself at fuel `n + k`. -/
private def Mono (P : Prog) (n k : Nat) : Prop :=
  (∀ fd e env, Approx (evalL P n fd e env) (evalL P (n + k) fd e env)) ∧
  (∀ fd e env, Approx (evalA P n fd e env) (evalA P (n + k) fd e env)) ∧
  (∀ fd e env, Approx (evalD P n fd e env) (evalD P (n + k) fd e env)) ∧
  (∀ fd e env, Approx (evalE P n fd e env) (evalE P (n + k) fd e env)) ∧
  (∀ fd pts es env, Approx (evalArgs P n fd pts es env) (evalArgs P (n + k) fd pts es env)) ∧
  (∀ fd a ty e env, Approx (initAt P n fd a ty e env) (initAt P (n + k) fd a ty e env)) ∧
  (∀ g vs env, Approx (callFn P n g vs env) (callFn P (n + k) g vs env)) ∧
  (∀ fd focus c env, Approx (loop P n fd focus c env) (loop P (n + k) fd focus c env)) ∧
  (∀ fd focus c env, Approx (step P n fd focus c env) (step P (n + k) fd focus c env))

private theorem evalL_succ {P : Prog} {n k : Nat} (ih : Mono P n k) :
    ∀ fd e env, Approx (evalL P (n + 1) fd e env) (evalL P (n + 1 + k) fd e env) := by
  obtain ⟨hv, hag, hd, he, ha, hi, hc, hl, hs⟩ := ih
  intro fd e env
  cases h : e.node <;> simp only [Nat.succ_add, evalL, h]
  all_goals fuel_mono

private theorem evalA_succ {P : Prog} {n k : Nat} (ih : Mono P n k) :
    ∀ fd e env, Approx (evalA P (n + 1) fd e env) (evalA P (n + 1 + k) fd e env) := by
  obtain ⟨hv, hag, hd, he, ha, hi, hc, hl, hs⟩ := ih
  intro fd e env
  cases h : e.node <;> simp only [Nat.succ_add, evalA, h]
  all_goals fuel_mono

private theorem evalD_succ {P : Prog} {n k : Nat} (ih : Mono P n k) :
    ∀ fd e env, Approx (evalD P (n + 1) fd e env) (evalD P (n + 1 + k) fd e env) := by
  obtain ⟨hv, hag, hd, he, ha, hi, hc, hl, hs⟩ := ih
  intro fd e env
  simp only [Nat.succ_add, evalD]
  fuel_mono

-- `evalE` is the largest interpreter function; unfolding and splitting it needs more.
set_option maxHeartbeats 2000000 in
private theorem evalE_succ {P : Prog} {n k : Nat} (ih : Mono P n k) :
    ∀ fd e env, Approx (evalE P (n + 1) fd e env) (evalE P (n + 1 + k) fd e env) := by
  obtain ⟨hv, hag, hd, he, ha, hi, hc, hl, hs⟩ := ih
  intro fd e env
  cases h : e.node <;> simp only [Nat.succ_add, evalE, h]
  all_goals fuel_mono

private theorem evalArgs_succ {P : Prog} {n k : Nat} (ih : Mono P n k) :
    ∀ fd pts es env, Approx (evalArgs P (n + 1) fd pts es env) (evalArgs P (n + 1 + k) fd pts es env) := by
  obtain ⟨hv, hag, hd, he, ha, hi, hc, hl, hs⟩ := ih
  intro fd pts es env
  cases es <;> simp only [Nat.succ_add, evalArgs]
  all_goals fuel_mono

private theorem initAt_succ {P : Prog} {n k : Nat} (ih : Mono P n k) :
    ∀ fd a ty e env, Approx (initAt P (n + 1) fd a ty e env) (initAt P (n + 1 + k) fd a ty e env) := by
  obtain ⟨hv, hag, hd, he, ha, hi, hc, hl, hs⟩ := ih
  intro fd a ty e env
  simp only [Nat.succ_add, initAt]
  fuel_mono

private theorem callFn_succ {P : Prog} {n k : Nat} (ih : Mono P n k) :
    ∀ g vs env, Approx (callFn P (n + 1) g vs env) (callFn P (n + 1 + k) g vs env) := by
  obtain ⟨hv, hag, hd, he, ha, hi, hc, hl, hs⟩ := ih
  intro g vs env
  simp only [Nat.succ_add, callFn]
  fuel_mono

private theorem loop_succ {P : Prog} {n k : Nat} (ih : Mono P n k) :
    ∀ fd focus c env, Approx (loop P (n + 1) fd focus c env) (loop P (n + 1 + k) fd focus c env) := by
  obtain ⟨hv, hag, hd, he, ha, hi, hc, hl, hs⟩ := ih
  intro fd focus c env
  simp only [Nat.succ_add, loop]
  have h := hs fd focus c env
  cases hstep : step P n fd focus c env with
  | error e =>
    by_cases hno : e = .outOfFuel
    · subst e
      exact approx_bottom _
    · have eq := h (by simp [hstep, hno])
      simp only [eq, hstep]
      exact approx_refl _
  | ok x =>
    have eq := h (by simp [hstep])
    simp only [eq, hstep]
    rcases x with ⟨next, env'⟩
    cases next with
    | running focus c => exact hl fd focus c env'
    | returned v => exact approx_refl _

private theorem step_succ {P : Prog} {n k : Nat} (ih : Mono P n k) :
    ∀ fd focus c env, Approx (step P (n + 1) fd focus c env) (step P (n + 1 + k) fd focus c env) := by
  obtain ⟨hv, hag, hd, he, ha, hi, hc, hl, hs⟩ := ih
  intro fd focus c env
  cases focus <;> simp only [Nat.succ_add, step]
  all_goals fuel_mono

private theorem mutual_mono (P : Prog) (n k : Nat) : Mono P n k := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> exact approx_bottom _
  | succ n ih =>
    exact ⟨evalL_succ ih, evalA_succ ih, evalD_succ ih, evalE_succ ih, evalArgs_succ ih, initAt_succ ih, callFn_succ ih, loop_succ ih, step_succ ih⟩

/-- Expression evaluation preserves every result other than exhaustion. -/
theorem evalE_mono (P : Prog) (n k : Nat) (fd : FunDef) (e : TypedExpression) (env : Env) :
    Approx (evalE P n fd e env) (evalE P (n + k) fd e env) :=
  (mutual_mono P n k).2.2.2.1 fd e env

/-- Statement execution preserves every result other than exhaustion. -/
theorem loop_mono (P : Prog) (n k : Nat) (fd : FunDef)
    (focus : Option TypedStatement) (c : Kont) (env : Env) :
    Approx (loop P n fd focus c env) (loop P (n + k) fd focus c env) :=
  (mutual_mono P n k).2.2.2.2.2.2.2.1 fd focus c env

private theorem initMemory_mono (P : Prog) (n k : Nat) :
    Approx (initMemory P n) (initMemory P (n + k)) := by
  simp only [initMemory]
  have hi := (mutual_mono P n k).2.2.2.2.2.1
  fuel_mono

private def finish : Except Stop (Val × Env) → Result
  | .ok (v, env) => .done ⟨env.out.toList, C0.toStatus v.int⟩
  | .error (.exit c out) => .done ⟨out.toList, C0.toStatus c⟩
  | .error (.abort out) => .done ⟨out.toList, .signal 6⟩
  | .error (.undefined why) => .undefined why
  | .error .outOfFuel => .outOfFuel
  | .error (.unsupported why) => .unsupported why

private theorem finish_mono {a b : Except Stop (Val × Env)} (h : Approx a b)
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
  apply approx_bind (initMemory_mono (prepare p) n k)
  intro env
  have hc := (mutual_mono (prepare p) (n + 1) k).2.2.2.2.2.2.1
  simp only [Nat.add_right_comm n k 1]
  fuel_mono

/-- Two non-exhausted runs agree by extending both to the sum of their fuel bounds. -/
theorem run_agree {n m : Nat} {p : TypedProgram} {r s : Result}
    (hr : run n p = r) (hs : run m p = s)
    (hn : r ≠ .outOfFuel) (hm : s ≠ .outOfFuel) : r = s :=
  agree (run := (run · p)) (fun n k r => run_mono n k p r) hr hs hn hm

/-- C3 has at most one observation, unless it encounters undefined behaviour. -/
theorem beh_subsingleton_or_univ (p : TypedProgram) :
    (beh p).Subsingleton ∨ beh p = Set.univ :=
  subsingleton_or_univ (run := (run · p)) (fun n k r => run_mono n k p r)

end Silmaril.Compile.C.Sem.C3

module

public import Silmaril.Wasm.FX.Asyncify.Selective.Defs
public import Mathlib.Data.List.Forall2

/-!
# Selective instrumentation: the relation between optimized and instrumented runs

The optimized machine `tstep (optP S Q)` is related to the instrumented `tstep Q` by:

* `FR S b y x`: frames with equal operands, `y`'s code the optimization of `x`'s, with `skip`
  flag `b` (`b = true`: `x` waits on a call of a function in `S`, and its leading check is
  missing in `y`);
* `Stk S A ys xs`: stacks of related frames below a frame whose code is safe exactly when `A`
  holds, where a flagged frame requires every frame above it to run safe code (`A`);
* `SR S y x`: pointwise related heaps (unflagged frames), equal modes, unflagged buffers, and in
  normal mode a top frame with flag `false` over a `Stk`; while unwinding or rewinding, every
  frame is unflagged.

The lemmas: the equations of `opt`, and the facts on `Stk` used by the simulation; the soundness
of `analyze` (`analyze_safe`).

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Selective

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify.Selective

variable {V : Type} (S : Nat → Bool)

/-- Related frames, with a skip flag. -/
def FR (b : Bool) (y x : TFrame V) : Prop := y.ops = x.ops ∧ y.code = opt S b x.code

/-- Related stacks under a frame whose code is safe when `A` holds. -/
inductive Stk : Prop → List (TFrame V) → List (TFrame V) → Prop where
  | nil (A : Prop) : Stk A [] []
  | cons {A : Prop} {b : Bool} {y x : TFrame V} {ys xs : List (TFrame V)} (hfr : FR S b y x)
      (hb : b = true → A) (tl : Stk (A ∧ SafeCode S x.code) ys xs) : Stk A (y :: ys) (x :: xs)

/-- The modes, with unflagged buffers. -/
def RMode : Mode V → Mode V → Prop
  | .normal, .normal => True
  | .unwind t p buf, .unwind t' p' buf' => t = t' ∧ p = p' ∧ List.Forall₂ (FR S false) buf buf'
  | .rewind pend args, .rewind pend' args' =>
    args = args' ∧ List.Forall₂ (FR S false) pend pend'
  | _, _ => False

/-- The stacks, by mode. -/
def RStack : Mode V → List (TFrame V) → List (TFrame V) → Prop
  | .normal, [], [] => True
  | .normal, y :: ys, x :: xs => FR S false y x ∧ Stk S (SafeCode S x.code) ys xs
  | .normal, _, _ => False
  | _, ys, xs => List.Forall₂ (FR S false) ys xs

/-- **Related configurations**: optimized `y`, instrumented `x`. -/
def SR (y x : TCfg V) : Prop :=
  List.Forall₂ (Option.Rel (List.Forall₂ (FR S false))) y.heap x.heap ∧
    RMode S y.mode x.mode ∧ RStack S y.mode y.stack x.stack

variable {S}

/-! ## `opt` -/

theorem opt_false_cons (i : TIns V) (c : List (TIns V)) :
    opt S false (i :: c) = i :: opt S (after S i) c := by
  simp only [opt, Bool.false_and, Bool.false_eq_true, ite_false]

theorem opt_true_chk (c : List (TIns V)) : opt S true (.chk :: c) = opt S false c := by
  simp only [opt, isChk, Bool.and_self, ite_true]

theorem opt_true_of_not_chk {i : TIns V} (h : isChk i = false) (c : List (TIns V)) :
    opt S true (i :: c) = opt S false (i :: c) := by
  simp only [opt, h, Bool.and_false, Bool.false_eq_true, ite_false]

/-- A flagged code drops a leading check, or is optimized as an unflagged one. -/
theorem opt_true_cases (c : List (TIns V)) :
    (∃ d, c = .chk :: d) ∨ opt S true c = opt S false c := by
  cases c with
  | nil => exact .inr rfl
  | cons i d =>
    cases i
    case chk => exact .inl ⟨d, rfl⟩
    all_goals exact .inr (opt_true_of_not_chk rfl d)

/-! ## Safe code -/

theorem safeCode_nil : SafeCode S ([] : List (TIns V)) := fun _ h => by cases h

theorem safeCode_cons {i : TIns V} {c : List (TIns V)} (hi : safeI S i = true)
    (hc : SafeCode S c) : SafeCode S (i :: c) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj'
  · exact hi
  · exact hc j hj'

theorem safeCode_tail {i : TIns V} {c : List (TIns V)} (h : SafeCode S (i :: c)) :
    SafeCode S c := fun j hj => h j (List.mem_cons_of_mem i hj)

theorem safeCode_head {i : TIns V} {c : List (TIns V)} (h : SafeCode S (i :: c)) :
    safeI S i = true := h i List.mem_cons_self

/-! ## Stacks -/

/-- Unflagged stacks are `Stk` under any frame. -/
theorem stk_of_forall₂ {ys xs : List (TFrame V)} (h : List.Forall₂ (FR S false) ys xs)
    (A : Prop) : Stk S A ys xs := by
  induction h generalizing A with
  | nil => exact .nil A
  | cons hfr _ ih => exact .cons hfr (fun hb => by cases hb) (ih _)

/-- Below a frame that is not safe, no frame is flagged. -/
theorem forall₂_of_stk {A : Prop} {ys xs : List (TFrame V)} (h : Stk S A ys xs) (hA : ¬A) :
    List.Forall₂ (FR S false) ys xs := by
  induction h with
  | nil => exact .nil
  | @cons A b y x ys xs hfr hb tl ih =>
    have hb' : b = false := by
      cases b
      · rfl
      · exact absurd (hb rfl) hA
    have hfr' : FR S false y x := hb' ▸ hfr
    exact .cons hfr' (ih fun h' => hA h'.1)

/-- A weaker requirement keeps a `Stk`. -/
theorem stk_mono {A B : Prop} {ys xs : List (TFrame V)} (h : Stk S A ys xs) (hAB : A → B) :
    Stk S B ys xs := by
  induction h generalizing B with
  | nil => exact .nil B
  | cons hfr hb tl ih =>
    exact .cons hfr (fun h' => hAB (hb h')) (ih fun h' => ⟨hAB h'.1, h'.2⟩)

/-- **A step of the top frame**: the stack below a frame running `i :: c` is a stack below one
running `c` and above one running code that is safe when `i` is (`B`). -/
theorem stk_step {i : TIns V} {c : List (TIns V)} {ys xs : List (TFrame V)}
    (h : Stk S (SafeCode S (i :: c)) ys xs) {B : Prop} (hB : safeI S i = true → B) :
    Stk S (B ∧ SafeCode S c) ys xs := by
  cases hi : safeI S i with
  | true => exact stk_mono h fun h' => ⟨hB hi, safeCode_tail h'⟩
  | false =>
    have hn : ¬SafeCode S (i :: c) := fun h' => by rw [safeCode_head h'] at hi; cases hi
    exact stk_of_forall₂ (forall₂_of_stk h hn) _

/-! ## The analysis -/

theorem okF_spec {Q : Prog (TIns V)} {T : Nat → Bool} {f : Nat} (h : okF Q T f = true) :
    ∃ np body, Q f = some (np, body) ∧ SafeCode T body := by
  unfold okF at h
  split at h
  · rename_i np body hq
    exact ⟨np, body, hq, fun i hi => List.all_eq_true.mp h i hi⟩
  · cases h

theorem check_spec {Q : Prog (TIns V)} {n : Nat} {T : Nat → Bool} (h : check Q n T = true)
    {f : Nat} (hf : f < n) (hT : T f = true) : okF Q T f = true := by
  have hall := List.all_eq_true.mp h f (List.mem_range.mpr hf)
  simpa only [hT, Bool.not_true, Bool.false_or] using hall

theorem candidate_lt {Q : Prog (TIns V)} {n f : Nat} (h : candidate Q n f = true) : f < n := by
  unfold candidate at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

/-- **The analysis is sound**: its result is a certificate. -/
theorem analyze_safe (Q : Prog (TIns V)) (n : Nat) : SafeProg (analyze Q n) Q := by
  intro f hf
  unfold analyze at hf ⊢
  split
  · rename_i hc
    have hf' : candidate Q n f = true := by simpa only [hc, ite_true] using hf
    exact okF_spec (check_spec hc (candidate_lt hf') hf')
  · rename_i hc
    have hf' : False := by simp only [hc, ite_false, Bool.false_eq_true] at hf
    exact hf'.elim

end Silmaril.Proofs.Wasm.FX.Asyncify.Selective

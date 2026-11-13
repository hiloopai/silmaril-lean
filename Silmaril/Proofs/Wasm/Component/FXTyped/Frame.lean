module

public import Silmaril.Wasm.Models.FXV.Thms
public import Silmaril.Wasm.SingleThreaded.NoRedex

/-!
# Inversion of `StepFX'` at an outermost frame

The results returned by a call of an FX function leave the frame that the FX rule `invoke`
pushes. This module inverts `StepFX'` at code that is a single frame, and at empty code:

* `stepFX'_code_ne_nil`: no step starts from empty code;
* `FrameOut n c`: `c` is a frame of arity `n`, FX values of length `n`, a trap, or a thrown
  exception;
* **`stepFX'_frame`**: every `StepFX'` step from `[frame n fi es]` reaches `FrameOut n`
  (`ctxFrame` keeps the frame, `frameVals` and `returnFrame` give `n` values, `trapFrame` and
  `throwFrame` the trap or the exception; no other rule applies to a single frame).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (AdminFX ContFX ConfigFX FuncFX InstrFX cvals cthrowing)
open Silmaril.Wasm.Models.FXV (StepFX' FVal fvals CtxV)
open Silmaril.Proofs.Wasm.Models.FXV (fvals_cons fvals_append fvals_nil)
open Silmaril.Proofs.Wasm.Models.FX (map_core_inj)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- The head of FX values is not a frame. -/
theorem fval_ne_frame (v : FVal) (n : Nat) (fi : Frame) (es : List AdminFX) :
    v.toAdmin ≠ .frame n fi es := by
  cases v <;> simp [FVal.toAdmin]

/-- A Core step does not start from empty code. -/
theorem core_step_ne_nil {s s' : Store H} {f f' : Frame} {cs' : List Admin} {host' : HostSemantics H}
    (h : Step P host' ⟨s, f, []⟩ ⟨s', f', cs'⟩) : False :=
  Silmaril.Wasm.SingleThreaded.Step.not_quiet h
    (by simpa using Silmaril.Wasm.SingleThreaded.quiet_vals ([] : List Val))

/-- **No `StepFX'` step starts from empty code.** -/
theorem stepFX'_code_ne_nil {x y : ConfigFX H} (h : StepFX' P host fx x y) : x.code ≠ [] := by
  induction h with
  | core h =>
    intro e
    have e' : _ = [] := List.map_eq_nil_iff.mp e
    exact core_step_ne_nil (e' ▸ h)
  | seq _ _ ih =>
    intro e
    have e' := List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp e).1
    exact ih e'.2
  | _ => simp [cvals, cthrowing, throwing]

/-- What a step from an outermost frame of arity `n` reaches. -/
def FrameOut (n : Nat) (c : List AdminFX) : Prop :=
  (∃ fi es, c = [.frame n fi es]) ∨ (∃ vs : List FVal, c = fvals vs ∧ vs.length = n) ∨
    c = [.core .trap] ∨ ∃ a, c = cthrowing a

/-- FX values followed by `a` form a single frame only when there are no values and `a` is
that frame. -/
theorem fvals_cons_frame {vs : List FVal} {a : AdminFX} {L : List AdminFX} {n : Nat} {fi : Frame}
    {es : List AdminFX} (e : fvals vs ++ a :: L = [.frame n fi es]) : a = .frame n fi es := by
  cases vs with
  | nil =>
    simp only [fvals_nil, List.nil_append, List.cons.injEq] at e
    exact e.1
  | cons v vs =>
    simp only [fvals_cons, List.cons_append, List.cons.injEq] at e
    exact (fval_ne_frame v n fi es e.1).elim

/-- The `seq` case at a single frame is impossible. -/
theorem seq_frame_absurd {vs : List FVal} {es rest : List AdminFX} {n : Nat} {fi : Frame}
    {es₀ : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) (hes : es ≠ [])
    (e : fvals vs ++ es ++ rest = [.frame n fi es₀]) : False := by
  cases vs with
  | cons v vs =>
    simp only [fvals_cons, List.cons_append, List.cons.injEq] at e
    exact fval_ne_frame v n fi es₀ e.1
  | nil =>
    simp only [fvals_nil, List.nil_append, List.append_eq_singleton_iff] at e
    rcases e with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hes h1
    · exact (hne.resolve_left (fun h => h rfl)) h2

/-- A single frame determines its arity. -/
theorem frame_arity {n n' : Nat} {fi fi' : Frame} {es es' : List AdminFX}
    (e : [AdminFX.frame n' fi' es'] = [.frame n fi es]) : n' = n := by
  simp only [List.cons.injEq, AdminFX.frame.injEq, and_true] at e
  exact e.1

/-- The non-frame rules do not apply to a single frame. -/
local macro "frame_absurd" e:ident : tactic => `(tactic|
  first
    | (simp [cthrowing, throwing] at $e:ident; done)
    | (simp only [List.append_assoc, List.cons_append, List.nil_append] at $e:ident
       exact absurd (fvals_cons_frame $e) (by simp))
    | (rw [← Silmaril.Proofs.Wasm.Models.FXV.fvals_liftV] at $e:ident
       simp only [List.append_assoc, List.cons_append, List.nil_append] at $e:ident
       exact absurd (fvals_cons_frame $e) (by simp)))

set_option linter.unusedSimpArgs false in
/-- **Inversion at an outermost frame**: a step from `[frame n fi es]` reaches `FrameOut n`. -/
theorem stepFX'_frame {x y : ConfigFX H} (h : StepFX' P host fx x y) :
    ∀ {n : Nat} {fi : Frame} {es : List AdminFX}, x.code = [.frame n fi es] → FrameOut n y.code := by
  induction h with
  | core h => intro n fi es e; simp at e
  | seq h hne _ => exact fun e => (seq_frame_absurd hne (stepFX'_code_ne_nil h) e).elim
  | ctxFrame _ _ => exact fun e => frame_arity e ▸ Or.inl ⟨_, _, rfl⟩
  | frameVals hn => exact fun e => frame_arity e ▸ Or.inr (Or.inl ⟨_, rfl, hn⟩)
  | returnFrame hn => exact fun e => frame_arity e ▸ Or.inr (Or.inl ⟨_, rfl, hn⟩)
  | trapFrame => exact fun _ => Or.inr (Or.inr (Or.inl rfl))
  | throwFrame => exact fun _ => Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
  | _ => intro n fi es e; frame_absurd e

/-! ## Quiet code -/

/-- An FX value instruction (a Core value or a continuation reference). -/
def isFV : AdminFX → Bool
  | .core a => a.val?.isSome
  | .contRef _ => true
  | _ => false

/-- **Quiet FX code**: FX values, a trap, a lone `throw_ref`, or a thrown exception. -/
def QuietFX (c : List AdminFX) : Prop :=
  c.all isFV = true ∨ c = [.core .trap] ∨ c = [.core (.plain .throwRef)] ∨ ∃ a, c = cthrowing a

@[simp] theorem all_isFV_fvals (vs : List FVal) : (fvals vs).all isFV = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases v <;> simp_all [fvals_cons, FVal.toAdmin, isFV]

theorem vals_of_all_isFV : ∀ {cs : List Admin}, (cs.map AdminFX.core).all isFV = true →
    ∃ ws, cs = vals ws
  | [], _ => ⟨[], rfl⟩
  | c :: cs, h => by
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ws, rfl⟩ := vals_of_all_isFV h.2
    have h1 : c.val?.isSome = true := h.1
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h1
    refine ⟨v :: ws, ?_⟩
    simp only [vals, List.map_cons, List.cons.injEq, and_true]
    exact Silmaril.Wasm.Execution.Core.Admin.eq_of_val? hv

/-- Quiet Core code lifted to FX code is quiet for Core. -/
theorem quiet_of_quietFX {cs : List Admin} (h : QuietFX (cs.map AdminFX.core)) :
    Silmaril.Wasm.SingleThreaded.Quiet cs := by
  rcases h with h | h | h | ⟨a, h⟩
  · obtain ⟨ws, rfl⟩ := vals_of_all_isFV h
    exact Silmaril.Wasm.SingleThreaded.quiet_vals ws
  · rw [show cs = [.trap] from map_core_inj (l' := [.trap]) h]
    exact Silmaril.Wasm.SingleThreaded.quiet_trap
  · rw [show cs = [.plain .throwRef] from map_core_inj (l' := [.plain .throwRef]) h]
    exact Or.inr (Or.inr (Or.inl rfl))
  · rw [show cs = throwing a from map_core_inj h]
    exact Silmaril.Wasm.SingleThreaded.quiet_throwing a

theorem head_isFV (v : FVal) : isFV v.toAdmin = true := by
  cases v <;> simp [FVal.toAdmin, isFV]

/-- FX values followed by code equal to a list whose head is not an FX value: no values. -/
theorem fvals_nil_of_head {vs : List FVal} {L : List AdminFX} {x : AdminFX} {M : List AdminFX}
    (hx : isFV x = false) (h : fvals vs ++ L = x :: M) : vs = [] ∧ L = x :: M := by
  cases vs with
  | nil => exact ⟨rfl, by simpa using h⟩
  | cons v vs =>
    simp only [fvals_cons, List.cons_append, List.cons.injEq] at h
    have := head_isFV v
    rw [h.1, hx] at this
    cases this

/-- A one-element list from a non-empty middle part and a non-empty side part is impossible. -/
theorem single_absurd {vs : List FVal} {es rest : List AdminFX} {x : AdminFX}
    (hx : isFV x = false) (hne : vs ≠ [] ∨ rest ≠ []) (hes : es ≠ [])
    (h : fvals vs ++ es ++ rest = [x]) : False := by
  rw [List.append_assoc] at h
  obtain ⟨rfl, h'⟩ := fvals_nil_of_head hx h
  rcases List.append_eq_singleton_iff.mp h' with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact hes h1
  · exact (hne.resolve_left (fun h => h rfl)) h2

/-- The `seq` case at a thrown exception with no FX values before it. -/
theorem quiet_seq_throw_nil {es rest : List AdminFX} {x₁ x₂ : AdminFX} (hx : isFV x₁ = true)
    (hr : rest ≠ []) (hes : es ≠ []) (h : es ++ rest = [x₁, x₂]) : es.all isFV = true := by
  rcases List.append_eq_cons_iff.mp h with ⟨rfl, -⟩ | ⟨es', rfl, h'⟩
  · exact (hes rfl).elim
  · rcases List.append_eq_singleton_iff.mp h'.symm with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · simpa using hx
    · exact (hr rfl).elim

/-- The `seq` case at a thrown exception with FX values before it. -/
theorem quiet_seq_throw_cons {v : FVal} {vs : List FVal} {es rest : List AdminFX}
    {x₁ : AdminFX} (hes : es ≠ []) (h : fvals (v :: vs) ++ (es ++ rest) = [x₁, .core (.plain .throwRef)]) :
    es = [.core (.plain .throwRef)] := by
  have h₁ : fvals vs ++ (es ++ rest) = [.core (.plain .throwRef)] := by
    simp only [fvals_cons, List.cons_append, List.cons.injEq] at h
    exact h.2
  obtain ⟨-, h'⟩ := fvals_nil_of_head (x := .core (.plain .throwRef)) (by rfl) h₁
  rcases List.append_eq_singleton_iff.mp h' with ⟨h₂, -⟩ | ⟨h₂, -⟩
  · exact (hes h₂).elim
  · exact h₂

/-- The `seq` case: a step of `es` inside quiet code is a step of quiet code. -/
theorem quiet_seq {vs : List FVal} {es rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ [])
    (hes : es ≠ []) (h : QuietFX (fvals vs ++ es ++ rest)) : QuietFX es := by
  rcases h with h | h | h | ⟨a, h⟩
  · have h' : (es.all isFV) = true := by
      simp only [List.all_append, Bool.and_eq_true] at h
      exact h.1.2
    exact Or.inl h'
  · exact (single_absurd (by rfl) hne hes h).elim
  · exact (single_absurd (by rfl) hne hes h).elim
  · have h' : fvals vs ++ (es ++ rest) = [.core (.ref (.exn a)), .core (.plain .throwRef)] := by
      simpa [cthrowing, throwing] using h
    cases vs with
    | nil => exact Or.inl (quiet_seq_throw_nil (x₁ := .core (.ref (.exn a)))
        (by simp [isFV, Admin.val?]) (hne.resolve_left (fun h => h rfl)) hes (by simpa using h'))
    | cons v vs => exact Or.inr (Or.inr (Or.inl (quiet_seq_throw_cons hes h')))

/-- A middle part with values or code on a side is longer than the middle part. -/
theorem length_lt_side {vs : List FVal} {rest : List AdminFX} (L : List AdminFX)
    (hne : vs ≠ [] ∨ rest ≠ []) : L.length < (fvals vs ++ L ++ rest).length := by
  have h₁ : 0 < vs.length ∨ 0 < rest.length :=
    hne.imp List.length_pos_iff.mpr List.length_pos_iff.mpr
  have h₂ : (fvals vs ++ L ++ rest).length = vs.length + L.length + rest.length := by
    simp [fvals, Silmaril.Wasm.Models.FXV.fvals, Nat.add_assoc]
  omega

/-- The left-hand side of `trapSeq` is not quiet. -/
theorem not_quiet_trapSeq {vs : List FVal} {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) :
    ¬ QuietFX (fvals vs ++ [.core .trap] ++ rest) := by
  have hl := length_lt_side [.core .trap] hne
  rintro (hq | hq | hq | ⟨a, hq⟩)
  · simp [isFV, Admin.val?] at hq
  · rw [hq] at hl; simp at hl
  · rw [hq] at hl; simp at hl
  · have hm : AdminFX.core .trap ∈ cthrowing a := by rw [← hq]; simp
    simp [cthrowing, throwing] at hm

/-- The left-hand side of `throwSeq` is not quiet. -/
theorem not_quiet_throwSeq {vs : List FVal} {b : Nat} {rest : List AdminFX}
    (hne : vs ≠ [] ∨ rest ≠ []) : ¬ QuietFX (fvals vs ++ cthrowing b ++ rest) := by
  have hl := length_lt_side (cthrowing b) hne
  rintro (hq | hq | hq | ⟨a, hq⟩)
  · simp [isFV, Admin.val?, cthrowing, throwing] at hq
  · rw [hq] at hl; simp [cthrowing, throwing] at hl
  · rw [hq] at hl; simp [cthrowing, throwing] at hl
  · rw [hq] at hl; simp [cthrowing, throwing] at hl

/-- The left-hand side of `invoke` is not quiet. -/
theorem not_quiet_invoke {vs : List Val} {a : Nat} {c : Admin} (hc : c.IsCallRef) :
    ¬ QuietFX (cvals vs ++ [.core (.ref (.func a)), .core c]) := by
  have hcv : c.val? = none := Silmaril.Wasm.Execution.Core.Admin.val?_of_isCallRef hc
  rintro (hq | hq | hq | ⟨b, hq⟩)
  · simp [isFV, hcv] at hq
  · have hl := congrArg List.length hq; simp [cvals, vals] at hl
  · have hl := congrArg List.length hq; simp [cvals, vals] at hl
  · have hl : some (AdminFX.core c) = some (.core (.plain .throwRef)) := by
      simpa [cthrowing, throwing] using congrArg List.getLast? hq
    have hc' : c = .plain .throwRef := by simpa using hl
    rw [hc'] at hc
    exact hc

/-- The other rules do not apply to quiet code. -/
local macro "quiet_absurd" : tactic => `(tactic|
  (intro hq
   dsimp only at hq
   rcases hq with hq | hq | hq | ⟨a, hq⟩
   all_goals first
     | (simp [isFV, cvals, cthrowing, throwing, vals, Admin.val?] at hq; done)
     | (have hl := congrArg List.getLast? hq
        simp [cvals, cthrowing, throwing, vals] at hl)))

set_option linter.unusedSimpArgs false in
/-- **Quiet FX code takes no `StepFX'` step.** -/
theorem stepFX'_not_quiet {x y : ConfigFX H} (h : StepFX' P host fx x y) : ¬ QuietFX x.code := by
  induction h with
  | core h => exact fun hq => Silmaril.Wasm.SingleThreaded.Step.not_quiet h (quiet_of_quietFX hq)
  | seq h hne ih => exact fun hq => ih (quiet_seq hne (stepFX'_code_ne_nil h) hq)
  | trapSeq hne => exact not_quiet_trapSeq hne
  | throwSeq hne => exact not_quiet_throwSeq hne
  | invoke hc => exact not_quiet_invoke hc
  | _ => quiet_absurd

end Silmaril.Proofs.Wasm.Component.FXTyped

module

public import Silmaril.Wasm.FX.Logic.Defs

/-!
# Runs of `StepFX'` in evaluation contexts

Runs lift through the evaluation contexts of `StepFX'` (values before and code after, labels,
function frames, handler frames), and Core runs lift to FX runs. These are the structural
facts the rules of `Silmaril.Wasm.FX.Logic` are proved from.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-! ## FX values -/

theorem fvals_app (xs ys : List FVal) : fvals (xs ++ ys) = fvals xs ++ fvals ys :=
  List.map_append

theorem fvals_lift (vs : List Val) : fvals (liftV vs) = (vals vs).map .core := by
  simp only [fvals, liftV, vals, List.map_map]
  rfl

theorem cvals_eq_fvals (vs : List Val) : cvals vs = fvals (liftV vs) := (fvals_lift vs).symm

theorem fvals_cont (vs : List FVal) (k : Nat) :
    fvals (vs ++ [.cont k]) = fvals vs ++ [.contRef k] := by
  simp only [fvals_app]
  rfl

theorem map_core_expression (is : List Instr) :
    (expression is).map AdminFX.core = is.map fun i => AdminFX.core (.plain i) := by
  simp only [expression, List.map_map]
  rfl

/-! ## Runs in contexts -/

/-- A run lifts below values and before code (`ctxt-instrs`). -/
theorem steps_seq {us : List FVal} {rest : List AdminFX} (hne : us ≠ [] ∨ rest ≠ [])
    {c d : ConfigFX H} (h : StepsFX' P host fx c d) :
    StepsFX' P host fx ⟨c.store, c.conts, c.frame, fvals us ++ c.code ++ rest⟩
      ⟨d.store, d.conts, d.frame, fvals us ++ d.code ++ rest⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail (StepFX'.seq st hne)

/-- A run lifts into a label. -/
theorem steps_label {n : Nat} {k : List InstrFX} {c d : ConfigFX H}
    (h : StepsFX' P host fx c d) :
    StepsFX' P host fx ⟨c.store, c.conts, c.frame, [.label n k c.code]⟩
      ⟨d.store, d.conts, d.frame, [.label n k d.code]⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail (StepFX'.ctxLabel st)

/-- A run lifts into a function frame; the caller's frame `f` stays. -/
theorem steps_frame {n : Nat} (f : Frame) {c d : ConfigFX H} (h : StepsFX' P host fx c d) :
    StepsFX' P host fx ⟨c.store, c.conts, f, [.frame n c.frame c.code]⟩
      ⟨d.store, d.conts, f, [.frame n d.frame d.code]⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail (StepFX'.ctxFrame st)

/-- A run lifts into a handler frame. -/
theorem steps_handler {hs : List HClause} {c d : ConfigFX H} (h : StepsFX' P host fx c d) :
    StepsFX' P host fx ⟨c.store, c.conts, c.frame, [.handler hs c.code]⟩
      ⟨d.store, d.conts, d.frame, [.handler hs d.code]⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail (StepFX'.ctxHandler st)

/-- A Core run (with FX function codes refused) is an FX run, with any continuation store. -/
theorem steps_core (K : Conts) {c d : Config H} (h : Steps P (blockFX host fx) c d) :
    StepsFX' P host fx ⟨c.store, K, c.frame, c.code.map .core⟩
      ⟨d.store, K, d.frame, d.code.map .core⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail (StepFX'.core st)

/-- One step at the head of `us; c; rest`. -/
theorem step_ctx {us : List FVal} {rest : List AdminFX} {c d : ConfigFX H}
    (h : StepFX' P host fx c d) :
    StepsFX' P host fx ⟨c.store, c.conts, c.frame, fvals us ++ c.code ++ rest⟩
      ⟨d.store, d.conts, d.frame, fvals us ++ d.code ++ rest⟩ := by
  by_cases hne : us ≠ [] ∨ rest ≠ []
  · exact .single (StepFX'.seq h hne)
  · have hu : us = [] := by simp_all
    have hr : rest = [] := by simp_all
    have e₁ : fvals us ++ c.code ++ rest = c.code := by simp [hu, hr, fvals]
    have e₂ : fvals us ++ d.code ++ rest = d.code := by simp [hu, hr, fvals]
    rw [e₁, e₂]
    exact .single h

/-- A run at the head of `us; c; rest`. -/
theorem steps_ctx {us : List FVal} {rest : List AdminFX} {c d : ConfigFX H}
    (h : StepsFX' P host fx c d) :
    StepsFX' P host fx ⟨c.store, c.conts, c.frame, fvals us ++ c.code ++ rest⟩
      ⟨d.store, d.conts, d.frame, fvals us ++ d.code ++ rest⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact ih.trans (step_ctx st)

end Silmaril.Wasm.FX.Logic

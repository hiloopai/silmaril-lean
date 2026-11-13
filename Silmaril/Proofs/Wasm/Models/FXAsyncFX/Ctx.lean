module

public import Silmaril.Wasm.Models.FXAsyncFX.Defs

/-!
# Contexts of `StepFX'`: composition and lifting of steps

* `plug_comp`, `frameAt_comp`, `handles_comp`: composing contexts (`comp`) plugs, finds the
  frame at the hole and finds handlers piecewise;
* `step_seq`: a step under a value prefix and a code suffix (the `seq` rule, or nothing when both
  are empty);
* **`step_lift`**, `frun_lift`, `fplus_lift`: a step (run of `FStep`s) at the frame of the hole
  that keeps that frame lifts to the plugged code, keeping the outer frame;
* `ModM`: every frame of a context belongs to module `M`, so the frame at the hole does too
  (`frameAt_module`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX

variable {H : Type}

@[simp] theorem plug_comp (E E' : CtxV) (c : List AdminFX) :
    (comp E E').plug c = E.plug (E'.plug c) := by
  induction E with
  | hole => rfl
  | seq vs E rest ih => simp only [comp, CtxV.plug, ih]
  | label n k E ih => simp only [comp, CtxV.plug, ih]
  | frame n f E ih => simp only [comp, CtxV.plug, ih]
  | handler hs E ih => simp only [comp, CtxV.plug, ih]

@[simp] theorem frameAt_comp (E E' : CtxV) (f : Frame) :
    (comp E E').frameAt f = E'.frameAt (E.frameAt f) := by
  induction E generalizing f with
  | hole => rfl
  | seq vs E rest ih => exact ih f
  | label n k E ih => exact ih f
  | frame n fi E ih => exact ih fi
  | handler hs E ih => exact ih f

theorem handles_comp (ta : Nat) (E E' : CtxV) :
    (comp E E').Handles ta ↔ E.Handles ta ∨ E'.Handles ta := by
  induction E with
  | hole => simp only [comp, CtxV.Handles, false_or]
  | seq vs E rest ih => exact ih
  | label n k E ih => exact ih
  | frame n f E ih => exact ih
  | handler hs E ih => simp only [comp, CtxV.Handles, ih, or_assoc]

@[simp] theorem comp_hole (E : CtxV) : comp E .hole = E := by
  induction E with
  | hole => rfl
  | seq vs E rest ih => simp only [comp, ih]
  | label n k E ih => simp only [comp, ih]
  | frame n f E ih => simp only [comp, ih]
  | handler hs E ih => simp only [comp, ih]

theorem comp_assoc (E₁ E₂ E₃ : CtxV) : comp (comp E₁ E₂) E₃ = comp E₁ (comp E₂ E₃) := by
  induction E₁ with
  | hole => rfl
  | seq vs E rest ih => simp only [comp, ih]
  | label n k E ih => simp only [comp, ih]
  | frame n f E ih => simp only [comp, ih]
  | handler hs E ih => simp only [comp, ih]

theorem kindCtx_eq (k : Kind) (E : CtxV) : kindCtx k E = comp (kindCtx k .hole) E := by
  cases k <;> rfl

@[simp] theorem fvals_nil : fvals [] = [] := rfl

@[simp] theorem fvals_append (xs ys : List FVal) : fvals (xs ++ ys) = fvals xs ++ fvals ys :=
  List.map_append

theorem fvals_val (vs : List Val) : fvals (vs.map .val) = (vals vs).map .core := by
  simp only [fvals, vals, List.map_map]
  rfl

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- A step under a value prefix and a code suffix. -/
theorem step_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} (vs : List FVal)
    {es es' : List AdminFX} (rest : List AdminFX)
    (h : StepFX' P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    StepFX' P host fx ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  by_cases hv : vs = [] ∧ rest = []
  · obtain ⟨rfl, rfl⟩ := hv
    simpa only [fvals_nil, List.nil_append, List.append_nil] using h
  · exact .seq h (by
      rcases not_and_or.mp hv with h₁ | h₁
      · exact Or.inl h₁
      · exact Or.inr h₁)

/-- **A step at the frame of the hole lifts to the plugged code.** -/
theorem step_lift (E : CtxV) {s s' : Store H} {K K' : List (Option ContFX)} {f : Frame}
    {X X' : List AdminFX}
    (h : StepFX' P host fx ⟨s, K, E.frameAt f, X⟩ ⟨s', K', E.frameAt f, X'⟩) :
    StepFX' P host fx ⟨s, K, f, E.plug X⟩ ⟨s', K', f, E.plug X'⟩ := by
  induction E generalizing f with
  | hole => exact h
  | seq vs E rest ih => exact step_seq vs rest (ih h)
  | label n k E ih => exact .ctxLabel (ih h)
  | frame n fi E ih => exact .ctxFrame (ih (f := fi) h)
  | handler hs E ih => exact .ctxHandler (ih h)

/-- A step that keeps the store and the frame `F`, on continuation stores and code. -/
def FStep (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (fx : H → Option FuncFX)
    (s : Store H) (F : Frame) (a b : List (Option ContFX) × List AdminFX) : Prop :=
  StepFX' P host fx ⟨s, a.1, F, a.2⟩ ⟨s, b.1, F, b.2⟩

/-- A step at the frame of the hole lifts to the plugged code, at the outer frame. -/
theorem fstep_lift (E : CtxV) {s : Store H} {f : Frame}
    {a b : List (Option ContFX) × List AdminFX} (h : FStep P host fx s (E.frameAt f) a b) :
    FStep P host fx s f (a.1, E.plug a.2) (b.1, E.plug b.2) :=
  step_lift E h

/-- **Runs at the frame of the hole lift to the plugged code**, at the outer frame. -/
theorem frun_lift (E : CtxV) {s : Store H} {f : Frame}
    {a b : List (Option ContFX) × List AdminFX}
    (h : Relation.ReflTransGen (FStep P host fx s (E.frameAt f)) a b) :
    Relation.ReflTransGen (FStep P host fx s f) (a.1, E.plug a.2) (b.1, E.plug b.2) := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (step_lift E hbc)

/-- Positive runs lift too. -/
theorem fplus_lift (E : CtxV) {s : Store H} {f : Frame}
    {a b : List (Option ContFX) × List AdminFX}
    (h : Relation.TransGen (FStep P host fx s (E.frameAt f)) a b) :
    Relation.TransGen (FStep P host fx s f) (a.1, E.plug a.2) (b.1, E.plug b.2) := by
  induction h with
  | single hab => exact .single (step_lift E hab)
  | tail _ hbc ih => exact ih.tail (step_lift E hbc)

/-- `FStep` runs are `StepFX'` runs. -/
theorem frun_steps {s : Store H} {F : Frame} {a b : List (Option ContFX) × List AdminFX}
    (h : Relation.ReflTransGen (FStep P host fx s F) a b) :
    StepsFX' P host fx ⟨s, a.1, F, a.2⟩ ⟨s, b.1, F, b.2⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail hbc

/-- Positive `FStep` runs are positive `StepFX'` runs. -/
theorem fplus_plus {s : Store H} {F : Frame} {a b : List (Option ContFX) × List AdminFX}
    (h : Relation.TransGen (FStep P host fx s F) a b) :
    Relation.TransGen (StepFX' P host fx) ⟨s, a.1, F, a.2⟩ ⟨s, b.1, F, b.2⟩ := by
  induction h with
  | single hab => exact .single hab
  | tail _ hbc ih => exact ih.tail hbc

/-- A positive run built from a step and a run. -/
theorem plus_of_step_steps {a b c : ConfigFX H} (h₁ : StepFX' P host fx a b)
    (h₂ : StepsFX' P host fx b c) : Relation.TransGen (StepFX' P host fx) a c :=
  Relation.TransGen.head' h₁ h₂

/-- Every frame of a context belongs to `M`. -/
def ModM (M : ModuleInst) : CtxV → Prop
  | .hole => True
  | .seq _ E _ => ModM M E
  | .label _ _ E => ModM M E
  | .frame _ fi E => fi.module = M ∧ ModM M E
  | .handler _ E => ModM M E

theorem frameAt_module {M : ModuleInst} (E : CtxV) {f : Frame} (hE : ModM M E)
    (hf : f.module = M) : (E.frameAt f).module = M := by
  induction E generalizing f with
  | hole => exact hf
  | seq vs E rest ih => exact ih hE hf
  | label n k E ih => exact ih hE hf
  | frame n fi E ih => exact ih hE.2 hE.1
  | handler hs E ih => exact ih hE hf

theorem modM_comp {M : ModuleInst} (E E' : CtxV) :
    ModM M (comp E E') ↔ ModM M E ∧ ModM M E' := by
  induction E with
  | hole => simp only [comp, ModM, true_and]
  | seq vs E rest ih => exact ih
  | label n k E ih => exact ih
  | frame n f E ih => simp only [comp, ModM, ih, and_assoc]
  | handler hs E ih => exact ih

end Silmaril.Proofs.Wasm.Models.FXAsyncFX

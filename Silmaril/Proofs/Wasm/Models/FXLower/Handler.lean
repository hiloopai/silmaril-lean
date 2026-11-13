module

public import Silmaril.Wasm.Models.FXLower.Defs
public import Silmaril.Wasm.Models.FX.Thms

/-!
# A handler frame around Core code is transparent (Core behaviours are FX behaviours)

* `steps_handler`: a Core run lifts to an FX run under a handler frame, with any continuation
  store;
* `result_handler`: a handler frame around a result steps to the result;
* `diverges_handler`: Core divergence lifts under a handler frame;
* `behaviours_handler_sub`: every Core behaviour of `cs` is an FX behaviour of `cs` under a
  handler frame.

No hypothesis on the host or on the FX function table is needed: Core steps run with the host
`blockFX host fx` on both sides.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXLower
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- A Core configuration under a handler frame, with continuation store `K`. -/
def underH (K : List (Option ContFX)) (hs : List HClause) (c : Config H) : ConfigFX H :=
  ⟨c.store, K, c.frame, onHandler hs c.code⟩

/-- One Core step lifts under a handler frame. -/
theorem step_handler {K : List (Option ContFX)} {hs : List HClause} {c c' : Config H}
    (h : Step P (blockFX host fx) c c') :
    StepFX P host fx (underH K hs c) (underH K hs c') := by
  obtain ⟨s, f, cs⟩ := c
  obtain ⟨s', f', cs'⟩ := c'
  exact StepFX.ctxHandler (StepFX.core h)

/-- **A Core run lifts under a handler frame.** -/
theorem steps_handler {K : List (Option ContFX)} {hs : List HClause} {c c' : Config H}
    (h : Steps P (blockFX host fx) c c') :
    StepsFX P host fx (underH K hs c) (underH K hs c') := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (step_handler hstep)

/-- **A handler frame around a result steps to the result.** -/
theorem result_handler {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {hs : List HClause} (r : Result) :
    StepFX P host fx ⟨s, K, f, onHandler hs r.toAdmin⟩ ⟨s, K, f, r.toAdmin.map .core⟩ := by
  cases r with
  | values vs => exact StepFX.handlerVals (vs := vs)
  | throw a => exact StepFX.throwHandler (a := a)
  | trap => exact StepFX.trapHandler

/-- **Core divergence lifts under a handler frame.** -/
theorem diverges_handler {K : List (Option ContFX)} {hs : List HClause} {c : Config H}
    (h : Diverges P (blockFX host fx) c) :
    Silmaril.InfiniteTrace (StepFX P host fx) (underH K hs c) := by
  obtain ⟨T, h0, hT⟩ := h
  exact ⟨fun n => underH K hs (T n), by simp only [h0], fun n => step_handler (hT n)⟩

/-- **Every Core behaviour of `c` is an FX behaviour of `c` under a handler frame.** -/
theorem behaviours_handler_sub (K : List (Option ContFX)) (hs : List HClause) (c : Config H) :
    behavioursOf P (blockFX host fx) c ⊆ behavioursFX P host fx (underH K hs c) := by
  rintro b (⟨c', r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
  · refine Or.inl ⟨⟨c'.store, K, c'.frame, r.toAdmin.map .core⟩, r, ?_, rfl, rfl⟩
    have hlast : StepFX P host fx (underH K hs c')
        ⟨c'.store, K, c'.frame, r.toAdmin.map .core⟩ := by
      unfold underH
      rw [hcode]
      exact result_handler r
    exact (steps_handler hrun).tail hlast
  · exact Or.inr ⟨rfl, diverges_handler hdiv⟩

end Silmaril.Proofs.Wasm.Models.FXLower

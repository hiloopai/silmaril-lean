module

public import Silmaril.Wasm.Dataflow.Dce.Defs
public import Silmaril.Wasm.Dataflow.LocalDce.Thms
public import Silmaril.Wasm.Dataflow.DropElim.Thms
public import Silmaril.Wasm.Dataflow.Fused.Defs

/-!
# Two-pass liveness-based DCE for Wasm, against Core 3.0: theorems

For a fragment function body `e` (`fragSeq e`: code that runs inside one frame without
calls or exceptions; `Silmaril.Wasm.Dataflow.Fragment`), run under its outer label, at every
numerical profile `P` and host:

* `dce2_result`: if `e` reaches a result (values, a trap or an escaping exception) with
  store `s₁`, then `dce2 e` reaches the same result and store, from any frame that agrees
  with the original one on the live-in locals of `e` (`FrameRel (liveEntry e)`);
* `dce2_returning`: the same for a pending `return` with its values;
* `dce2_diverges`: if `e` diverges, so does `dce2 e`.

These are forward statements: they say nothing about runs of `e` that get stuck, and they
do not by themselves give the converse (a result of `dce2 e` is a result of `e`). The
converse also needs determinism of `Step` and that runs of `e` do not get stuck (for
example by type soundness of valid code); it is not stated here. In particular `dce2` may
turn a stuck run into a terminating one: `local.get x; drop` with `x` unset or out of
range is stuck, and its image is empty.

`dce2_removes_more`: `dce2` is not the fused transform `dce`. On
`i32.const 1; local.tee 0; drop` with local `0` dead, `dce2` removes everything and `dce`
keeps `i32.const 1; drop`, because the fused transform looks for the dead consumer only
immediately after the producer, before the dead `local.tee` has been deleted.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Two-pass DCE correctness.** If a fragment function body, run under its outer label,
reaches a result, the `dce2` body reaches the same result and store from any frame that
agrees with the original on the body's live-in locals. -/
theorem dce2_result {s s₁ : Store H} {f f' f₁ : Frame} {n : Nat} {e : Expr} {r : Result}
    (he : fragSeq e = true) (hf : FrameRel (liveEntry e) f f')
    (h : Steps P host ⟨s, f, [.label n [] (expression e)]⟩ ⟨s₁, f₁, r.toAdmin⟩) :
    ∃ f₁', Steps P host ⟨s, f', [.label n [] (expression (dce2 e))]⟩ ⟨s₁, f₁', r.toAdmin⟩ := by
  obtain ⟨f₁', h₁⟩ := localDce_result he hf h
  exact ⟨f₁', dropElim_result h₁⟩

/-- Two-pass DCE correctness from the same frame. -/
theorem dce2_result_same_frame {s s₁ : Store H} {f f₁ : Frame} {n : Nat} {e : Expr}
    {r : Result} (he : fragSeq e = true)
    (h : Steps P host ⟨s, f, [.label n [] (expression e)]⟩ ⟨s₁, f₁, r.toAdmin⟩) :
    ∃ f₁', Steps P host ⟨s, f, [.label n [] (expression (dce2 e))]⟩ ⟨s₁, f₁', r.toAdmin⟩ :=
  dce2_result he (FrameRel.refl _ _) h

/-- The two-pass DCE preserves a `return` out of the body, with its values. -/
theorem dce2_returning {s s₁ : Store H} {f f' f₁ : Frame} {n : Nat} {e : Expr} {vs : List Val}
    (he : fragSeq e = true) (hf : FrameRel (liveEntry e) f f')
    (h : Steps P host ⟨s, f, [.label n [] (expression e)]⟩
      ⟨s₁, f₁, vals vs ++ [.plain .return_]⟩) :
    ∃ f₁', Steps P host ⟨s, f', [.label n [] (expression (dce2 e))]⟩
      ⟨s₁, f₁', vals vs ++ [.plain .return_]⟩ := by
  obtain ⟨f₁', h₁⟩ := localDce_returning he hf h
  exact ⟨f₁', dropElim_returning h₁⟩

/-- The two-pass DCE preserves divergence. -/
theorem dce2_diverges {s : Store H} {f f' : Frame} {n : Nat} {e : Expr}
    (he : fragSeq e = true) (hf : FrameRel (liveEntry e) f f')
    (h : Diverges P host ⟨s, f, [.label n [] (expression e)]⟩) :
    Diverges P host ⟨s, f', [.label n [] (expression (dce2 e))]⟩ :=
  dropElim_diverges (localDce_diverges he hf h)

/-! ## `dce2` removes strictly more than `dce` -/

/-- On `i32.const 1; local.tee 0; drop`, `dce2` removes everything, while `dce` keeps
`i32.const 1; drop`. -/
theorem dce2_removes_more :
    dce2 teeDropExample = [] ∧ dce teeDropExample = [.intConst .i32 1, .drop] := by
  constructor <;> rfl

theorem dce2_ne_dce : dce2 ≠ dce := fun h => by
  have := dce2_removes_more
  rw [h] at this
  simp [this.2] at this

end Silmaril.Wasm.Dataflow

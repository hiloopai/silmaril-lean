module

public import Silmaril.Wasm.JcoTool.KReadComp.Defs
public import Silmaril.Wasm.JcoTool.KRead.Thms
public import Silmaril.Wasm.Component.Algebra.Ops.Thms

/-!
# The component of an observed runtime denotes its reading

* `maskH_den`, `den_maskH`: the stream game of a transformer is unchanged by the mask of one
  function on either side (`den_id` is the mask; `den_comp`; the identity is a unit up to
  equivalence);
* `wire_in`, `wire_out`: the import and export wiring of a one-function core instance compose to
  the mask;
* **`obsComp_denU`**: `(obsComp O).denU obsSem = O.game`.
-/

public section

namespace Silmaril.Proofs.Wasm.JcoTool.KReadComp

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.JcoTool.KRead (Obs)
open Silmaril.Wasm.JcoTool.KReadComp

variable {σ : Type}

theorem id_comp_equiv (T : Tr σ Val Val) : ((Tr.id : Tr Unit Val Val).comp T).Equiv T := fun xs =>
  ⟨by rw [Tr.runP_comp', Tr.runP_id], by rw [Tr.run_comp', Tr.run_id]⟩

theorem comp_id_equiv (T : Tr σ Val Val) : (T.comp (Tr.id : Tr Unit Val Val)).Equiv T := fun xs =>
  ⟨by rw [Tr.runP_comp', Tr.runP_id], by rw [Tr.run_comp', Tr.run_id]⟩

/-- The mask below the stream game of a transformer changes nothing. -/
theorem maskH_den (T : Tr σ Val Val) :
    (Strategy.ofHandler (maskH 1)).comp (StreamGame.den T) = StreamGame.den T := by
  rw [← StreamGame.den_id, ← StreamGame.den_comp]
  exact StreamGame.den_congr (id_comp_equiv T)

/-- The mask above the stream game of a transformer changes nothing. -/
theorem den_maskH (T : Tr σ Val Val) :
    (StreamGame.den T).comp (Strategy.ofHandler (maskH 1)) = StreamGame.den T := by
  rw [← StreamGame.den_id, ← StreamGame.den_comp]
  exact StreamGame.den_congr (comp_id_equiv T)

/-- The import wiring of the instance, then its widening, is the mask. -/
theorem wire_in : (maskH 1).comp ((implsN 1 [Impl.fwd 0] 1).comp (widenH 1)) = maskH 1 := by
  funext q
  obtain ⟨n, p⟩ := q
  cases n with
  | zero =>
    simp [Handler.comp, Prog.interp, implsH, Impl.prog, runChain, Target.prog, implsN, widenH, maskH]
  | succ n =>
    simp [Handler.comp, widenH, maskH, Target.prog]

/-- The export narrowing of the instance, then its widening, is the mask. -/
theorem wire_out : ((narrowH 1).comp (widenH 1)).comp (maskH 1) = maskH 1 := by
  funext q
  obtain ⟨n, p⟩ := q
  cases n with
  | zero =>
    simp [Handler.comp, Prog.interp, narrowH, widenH, maskH, Target.prog]
  | succ n =>
    simp [Handler.comp, maskH, Target.prog]

/-- **The component of an observed runtime denotes its strategy reading.** -/
theorem obsComp_denU (O : Obs) : (obsComp O).denU obsSem = O.game := by
  have hT : (obsComp O).denU obsSem =
      (ext 1 (Strategy.ofHandler (maskH 1)) (coreNode obsSem 1 O [Impl.fwd 0])).comp
        (Strategy.ofHandler (exportsH (1 + [(⟨"out", Streams.Alg.ftS, Impl.fwd 0⟩ : Export)].length)
          (reexport 1 [⟨"out", Streams.Alg.ftS, Impl.fwd 0⟩]))) := by
    simp only [obsComp, Comp.denU, denNodes, Node.den, Node.width, envAfter]
    rfl
  have hG : O.game = StreamGame.den (Silmaril.Wasm.JcoTool.KRead.ofObs O.partF O.wholeF) := rfl
  rw [hT, ext_comp_reexport]
  simp only [coreNode, obsSem, atSizes, List.length_singleton]
  rw [hG]
  calc _ = (Strategy.ofHandler ((maskH 1).comp ((implsN 1 [Impl.fwd 0] 1).comp (widenH 1)))).comp
        ((StreamGame.den (Silmaril.Wasm.JcoTool.KRead.ofObs O.partF O.wholeF)).comp
          (Strategy.ofHandler (((narrowH 1).comp (widenH 1)).comp (maskH 1)))) := by
        simp only [Strategy.ofHandler_comp, Strategy.comp_assoc]
        rfl
    _ = _ := by rw [wire_in, wire_out, den_maskH, maskH_den]

end Silmaril.Proofs.Wasm.JcoTool.KReadComp

module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Spec

@[expose] public section

/-!
# The Farkas checker: soundness over sessions

`farkas_session`: in every closed-world Core 3.0 session of export calls on `farkasI` (every
profile, every environment), a `check` answering `1` certifies the rows loaded since the
previous `check` (`WRows.IsCert`); `farkas_session_infeasible`: their system has no solution
over any ordered field (`ℚ`, `ℝ`). From `Common.session_allGood` with `farkas_spec`, starting
from the instance's store (`Rep [] farkasStore`).
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
open Silmaril.Wasm.Spec.Multi (Call Session)
open Silmaril.Logic.LinArith (WRows Feasible)
open Silmaril.Wasm.Examples.Common (session_allGood allGood_append)

theorem rep_init : Rep [] farkasI.store := ⟨Mach.init, farkasStore_holds, inv_init⟩

/-- **Soundness of the Wasm checker over sessions**: whenever `check` answers `1`, the rows
loaded since the previous `check` carry a valid Farkas certificate. -/
theorem farkas_session {P : Silmaril.Wasm.Numerics.Profile} {K : Env farkasI.E} {l₁ l₂ : List (Call farkasI)}
    {c : Call farkasI} (h : Session P farkasI K farkasI.store (l₁ ++ c :: l₂))
    (hc : c.1.1.val = 2) (h1 : Answer.toResult (ft := farkasI.exports.get c.1.1) c.2 = .values [Val.i32 1]) :
    WRows.IsCert (loaded l₁) :=
  allGood_append (session_allGood (fun f => farkas_spec f) rep_init h) hc h1

/-- **The loaded system is infeasible** over every ordered field when `check` answers `1`. -/
theorem farkas_session_infeasible {P : Silmaril.Wasm.Numerics.Profile} {K : Env farkasI.E} {l₁ l₂ : List (Call farkasI)}
    {c : Call farkasI} (h : Session P farkasI K farkasI.store (l₁ ++ c :: l₂))
    (hc : c.1.1.val = 2) (h1 : Answer.toResult (ft := farkasI.exports.get c.1.1) c.2 = .values [Val.i32 1])
    (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    ¬ Feasible 𝕜 (WRows.system (loaded l₁)) :=
  (farkas_session h hc h1).not_feasible

end Silmaril.Wasm.Examples.Farkas

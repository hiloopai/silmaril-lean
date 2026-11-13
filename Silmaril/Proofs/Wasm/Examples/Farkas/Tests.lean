module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Session

@[expose] public section

/-!
# The Farkas checker: tests

Consequences of `farkas_session` for concrete call sequences, every profile and environment:

* `bogus_rejected`: the system `x₀ ≤ 1, -x₀ ≤ -2` loaded with the wrong multipliers `1, 2`
  (they leave `-x₀` uncancelled): no session answers `1` to the following `check`;
* `overflow_rejected`: the row `2³² x₀ ≤ -1` with multiplier `2³²` cancels in wrapping `i64`
  arithmetic (`2³² · 2³² ≡ 0 mod 2⁶⁴`, and `2³² · (-1) < 0`), so a checker with wraparound
  would accept; the system is feasible (`x₀ = -1`, `overflow_feasible`), and no session answers
  `1` to the following `check`.

Positive tests (valid certificates accepted) are in `Complete` (`cert_accepted`) and `Total`
(`cert_session`: a session answering `1` exists).
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
open Silmaril.Wasm.Spec.Multi (Call Session)
open Silmaril.Logic.LinArith (WRows Feasible Ineq)

/-- The call `row(y, b)`. -/
def rowOp (y b : BitVec 64) : farkasI.F.Op :=
  ⟨⟨0, by decide⟩, ⟨[Val.i64 y, Val.i64 b], .cons ⟨y, rfl⟩ (.cons ⟨b, rfl⟩ .nil)⟩⟩

/-- The call `entry(j, a)`. -/
def entryOp (j : BitVec 32) (a : BitVec 64) : farkasI.F.Op :=
  ⟨⟨1, by decide⟩, ⟨[Val.i32 j, Val.i64 a], .cons ⟨j, rfl⟩ (.cons ⟨a, rfl⟩ .nil)⟩⟩

/-- The call `check()`. -/
def checkOp : farkasI.F.Op := ⟨⟨2, by decide⟩, ⟨[], .nil⟩⟩

/-- No session answers `1` to a `check` after calls whose loaded rows are not a certificate. -/
theorem no_accept {P : Silmaril.Wasm.Numerics.Profile} {K : Env farkasI.E} {l₁ l₂ : List (Call farkasI)}
    (hbad : ¬ WRows.IsCert (loaded l₁)) {w : farkasI.F.Ar checkOp}
    (hw : Answer.toResult (ft := farkasI.exports.get checkOp.1) w = .values [Val.i32 1]) :
    ¬ Session P farkasI K farkasI.store (l₁ ++ ⟨checkOp, w⟩ :: l₂) :=
  fun h => hbad (farkas_session h rfl hw)

/-- **A bogus certificate is rejected.** -/
theorem bogus_rejected {P : Silmaril.Wasm.Numerics.Profile} {K : Env farkasI.E} {l₂ : List (Call farkasI)}
    (w₁ : farkasI.F.Ar (rowOp 1 1)) (w₂ : farkasI.F.Ar (entryOp 0 1))
    (w₃ : farkasI.F.Ar (rowOp 2 (-2))) (w₄ : farkasI.F.Ar (entryOp 0 (-1))) {w : farkasI.F.Ar checkOp}
    (hw : Answer.toResult (ft := farkasI.exports.get checkOp.1) w = .values [Val.i32 1]) :
    ¬ Session P farkasI K farkasI.store
      ([⟨rowOp 1 1, w₁⟩, ⟨entryOp 0 1, w₂⟩, ⟨rowOp 2 (-2), w₃⟩, ⟨entryOp 0 (-1), w₄⟩] ++
        ⟨checkOp, w⟩ :: l₂) := by
  have hl : loaded [⟨rowOp 1 1, w₁⟩, ⟨entryOp 0 1, w₂⟩, ⟨rowOp 2 (-2), w₃⟩, ⟨entryOp 0 (-1), w₄⟩] =
      [(2, ⟨[(0, -1)], -2⟩), (1, ⟨[(0, 1)], 1⟩)] := rfl
  refine no_accept (fun hc => ?_) hw
  have h0 := hc.comb_zero 0
  rw [hl] at h0
  revert h0
  decide

/-- **An overflowing certificate is rejected.** -/
theorem overflow_rejected {P : Silmaril.Wasm.Numerics.Profile} {K : Env farkasI.E} {l₂ : List (Call farkasI)}
    (w₁ : farkasI.F.Ar (rowOp (2 ^ 32) (-1))) (w₂ : farkasI.F.Ar (entryOp 0 (2 ^ 32)))
    {w : farkasI.F.Ar checkOp}
    (hw : Answer.toResult (ft := farkasI.exports.get checkOp.1) w = .values [Val.i32 1]) :
    ¬ Session P farkasI K farkasI.store
      ([⟨rowOp (2 ^ 32) (-1), w₁⟩, ⟨entryOp 0 (2 ^ 32), w₂⟩] ++ ⟨checkOp, w⟩ :: l₂) := by
  have hl : loaded [⟨rowOp (2 ^ 32) (-1), w₁⟩, ⟨entryOp 0 (2 ^ 32), w₂⟩] =
      [(2 ^ 32, ⟨[(0, 2 ^ 32)], -1⟩)] := rfl
  refine no_accept (fun hc => ?_) hw
  have h0 := hc.comb_zero 0
  rw [hl] at h0
  revert h0
  decide

/-- With wrapping `i64` arithmetic the overflowing rows would look like a certificate. -/
theorem overflow_wraps : (2 ^ 32 : BitVec 64) * 2 ^ 32 = 0 ∧ ((2 ^ 32 : BitVec 64) * (-1)).toInt < 0 := by
  decide

/-- The overflowing system `2³² x₀ ≤ -1` is feasible. -/
theorem overflow_feasible : Feasible ℚ [⟨[(0, 2 ^ 32)], -1⟩] :=
  ⟨fun _ => -1, fun r hr => by
    rw [List.mem_singleton] at hr
    subst hr
    norm_num [Ineq.Sat, Ineq.eval]⟩

end Silmaril.Wasm.Examples.Farkas

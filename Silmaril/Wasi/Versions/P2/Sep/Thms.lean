module

public import Silmaril.Wasi.Versions.P2.Sep.Defs
public import Silmaril.Proofs.Wasi.Versions.P2.Sep

@[expose] public section

/-!
# WASI 0.2: the strict and the loose reading differ on components

* **`trusting_strict`**: under the strict WASI 0.2 theory, `trusting` writes only within its
  permits (`agP (p2Th .strict) permitG`, by the invariant method, `trusting_inv`).
* **`trusting_not_loose`**, a refutation: under the loose theory it does not. `trustRun` is a
  play of `trusting` (`trustRun_mem`) whose answers the loose theory accepts
  (`trustRun_loose`: `check-write` answers `ok(0)` after the pollable was ready) and whose
  one-byte write exceeds the permit (`trustRun_violates`).

So a component that is correct for the strict reading of `check-write` (the WIT text "When this
pollable is ready, `check-write` will return `ok(n)` with n>0") need not be correct for hosts that
report a conservative budget.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Games
open Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)

/-- **`trusting` is permit-safe under the strict WASI 0.2 theory.** -/
theorem trusting_strict : (agP (p2Th .strict) permitG).holds (ofBody trusting) :=
  ag_of_inv trusting_inv

/-- **`trustRun` is a play of `trusting`.** -/
theorem trustRun_mem : trustRun ∈ ofBody trusting := by
  have h1 := (Reach.nil (h := trusting)).snoc (CStep.ask runQ2)
  have h2 := h1.snoc (CStep.call runQ2 getOp2 tGot)
  have h3 := h2.snoc (CStep.reply runQ2 getOp2 tGot (some [.u32 0]))
  have h4 := h3.snoc (CStep.call (h := trusting) runQ2 (subOp 0) (tSub 0))
  have h5 := h4.snoc (CStep.reply runQ2 (subOp 0) (tSub 0) (some [.u32 1]))
  have h6 := h5.snoc (CStep.call (h := trusting) runQ2 (blkOp 1) (tBlk 0))
  have h7 := h6.snoc (CStep.reply runQ2 (blkOp 1) (tBlk 0) (some []))
  have h8 := h7.snoc (CStep.call (h := trusting) runQ2 (cwOp 0) (tCw 0))
  have h9 := h8.snoc (CStep.reply runQ2 (cwOp 0) (tCw 0) (some [okV (some (.u64 0))]))
  exact ⟨_, h9.snoc (CStep.call (h := trusting) runQ2 (wr1Op 0) tDone)⟩

/-- The loose WASI 0.2 theory accepts the answers of `trustRun`. -/
theorem trustRun_loose : (p2Th .loose).Accepts (hostView (wtrace trustRun)) :=
  (Protocol.acceptsB_iff _ _).1 (by decide +kernel)

/-- The write of `trustRun` exceeds the permit. -/
theorem trustRun_violates : ¬ permitG.Accepts (wtrace trustRun) := fun h =>
  absurd ((Protocol.acceptsB_iff _ _).2 h) (by decide +kernel)

/-- **`trusting` is not permit-safe under the loose WASI 0.2 theory.** -/
theorem trusting_not_loose : ¬ (agP (p2Th .loose) permitG).holds (ofBody trusting) :=
  fun h => trustRun_violates (h trustRun trustRun_mem trustRun_loose)

end Silmaril.Wasi.Versions.P2

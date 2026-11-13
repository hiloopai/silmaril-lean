module

public import Silmaril.Wasi.Versions.P2OverP3.SepRef.Defs
public import Silmaril.Wasi.Versions.P2OverP3.Sep.Thms
public import Silmaril.Wasm.Component.Async.RefZero.Thms

@[expose] public section

/-!
# WASI 0.2 over 0.3: the separating play against the reference machine (header)

REFUTED: **`sepPlay_not_refW`**: the host answers of the separating play `sepPlay 4096`
(`Silmaril.Wasi.Versions.P2OverP3.Sep`) violate `refW`: after the `stream-write COMPLETED 0` event,
`stream.write(2, 0^4096)` answers `COMPLETED 0`, which the reference machine never does for a
non-empty write (`Silmaril.Wasm.Component.Async.RefZero.ref_own_progress_pos`). The earlier event
itself contradicts `ref_zeroRead_meets_write` (a zero-length read leaves a parked non-empty write
parked, with no event) and `ref_peer_progress_pos`.

So `p2OverP3_not_strict` holds against `p3Th`, a theory that accepts answers no reference
runtime gives; it is **not** established against `p3Th ⊗ refW`. Whether `p2OverP3 cap`
(`cap > 0`) satisfies the strict 0.2 reading over every host of a reference-faithful 0.3 theory
is open: with copies that always make progress, a pollable is ready only after a write made
progress, so the buffer has room at the next `check-write`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)

/-- **REFUTED: the separating play's host answers are not the reference machine's.** -/
theorem sepPlay_not_refW : ¬ refW.Accepts (hostView (wtrace (sepPlay 4096))) :=
  fun h => absurd ((Protocol.acceptsB_iff _ _).2 h) (by decide +kernel)

/-- `p3Th` accepts the play, `refW` rejects it. -/
theorem sepPlay_p3Th_not_refW :
    p3Th.Accepts (hostView (wtrace (sepPlay 4096))) ∧
      ¬ refW.Accepts (hostView (wtrace (sepPlay 4096))) :=
  ⟨sepPlay_host, sepPlay_not_refW⟩

end Silmaril.Wasi.Versions.P2OverP3

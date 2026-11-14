module

public import Silmaril.Wasi.Versions.P2OverP3.Sep.Defs
public import Silmaril.Wasi.Versions.P2OverP3.Comp.Thms
public import Silmaril.Proofs.Wasi.Versions.P2OverP3.Sep
public import Silmaril.Wasi.Versions.P2.Sep.Thms
public import Silmaril.Wasi.Versions.P2.World.Thms
public import Silmaril.Wasm.Component.Async.Thms

@[expose] public section

/-!
# WASI 0.2 over 0.3: separation from the strict reading (header)

PROVED, for the default buffer size `4096`:

* **`sepPlay_mem`**: `sepPlay 4096` is a play of `p2OverP3 4096` (computed by `session`,
  `Silmaril.Proofs.Wasi.Versions.P2OverP3.Sep`).
* **`sepPlay_host`**: its WASI 0.3 answers are accepted by `p3Th` (typing, clock, loose stdout),
  so the loose host of `p3Th` (a model, `Silmaril.Wasi.loose_sat`) can give them.
* **`sepPlay_blockThenZero`**: its last two returns are `block` returning and then
  `check-write` answering `ok(0)`: a ready pollable followed by a zero budget.
* **`sepPlay_loose`** (from `p2OverP3_sat`) and **`sepPlay_not_strict`**: the loose WASI 0.2
  theory accepts its returns, the strict one rejects them.
* **REFUTED: `p2OverP3_not_strict`**: `¬ (agP p3Th (retG (p2Th .strict))).holds (p2OverP3 4096)`.
  WASI 0.2 over 0.3 is not a model of the strict 0.2 theory over every 0.3 host.
* **`p2OverP3_strict_ne_loose`**: the composite produces a witness of `p2_strict_ne_loose`; a
  guest that trusts the strict reading (`trusting`, refuted under the loose theory by
  `trusting_not_loose`) gets no guarantee from `p2OverP3_model`.
* **The answers are the store model's** (`zeroRead_completes_write`, `write_meets_zeroRead`):
  in `Silmaril.Wasm.Component.Async`, a pending `stream.write` met by a zero-length `stream.read`
  completes with a `stream-write` event `COMPLETED 0`, and a `stream.write` meeting a pending
  zero-length read completes at once with `COMPLETED 0`. (That model does not give zero-length
  copies their special meaning of the reference `definitions.py`; the separation itself rests
  on `p3Th`, which accepts these answers.) the reference machine rejects them
  (`Silmaril.Wasm.Component.Async.RefZero`, `Silmaril.Wasi.Versions.P2OverP3.SepRef.sepPlay_not_refW`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions.P2

/-- The session of the separating play runs to its end. -/
theorem sepSession_isSome : (sepSession 4096).isSome = true := by decide +kernel

/-- **`sepPlay 4096` is a play of `p2OverP3 4096`.** -/
theorem sepPlay_mem : sepPlay 4096 ∈ p2OverP3 4096 := by
  obtain ⟨⟨ms, s'⟩, hs⟩ := Option.isSome_iff_exists.1 sepSession_isSome
  have hp : sepPlay 4096 = ms := by simp [sepPlay, hs]
  rw [hp]
  exact session_mem hs

/-- **Its WASI 0.3 answers are accepted by the WASI 0.3 theory.** -/
theorem sepPlay_host : p3Th.Accepts (hostView (wtrace (sepPlay 4096))) :=
  (Protocol.acceptsB_iff _ _).1 (by decide +kernel)

/-- **`block` returns, then `check-write` answers `ok(0)`.** -/
theorem sepPlay_blockThenZero : blockThenZero (retAsImp (wtrace (sepPlay 4096))) = true := by
  decide +kernel

/-- The loose WASI 0.2 theory accepts its returns. -/
theorem sepPlay_loose : (p2Th .loose).Accepts (retAsImp (wtrace (sepPlay 4096))) :=
  (accepts_retG _ _).1 (p2OverP3_sat 4096 _ sepPlay_mem
    ((Protocol.accepts_prod_iff _ _ _).1 ((Protocol.accepts_prod_iff _ _ _).1 sepPlay_host).2).1)

/-- The strict WASI 0.2 theory rejects its returns. -/
theorem sepPlay_not_strict : ¬ (p2Th .strict).Accepts (retAsImp (wtrace (sepPlay 4096))) :=
  fun h => absurd ((Protocol.acceptsB_iff _ _).2 h) (by decide +kernel)

/-- **REFUTED: WASI 0.2 over 0.3 is not a model of the strict 0.2 theory** over every host of
the WASI 0.3 theory. -/
theorem p2OverP3_not_strict : ¬ (agP p3Th (retG (p2Th .strict))).holds (p2OverP3 4096) :=
  fun h => sepPlay_not_strict ((accepts_retG _ _).1 (h _ sepPlay_mem sepPlay_host))

/-- **The composite separates the readings**: an instance of `p2_strict_ne_loose` produced by
WASI 0.2 over 0.3. -/
theorem p2OverP3_strict_ne_loose :
    ∃ t, (p2Th .loose).Accepts t ∧ ¬ (p2Th .strict).Accepts t ∧
      ∃ s ∈ p2OverP3 4096, p3Th.Accepts (hostView (wtrace s)) ∧ t = retAsImp (wtrace s) :=
  ⟨_, sepPlay_loose, sepPlay_not_strict, sepPlay 4096, sepPlay_mem, sepPlay_host, rfl⟩

/-- The two separations side by side: the loose theory admits answers the strict one rejects
(`p2_strict_ne_loose`), a guest trusting the strict reading is unsafe under the loose one
(`trusting_not_loose`), and WASI 0.2 over 0.3 actually gives such answers
(`p2OverP3_not_strict`). -/
theorem p2OverP3_separation :
    (∃ t, (p2Th .loose).Accepts t ∧ ¬ (p2Th .strict).Accepts t) ∧
      ¬ (agP (p2Th .loose) permitG).holds (ofBody trusting) ∧
      ¬ (agP p3Th (retG (p2Th .strict))).holds (p2OverP3 4096) :=
  ⟨p2_strict_ne_loose, trusting_not_loose, p2OverP3_not_strict⟩

/-! ## The host's answers in the store model -/

open Silmaril.Wasm.Component.Async in
/-- **A pending write met by a zero-length read** completes with `COMPLETED 0` (a `stream-write`
event), and no copy is pending afterwards. -/
theorem zeroRead_completes_write {st : Store} {r w s : Nat} {xs : List Val}
    (hw : st.tbl w = some (.streamW s)) (hr : st.tbl r = some (.streamR s))
    (hp : (st.chans s).pend = .idle) (hd : (st.chans s).rDropped = false) :
    ∃ st₁ st₂, step st (.streamWrite w xs) = some (st₁, .nat blocked) ∧
      step st₁ (.streamRead r 0) = some (st₂, .read (packCopy .completed 0) []) ∧
      st₂.ev w = some ⟨.streamWrite, w, packCopy .completed 0, []⟩ ∧
      (st₂.chans s).pend = .idle := by
  simp [step, Silmaril.Wasm.Component.Async.streamWrite, Silmaril.Wasm.Component.Async.streamRead, hw,
    hr, hp, hd, Store.setChan, Store.post, Silmaril.Wasm.Component.Async.upd]

open Silmaril.Wasm.Component.Async in
/-- **A write meeting a pending zero-length read** completes at once with `COMPLETED 0`. -/
theorem write_meets_zeroRead {st : Store} {r w s : Nat} {xs : List Val}
    (hw : st.tbl w = some (.streamW s)) (hr : st.tbl r = some (.streamR s))
    (hp : (st.chans s).pend = .idle) (hd : (st.chans s).wDropped = false) :
    ∃ st₁ st₂, step st (.streamRead r 0) = some (st₁, .nat blocked) ∧
      step st₁ (.streamWrite w xs) = some (st₂, .nat (packCopy .completed 0)) := by
  obtain ⟨st₁, st₂, h1, h2, -, -⟩ := read_write (n := 0) (xs := xs) hw hr hp hd
  rw [Nat.zero_min] at h2
  exact ⟨st₁, st₂, h1, h2⟩

end Silmaril.Wasi.Versions.P2OverP3

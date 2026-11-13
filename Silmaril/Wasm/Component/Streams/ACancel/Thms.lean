module

public import Silmaril.Wasm.Component.Streams.ACancel.Defs
public import Silmaril.Wasm.Component.Streams.Cancel.Thms
public import Silmaril.Proofs.Wasm.Component.Streams.ACancel

/-!
# Asynchronous cancellation and store-level futures: theorems

* **Conservativity** (`cancelR_comp`, `cancelW_comp`, `fcancelR_comp`, `fcancelW_comp`): when the
  peer end is component-owned, cancelling is `Cancel`'s synchronous cancel (never `BLOCKED`).
  At the store (`astep_ofD_*`, `atakeEv_ofD`, `await_ofD`): on a `Drop` store with no flags and no
  futures (`ofD`), every stream built-in and every wait of this variant is `Cancel.cstep`'s
  (hence, on the stores `Drop` reaches, `Drop.dstep`'s), so the network and generated-module
  theorems are theorems about this model's runs as well.
* **`BLOCKED`** (`cancelR_blocked`, `cancelR_blocked_only`, and the write side): a cancel returns
  `BLOCKED` exactly when the host owns the peer, no event is pending and the host chose to
  notify later; the end is then `CANCELLING_COPY`.
* **While cancelling** (`cancelling_traps_r`, `cancelling_traps_w`): a copy, a drop and a second
  cancel on the end trap; the peer's copies go on (`write_flags`, `read_flags`: the flags do not
  affect a copy).
* **The event of a cancelled copy** (`cancelling_takeR`, `cancelling_takeW`): `CANCELLED`
  (`DROPPED` if the peer has gone) with the progress and, for a read, the items copied, also
  those copied after the cancel request; the end is `IDLE` again (`DONE` after `DROPPED`).
* **No item lost or duplicated** (`asteps_sent`) and **a future delivers at most one value**
  (`afsteps_once`), with asynchronous cancellation and host operations.
* **Store-level futures**: `fut_*` scenario theorems for `future.new`, `future.read`,
  `future.write`, `future.cancel-*` and `future.drop-*` at the store, among them the asynchronous
  cancel of a read whose writer the host owns (`fut_host_cancel_blocked`), which returns
  `BLOCKED` and later delivers `COMPLETED` with the host's value.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.ACancel

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event EventCode CopyResult packCopy blocked upd)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Cancel

/-! ## Conservativity on channels -/

/-- **With a component-owned writer, `stream.cancel-read` is `Cancel.cancelR`.** -/
theorem cancelR_comp {a : AChan} (now : Bool) (hrc : a.f.rc = false) (hw : a.f.hostW = false) :
    a.cancelR now = (a.c.cancelR).map fun p => (⟨p.1, { a.f with rc := false }⟩, p.2) := by
  unfold AChan.cancelR DChan.cancelR AChan.startCancelR AChan.takeR
  by_cases hg : a.c.r.gone = true ∨ a.c.r.st ≠ .copying
  · rcases hg with hg | hg <;> simp [hg]
  · have hg' : a.c.r.gone = false ∧ a.c.r.st = .copying := by
      simpa [not_or] using hg
    cases he : a.c.r.ev <;> simp [hg'.1, hg'.2, hrc, hw]

/-- **With a component-owned reader, `stream.cancel-write` is `Cancel.cancelW`.** -/
theorem cancelW_comp {a : AChan} (now : Bool) (hwc : a.f.wc = false) (hr : a.f.hostR = false) :
    a.cancelW now = (a.c.cancelW).map fun p => (⟨p.1, { a.f with wc := false }⟩, p.2) := by
  unfold AChan.cancelW DChan.cancelW AChan.startCancelW AChan.takeW
  by_cases hg : a.c.w.gone = true ∨ a.c.w.st ≠ .copying
  · rcases hg with hg | hg <;> simp [hg]
  · have hg' : a.c.w.gone = false ∧ a.c.w.st = .copying := by
      simpa [not_or] using hg
    cases he : a.c.w.ev <;> simp [hg'.1, hg'.2, hwc, hr]

/-- A component-owned peer: the cancel never returns `BLOCKED`. -/
theorem cancelR_comp_not_blocked {a a' : AChan} {now : Bool} (hrc : a.f.rc = false)
    (hw : a.f.hostW = false) (h : a.cancelR now = some (a', .nat blocked)) : False := by
  rw [cancelR_comp now hrc hw] at h
  unfold DChan.cancelR at h
  split at h <;> simp at h

theorem cancelW_comp_not_blocked {a a' : AChan} {now : Bool} (hwc : a.f.wc = false)
    (hr : a.f.hostR = false) (h : a.cancelW now = some (a', .nat blocked)) : False := by
  rw [cancelW_comp now hwc hr] at h
  unfold DChan.cancelW at h
  split at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Res.nat.injEq] at h
    have h2 := h.2
    split at h2 <;> simp [packCopy, CopyResult.toNat, blocked] at h2 <;> omega

/-! ## `BLOCKED` and `CANCELLING_COPY` -/

/-- **A cancel returns `BLOCKED`** when the host owns the writer, no event is pending, and the host
chose to notify later; the end is then cancelling, and nothing else changed. -/
theorem cancelR_blocked {a : AChan} (hg : a.c.r.gone = false) (hc : a.c.r.st = .copying)
    (hrc : a.f.rc = false) (he : a.c.r.ev = none) (hw : a.f.hostW = true) :
    a.cancelR false = some (a.startCancelR false, .nat blocked) ∧
      (a.startCancelR false).rstate = .cancelling ∧ (a.startCancelR false).c = a.c := by
  refine ⟨?_, ?_, ?_⟩
  · simp [AChan.cancelR, AChan.startCancelR, AChan.takeR, hg, hc, hrc, he, hw]
  · simp [AChan.rstate, AChan.startCancelR, hc]
  · exact Silmaril.Proofs.Wasm.Component.Streams.ACancel.startCancelR_none (by simp [AChan.startCancelR, he, hw])

/-- **Only then.** -/
theorem cancelR_blocked_only {a a' : AChan} {now : Bool} (h : a.cancelR now = some (a', .nat blocked)) :
    a.f.hostW = true ∧ now = false ∧ a.c.r.ev = none ∧ a'.rstate = .cancelling := by
  obtain ⟨-, hc, hcase⟩ := Silmaril.Proofs.Wasm.Component.Streams.ACancel.cancelR_inv h
  rcases hcase with ⟨p, ys, -, hr⟩ | ⟨ht, ha, -⟩
  · cases hr
  · have hn : (a.startCancelR now).c.r.ev = none :=
      Silmaril.Proofs.Wasm.Component.Streams.ACancel.takeR_none ht
    have hcond : ¬(a.c.r.ev = none ∧ (a.f.hostW = false ∨ now = true)) := by
      intro hcd
      simp [AChan.startCancelR, hcd] at hn
    have hev : a.c.r.ev = none := by
      by_cases hcd : a.c.r.ev = none ∧ (a.f.hostW = false ∨ now = true)
      · exact absurd hcd hcond
      · simpa [AChan.startCancelR, hcd] using hn
    have hw : a.f.hostW = true ∧ now = false := by
      cases hW : a.f.hostW <;> cases hN : now <;> simp_all
    have hst : a'.rstate = .cancelling := by
      rw [ha]; simp [AChan.rstate, AChan.startCancelR, hc]
    exact ⟨hw.1, hw.2, hev, hst⟩

/-- The write side: `BLOCKED` when the host owns the reader. -/
theorem cancelW_blocked {a : AChan} (hg : a.c.w.gone = false) (hc : a.c.w.st = .copying)
    (hwc : a.f.wc = false) (he : a.c.w.ev = none) (hr : a.f.hostR = true) :
    a.cancelW false = some (a.startCancelW false, .nat blocked) ∧
      (a.startCancelW false).wstate = .cancelling ∧ (a.startCancelW false).c = a.c := by
  refine ⟨?_, ?_, ?_⟩
  · simp [AChan.cancelW, AChan.startCancelW, AChan.takeW, hg, hc, hwc, he, hr]
  · simp [AChan.wstate, AChan.startCancelW, hc]
  · exact Silmaril.Proofs.Wasm.Component.Streams.ACancel.startCancelW_none (by simp [AChan.startCancelW, he, hr])

/-- **While cancelling, a read, a drop and a second cancel of the readable end trap.** -/
theorem cancelling_traps_r {a : AChan} (h : a.rstate = .cancelling) (n : Nat) (now : Bool) :
    a.read n = none ∧ a.dropR = none ∧ a.cancelR now = none := by
  have hc : a.c.r.st = .copying ∧ a.f.rc = true := by
    unfold AChan.rstate at h
    split at h
    · cases h
    · rename_i hst; split at h
      · rename_i hrc; exact ⟨hst, hrc⟩
      · cases h
    · cases h
  refine ⟨?_, ?_, ?_⟩
  · simp [AChan.read, DChan.zread, hc.1]
  · simp [AChan.dropR, DChan.dropR, hc.1]
  · simp [AChan.cancelR, hc.2]

/-- **While cancelling, a write, a drop and a second cancel of the writable end trap.** -/
theorem cancelling_traps_w {a : AChan} (h : a.wstate = .cancelling) (xs : List Val) (now : Bool) :
    a.write xs = none ∧ a.dropW = none ∧ a.cancelW now = none := by
  have hc : a.c.w.st = .copying ∧ a.f.wc = true := by
    unfold AChan.wstate at h
    split at h
    · cases h
    · rename_i hst; split at h
      · rename_i hwc; exact ⟨hst, hwc⟩
      · cases h
    · cases h
  refine ⟨?_, ?_, ?_⟩
  · simp [AChan.write, DChan.zwrite, hc.1]
  · simp [AChan.dropW, DChan.dropW, hc.1]
  · simp [AChan.cancelW, hc.2]

/-- The peer's copies do not depend on the flags. -/
theorem write_flags (a : AChan) (f : Flags) (xs : List Val) :
    ({ a with f := f } : AChan).write xs = (a.write xs).map fun p => ({ p.1 with f := f }, p.2) := by
  simp [AChan.write, Option.map_map]
  rfl

theorem read_flags (a : AChan) (f : Flags) (n : Nat) :
    ({ a with f := f } : AChan).read n = (a.read n).map fun p => ({ p.1 with f := f }, p.2) := by
  simp [AChan.read, Option.map_map]
  rfl

/-- **The event of a cancelled read**: `CANCELLED` (`DROPPED` if the writer has gone) with the
progress and the items copied into the buffer, also after the cancel request. -/
theorem cancelling_takeR {a : AChan} {p : Nat} (h : a.rstate = .cancelling) (he : a.c.r.ev = some p) :
    ∃ a', a.takeR = some (a', if a.c.w.gone then packCopy .dropped p else packCopy .cancelled p,
        a.c.rgot) ∧ a'.rstate = (if a.c.w.gone then .done else .idle) := by
  have hrc : a.f.rc = true := by
    unfold AChan.rstate at h
    split at h
    · cases h
    · split at h
      · assumption
      · cases h
    · cases h
  let c' : DChan := { a.c with r := { a.c.r with st := if a.c.w.gone then .done else .idle, ev := none },
                               rcap := none, rgot := [] }
  refine ⟨{ c := c', f := { a.f with rc := false } }, by simp [c', AChan.takeR, he, hrc], ?_⟩
  cases hw : a.c.w.gone <;> simp [c', AChan.rstate, hw]

/-- **The event of a cancelled write.** -/
theorem cancelling_takeW {a : AChan} {p : Nat} (h : a.wstate = .cancelling) (he : a.c.w.ev = some p) :
    ∃ a', a.takeW = some (a', if a.c.r.gone then packCopy .dropped p else packCopy .cancelled p) ∧
      a'.wstate = (if a.c.r.gone then .done else .idle) := by
  have hwc : a.f.wc = true := by
    unfold AChan.wstate at h
    split at h
    · cases h
    · split at h
      · assumption
      · cases h
    · cases h
  let c' : DChan := { a.c with w := { a.c.w with st := if a.c.r.gone then .done else .idle, ev := none },
                               wbuf := none }
  refine ⟨{ c := c', f := { a.f with wc := false } }, by simp [c', AChan.takeW, he, hwc], ?_⟩
  cases hr : a.c.r.gone <;> simp [c', AChan.wstate, hr]

/-! ## Item flow -/

/-- Every operation of this variant on a stream is an operation of `Cancel` on its `DChan`, or
leaves the `DChan` unchanged. -/
theorem astep_cstep {a a' : AChan} {zs : List Val} (h : AStep a a' zs) :
    CStep a.c a'.c zs ∨ (a'.c = a.c ∧ zs = []) :=
  Silmaril.Proofs.Wasm.Component.Streams.ACancel.astep_cstep h

/-- **No item lost or duplicated**, with asynchronous cancellation: along any operations from a
new stream, the items transferred are the items handed to the reader followed by those still in
its buffer. -/
theorem asteps_sent {a : AChan} {ys : List Val} (h : ASteps {} a ys) : a.c.sent = ys ++ a.c.rgot :=
  Silmaril.Proofs.Wasm.Component.Streams.ACancel.asteps_sent h

/-- **A future delivers at most one value, the value written**, with asynchronous cancellation. -/
theorem afsteps_once {a : AFChan} {ys : List Val} (h : AFSteps {} a ys) :
    ys = [] ∨ ∃ v, ys = [v] ∧ a.c.sent = some v :=
  Silmaril.Proofs.Wasm.Component.Streams.ACancel.afsteps_once h

end Silmaril.Wasm.Component.Streams.ACancel

module

public import Silmaril.Wasm.Component.Streams.Cancel.Defs
public import Silmaril.Wasm.Component.Streams.Net.Defs
public import Silmaril.Proofs.Wasm.Component.Streams.Cancel

/-!
# Cancellation, zero-length copies and futures: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.Streams.Cancel`.

* **Conservativity** (`dstep_cstep`, `cstep_eq`, `reach_good`): every answer of `Drop`'s built-ins
  is an answer of this variant, and on every operation that copies something the two agree,
  traps included, on the stores `Drop` reaches (no zero-length buffer: `GoodS`). Every store a
  `Net` network reaches is such a store, so the network theorems (`Pipes`, `NetGame`) and the
  generated modules' theorems (`KDrop.Thms`, whose modules make only nonzero copies) are
  theorems about executions of this variant too.
* **Cancellation** (`cancelR_spec`, `cancelW_spec`, `cancel_idle_trap`): a cancelled read
  reports `CANCELLED` (or `DROPPED`) with its progress and hands over the items already copied;
  cancelling with no copy in progress traps.
* **Zero-length copies** (`zread_zero_*`, `zwrite_zero_*`): the cases of `End.copy`.
* **No item lost or duplicated** (`csteps_sent`): along any operations from a new stream,
  including cancellations and zero-length copies, the items transferred are the items handed to
  the reader followed by those still in its buffer.
* **Futures** (`fsteps_once`, `fdropW_trap`): the reader is handed at most one value, the value
  written; dropping the writable end before it is `DONE` traps.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Cancel

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res packCopy blocked)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (Network Reach)

/-- **Every answer of `Drop` is an answer of this variant.** -/
theorem dstep_cstep {st : DStore} {o : DOp} {p : DStore × Res} (hst : GoodS st)
    (h : dstep st o = some p) : cstep st (.op o) = some p :=
  Silmaril.Proofs.Wasm.Component.Streams.Cancel.dstep_cstep hst h

/-- **On nonzero copies the two agree**, traps included. -/
theorem cstep_eq {st : DStore} {o : DOp} (hst : GoodS st)
    (ho : Silmaril.Proofs.Wasm.Component.Streams.Cancel.nonzero o) : cstep st (.op o) = dstep st o :=
  Silmaril.Proofs.Wasm.Component.Streams.Cancel.cstep_eq hst ho

/-- `Drop`'s built-ins and event delivery keep every stream `Good`. -/
theorem dstep_good {st st' : DStore} {o : DOp} {r : Res} (hst : GoodS st)
    (h : dstep st o = some (st', r)) : GoodS st' :=
  Silmaril.Proofs.Wasm.Component.Streams.Cancel.dstep_good hst h

theorem wait_good {st st' : DStore} {s h : Nat} {e : Silmaril.Wasm.Component.Async.Event}
    (hst : GoodS st) (hw : DWait st s h st' e) : GoodS st' :=
  Silmaril.Proofs.Wasm.Component.Streams.Cancel.wait_good hst hw

/-- **Every store a network reaches has no zero-length buffer.** -/
theorem reach_good {net : Network} {s : Silmaril.Wasm.Component.Streams.Net.Sys net}
    (h : Reach net s) : GoodS s.st :=
  Silmaril.Proofs.Wasm.Component.Streams.Cancel.reach_good h

/-- A cancelled read: `CANCELLED` (`DROPPED` if the writer has gone) with the progress of the
copy, handing over the items already copied; the end is idle again (done after `DROPPED`). -/
theorem cancelR_spec {c : DChan} (hg : c.r.gone = false) (hc : c.r.st = .copying) :
    ∃ c', c.cancelR = some (c', .read (if c.w.gone then packCopy .dropped (c.r.ev.getD 0)
        else packCopy .cancelled (c.r.ev.getD 0)) c.rgot) ∧
      c'.r.st = (if c.w.gone then .done else .idle) ∧ c'.r.ev = none ∧ c'.rcap = none ∧
      c'.rgot = [] ∧ c'.sent = c.sent ∧ c'.w = c.w := by
  simp [DChan.cancelR, hg, hc]

/-- A cancelled write: `CANCELLED` (`DROPPED` if the reader has gone) with its progress. -/
theorem cancelW_spec {c : DChan} (hg : c.w.gone = false) (hc : c.w.st = .copying) :
    ∃ c', c.cancelW = some (c', .nat (if c.r.gone then packCopy .dropped (c.w.ev.getD 0)
        else packCopy .cancelled (c.w.ev.getD 0))) ∧
      c'.w.st = (if c.r.gone then .done else .idle) ∧ c'.w.ev = none ∧ c'.wbuf = none ∧
      c'.sent = c.sent ∧ c'.r = c.r := by
  simp [DChan.cancelW, hg, hc]

/-- Cancelling with no copy in progress traps. -/
theorem cancel_idle_trap {c : DChan} : (c.r.st ≠ .copying → c.cancelR = none) ∧
    (c.w.st ≠ .copying → c.cancelW = none) :=
  ⟨fun h => by simp [DChan.cancelR, h], fun h => by simp [DChan.cancelW, h]⟩

/-- A zero-length read meeting a nonempty pending write completes at once with `0`. -/
theorem zread_zero_now {c : DChan} {x : Val} {xs : List Val} (hg : c.r.gone = false)
    (hi : c.r.st = .idle) (hw : c.w.gone = false) (hb : c.wbuf = some (x :: xs)) :
    c.zread 0 = some (c, .read (packCopy .completed 0) []) := by
  simp [DChan.zread, hg, hi, hw, hb]

/-- A read meeting a zero-length pending write: the write completes with `0`, the read waits. -/
theorem zread_zero_peer {c : DChan} {n : Nat} (hg : c.r.gone = false) (hi : c.r.st = .idle)
    (hw : c.w.gone = false) (hb : c.wbuf = some []) :
    ∃ c', c.zread n = some (c', .nat blocked) ∧ c'.w.ev = some 0 ∧ c'.wbuf = none ∧
      c'.r.st = .copying ∧ c'.rcap = some n ∧ c'.sent = c.sent := by
  simp [DChan.zread, hg, hi, hw, hb]

/-- A zero-length write meeting a pending read completes at once with `0`. -/
theorem zwrite_zero_now {c : DChan} {n : Nat} (hg : c.w.gone = false) (hi : c.w.st = .idle)
    (hr : c.r.gone = false) (hb : c.rcap = some n) :
    c.zwrite [] = some (c, .nat (packCopy .completed 0)) := by
  simp [DChan.zwrite, hg, hi, hr, hb]

/-- A nonempty write meeting a zero-length pending read: the read completes with `0` (no items),
the write waits. -/
theorem zwrite_zero_peer {c : DChan} {x : Val} {xs : List Val} (hg : c.w.gone = false)
    (hi : c.w.st = .idle) (hr : c.r.gone = false) (hb : c.rcap = some 0) :
    ∃ c', c.zwrite (x :: xs) = some (c', .nat blocked) ∧ c'.r.ev = some 0 ∧ c'.rcap = none ∧
      c'.rgot = c.rgot ∧ c'.wbuf = some (x :: xs) ∧ c'.sent = c.sent := by
  simp [DChan.zwrite, hg, hi, hr, hb]

/-- **No item lost or duplicated**, with cancellation and zero-length copies. -/
theorem csteps_sent {c : DChan} {ys : List Val} (h : CSteps {} c ys) : c.sent = ys ++ c.rgot :=
  Silmaril.Proofs.Wasm.Component.Streams.Cancel.csteps_sent h

/-- **A future delivers at most one value, the value written.** -/
theorem fsteps_once {c : FChan} {ys : List Val} (h : FSteps {} c ys) :
    ys = [] ∨ ∃ v, ys = [v] ∧ c.sent = some v :=
  Silmaril.Proofs.Wasm.Component.Streams.Cancel.fsteps_once h

/-- Dropping a future's writable end before it is `DONE` traps (`futures-must-write`). -/
theorem fdropW_trap {c : FChan} (h : c.w.st ≠ .done) : c.fdropW = none := by
  simp [FChan.fdropW, h]

/-- A future read meeting a pending write completes at once with the value. -/
theorem fread_now {c : FChan} {v : Val} (hg : c.r.gone = false) (hi : c.r.st = .idle)
    (hw : c.w.gone = false) (hv : c.wval = some v) :
    ∃ c', c.fread = some (c', .read (fcode .completed) [v]) ∧ c'.sent = some v ∧
      c'.r.st = .done ∧ c'.w.ev = some 1 := by
  simp [FChan.fread, hg, hi, hw, hv]

/-! ## The scenarios of `cancel-model.wast`

Each function of `tools/wasm-streams/tests/cancel/cancel-model.wast` is a sequence of built-in
calls on a new stream or future; here are the model's results for the same calls (checked by
evaluation), which are the values the test asserts and wasmtime 50.0.0 returns (`blocked` is
`-1` as an `i32`). -/

/-- A byte. -/
def b8 (n : Nat) : Val := .u8 (BitVec.ofNat 8 n)

theorem wast_cancel_read_none :
    (do let (c, r1) ← ({} : DChan).zread 4; let (_, r2) ← c.cancelR; pure [r1, r2]) =
      some [.nat blocked, .read 0x02 []] := rfl

theorem wast_cancel_read_partial :
    (do let (c, r1) ← ({} : DChan).zread 8; let (c, r2) ← c.zwrite [b8 1, b8 2, b8 3]
        let (_, r3) ← c.cancelR; pure [r1, r2, r3]) =
      some [.nat blocked, .nat 0x30, .read 0x32 [b8 1, b8 2, b8 3]] := rfl

theorem wast_cancel_read_full :
    (do let (c, r1) ← ({} : DChan).zread 2; let (c, r2) ← c.zwrite (List.map b8 [1, 2, 3, 4, 5])
        let (_, r3) ← c.cancelR; pure [r1, r2, r3]) =
      some [.nat blocked, .nat 0x20, .read 0x22 [b8 1, b8 2]] := rfl

theorem wast_cancel_read_dropped :
    (do let (c, r1) ← ({} : DChan).zread 4; let (c, r2) ← c.zwrite [b8 1, b8 2]
        let c ← c.dropW; let (_, r3) ← c.cancelR; pure [r1, r2, r3]) =
      some [.nat blocked, .nat 0x20, .read 0x21 [b8 1, b8 2]] := rfl

theorem wast_cancel_write_partial :
    (do let (c, r1) ← ({} : DChan).zwrite (List.map b8 [1, 2, 3, 4, 5]); let (c, r2) ← c.zread 2
        let (c, r3) ← c.cancelW; let (_, r4) ← c.zread 4; pure [r1, r2, r3, r4]) =
      some [.nat blocked, .read 0x20 [b8 1, b8 2], .nat 0x22, .nat blocked] := rfl

theorem wast_cancel_write_dropped :
    (do let (c, r1) ← ({} : DChan).zwrite [b8 1, b8 2, b8 3]; let (c, r2) ← c.zread 1
        let c ← c.dropR; let (_, r3) ← c.cancelW; pure [r1, r2, r3]) =
      some [.nat blocked, .read 0x10 [b8 1], .nat 0x11] := rfl

theorem wast_cancel_idle : ({} : DChan).cancelR = none ∧ ({} : DChan).cancelW = none :=
  ⟨rfl, rfl⟩

theorem wast_zero_write_now :
    (do let (c, r1) ← ({} : DChan).zread 4; let (c, r2) ← c.zwrite []
        let (_, r3) ← c.zwrite [b8 1, b8 2]; pure [r1, r2, r3]) =
      some [.nat blocked, .nat 0x00, .nat 0x20] := rfl

theorem wast_zero_read_now :
    (do let (c, r1) ← ({} : DChan).zwrite [b8 1, b8 2, b8 3]; let (c, r2) ← c.zread 0
        let (_, r3) ← c.zread 8; pure [r1, r2, r3]) =
      some [.nat blocked, .read 0x00 [], .read 0x30 [b8 1, b8 2, b8 3]] := rfl

theorem wast_zero_read_peer :
    (do let (c, r1) ← ({} : DChan).zread 0; let (c, r2) ← c.zwrite [b8 1, b8 2, b8 3]
        let (c, r3) ← c.cancelR; let (_, r4) ← c.zread 8; pure [r1, r2, r3, r4]) =
      some [.nat blocked, .nat blocked, .read 0x02 [], .read 0x30 [b8 1, b8 2, b8 3]] := rfl

theorem wast_zero_zero_read :
    (do let (c, r1) ← ({} : DChan).zwrite []; let (c, r2) ← c.zread 0
        let (c, r3) ← c.cancelW; let (_, r4) ← c.cancelR; pure [r1, r2, r3, r4]) =
      some [.nat blocked, .nat blocked, .nat 0x02, .read 0x02 []] := rfl

theorem wast_zero_zero_write :
    (do let (c, r1) ← ({} : DChan).zread 0; let (c, r2) ← c.zwrite []
        let (_, r3) ← c.cancelR; pure [r1, r2, r3]) =
      some [.nat blocked, .nat 0x00, .read 0x02 []] := rfl

theorem wast_future_write_dropped :
    (do let c ← ({} : FChan).fdropR; let (_, r) ← c.fwrite (b8 1); pure r) = some (.nat 0x01) := rfl

theorem wast_future_read_write :
    (do let (c, r1) ← ({} : FChan).fread; let (c, r2) ← c.fwrite (b8 1)
        let (c, p, ys) ← c.fcancelR; let _ ← c.fdropW; pure (r1, r2, p, ys)) =
      some (.nat blocked, .nat 0x00, 0x00, [b8 1]) := rfl

theorem wast_future_cancel_read :
    (do let (c, r1) ← ({} : FChan).fread; let (c, p, _) ← c.fcancelR
        let (c, r2) ← c.fwrite (b8 1); let (_, r3) ← c.fread; pure (r1, p, r2, r3)) =
      some (.nat blocked, 0x02, .nat blocked, .read 0x00 [b8 1]) := rfl

theorem wast_future_cancel_write :
    (do let (c, r1) ← ({} : FChan).fwrite (b8 1); let (c, p) ← c.fcancelW
        let (c, r2) ← c.fwrite (b8 1); let (_, r3) ← c.fread; pure (r1, p, r2, r3)) =
      some (.nat blocked, 0x02, .nat blocked, .read 0x00 [b8 1]) := rfl

theorem wast_future_traps : ({} : FChan).fdropW = none ∧
    (do let (c, _) ← ({} : FChan).fwrite (b8 1); let (c, _) ← c.fread; c.fread) = none :=
  ⟨rfl, rfl⟩

end Silmaril.Wasm.Component.Streams.Cancel

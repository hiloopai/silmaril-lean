module

public import Silmaril.Wasi.Versions.P2.World.Defs
public import Silmaril.Wasi.Versions.P3.Defs

@[expose] public section

/-!
# WASI 0.3 over 0.2: the theories on both sides

Relation (b) of `docs/projects/wasm-wasi.md` implements the WASI 0.3 slice `P3.p3World` by a
component importing the WASI 0.2 command world `P2.p2Command`
(`Silmaril.Wasi.Versions.P3OverP2.Impl`). This module fixes the theories it is proved against.

## Corrections of the 0.3 theories (each a weakening, see `Theory.Thms`)

Three clauses of `Silmaril.Wasi.Versions.P3` cannot be satisfied by any host that answers every
call, or by `host3` (refutations in `Silmaril.Wasi.Versions.P3OverP2.Theory.Thms`):

* **Ill-shaped calls.** `outStep` rejects *every* answer to a `stream.write` whose argument list
  is not `[w, buf]` and to a `write-via-stream` whose argument list is not `[r]`; `rdStep`
  rejects every answer to a `read-via-stream` whose arguments are not `[u32, u64]` and to a
  `stream.read` of a known stream whose count is not a `u32`. Arguments are not constrained by
  the signature (`nsig`), so a guest can make these calls. `stdoutTh3w` and `fsReadTh3w F`
  leave such calls unconstrained.
* **Zero-length reads.** `rdStep` demands `0 < k` of a `COMPLETED k` read, also for a
  `stream.read r 0`; `host3` answers `COMPLETED 0` there. `fsReadTh3w F` allows `COMPLETED 0`
  for a zero-length read.
* **Clock overflow.** `clockStep3` owes `now ≥ l + d` after `now = l` and `wait-for d`, also
  when `l + d ≥ 2^64`; no `u64` answer satisfies that. `clockTh3s` saturates the bound at
  `2^64 - 1`.

## The 0.2 side

The guarantees for stdout, clocks and typing hold over **every** 0.2 host (the component checks
what it relies on). The read theory needs the file contents on the 0.2 side: `fsRead2 F`, a loose
theory of `wasi:filesystem` `read-via-stream` (vendored WIT 0.2.9, `filesystem/types.wit`) and
`wasi:io` `read`/`blocking-read`: the input stream of `read-via-stream(d, off)` delivers
consecutive bytes of `(F d).drop off`, and reports an error only at the end (no I/O errors). It
is the 0.2 counterpart of `P3.fsReadTh3 F`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (CopyResult)
open Silmaril.Wasi.Versions.P3

/-! ## Clocks, saturated -/

/-- One step of the saturated clock theory: as `clockStep3`, with the bound owed by `wait-for`
capped at `2^64 - 1`. -/
def clockStep3s (q : ClockSt) : WEv → Option ClockSt
  | .imp f a r =>
    if f = now3 then
      match r with
      | some [.u64 x] =>
        if q.last.all (fun l => decide (l ≤ x)) ∧ q.lb ≤ x.toNat then some { last := some x, lb := 0 }
        else none
      | _ => none
    else if f = waitFor3 then
      match a, q.last with
      | [.u64 d], some l => some { q with lb := max q.lb (min (l.toNat + d.toNat) u64Max) }
      | _, _ => some q
    else some q
  | _ => some q

/-- **The saturated clock theory of WASI 0.3.** -/
def clockTh3s : Protocol ClockSt WEv := ⟨{}, clockStep3s⟩

/-! ## Stdout, for well-shaped calls -/

/-- The calls `outStep` constrains have the argument lists it expects. -/
def outShaped : WEv → Bool
  | .imp f a _ =>
    if f = stdoutWrite3 then a.length == 1
    else if f = cStreamWrite then a.length == 2
    else true
  | _ => true

/-- **The loose stdout theory, for well-shaped calls.** -/
def stdoutTh3w : Protocol OutSt WEv := ⟨{}, fun q e => if outShaped e then outStep q e else some q⟩

/-! ## `read-via-stream`, for well-shaped calls and with zero-length reads -/

/-- The calls `rdStep` constrains have the argument lists it expects. -/
def rdShaped : WEv → Bool
  | .imp f a _ =>
    if f = readVia3 then (match a with | [.u32 _, .u64 _] => true | _ => false)
    else if f = cStreamRead then (match a with | [_, nv] => (natOf nv).isSome | _ => true)
    else true
  | _ => true

/-- One step of the read theory as `rdStep`, except that a read of `n = 0` items may complete
with `0`. -/
def rdStepZ (F : BitVec 32 → List (BitVec 8)) (q : RdSt) : WEv → Option RdSt
  | .imp f a r =>
    if f = readVia3 then
      match a, r with
      | [.u32 d, .u64 off], some [.record [rv, _]] =>
        match natOf rv with
        | some r' => some (setRest q r' ((F d).drop off.toNat))
        | none => none
      | _, _ => none
    else if f = cStreamRead then
      match a, r with
      | [rv, nv], some [pv, items] =>
        match natOf rv >>= rest q, natOf nv, natOf pv >>= copyOf with
        | some bs, some n, some (some (.completed, k)) =>
          if (0 < k ∨ n = 0) ∧ k ≤ n ∧ bytesOf items = bs.take k then
            (natOf rv).map fun r' => setRest q r' (bs.drop k)
          else none
        | some bs, some _, some (some (.dropped, 0)) => if bs = [] then some q else none
        | some _, some _, some none => some q
        | none, _, _ => some q
        | _, _, _ => none
      | _, _ => some q
    else some q
  | _ => some q

/-- **The loose read theory of WASI 0.3, for well-shaped calls and with zero-length reads.** -/
def fsReadTh3w (F : BitVec 32 → List (BitVec 8)) : Protocol RdSt WEv :=
  ⟨[], fun q e => if rdShaped e then rdStepZ F q e else some q⟩

/-! ## The 0.2 file contents -/

/-- One step of the 0.2 read theory over the contents `F`: the state maps an input stream (by
its handle) to the bytes it has still to deliver. -/
def rd2Step (F : BitVec 32 → List (BitVec 8)) (q : RdSt) : WEv → Option RdSt
  | .imp f a r =>
    if f = P2.fdReadStream then
      match a, r with
      | [.u32 d, .u64 off], some [.variant 0 (some (.u32 is))] =>
        some (setRest q is.toNat ((F d).drop off.toNat))
      | _, _ => some q
    else if f = P2.isBread ∨ f = P2.isRead then
      match a with
      | .u32 is :: _ =>
        match rest q is.toNat, r with
        | some bs, some [.variant 0 (some v)] =>
          if bytesOf v = bs.take (bytesOf v).length then
            some (setRest q is.toNat (bs.drop (bytesOf v).length))
          else none
        | some bs, some [.variant 1 _] => if bs = [] then some q else none
        | _, _ => some q
      | _ => some q
    else some q
  | _ => some q

/-- **The loose 0.2 read theory over the file contents `F`.** -/
def fsRead2 (F : BitVec 32 → List (BitVec 8)) : Protocol RdSt WEv := ⟨[], rd2Step F⟩

end Silmaril.Wasi.Versions.P3OverP2

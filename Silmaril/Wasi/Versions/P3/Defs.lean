module

public import Silmaril.Wasi.Comp.Defs
public import Silmaril.Wasi.Theory.Defs
public import Silmaril.Wasi.Os.Defs
public import Silmaril.Wasm.Component.Async.Defs
public import Silmaril.Wasi.Versions.WitImport.Pick.Defs
public import Silmaril.Wasi.Versions.WitImport.RSlices.Defs

@[expose] public section

/-!
# WASI 0.3 as a theory of the WASI institution: stdio streams, clocks, `read-via-stream`

WASI 0.3 (WIT packages `wasi:*@0.3.2`, vendored in `vendor/wasi/0.3.2` at WASI tag `v0.3.2`,
commit `bdadbbb8`) uses the native asynchrony of the Component Model: `async` functions,
`stream<T>`, `future<T>`. This module states a slice of it in the institution of
`Silmaril.Wasi.World`: a world (a signature), theories (axioms on the host's answers) with loose and
concrete host models, an example component, and the OS image of its runs. See
`docs/projects/wasm-wasi.md`.

## How streams and futures are observed

The stream and future *ends* are handles of the Component Model's async built-ins
(`Silmaril.Wasm.Component.Async`). A component reaches them through `canon` built-ins, which are
provided by the runtime, below the component, like its imports. They are therefore **imports of
the world**, in the pseudo-interface `$root` (the core-level module name of `canon` built-ins):
`stream.new`, `stream.write`, `stream.read`, `stream.drop-readable`, `stream.drop-writable`,
`future.read`, `future.drop-readable`, `waitable-set.new`, `waitable.join`,
`waitable-set.wait`. All are for `stream<u8>` and `future<result<_, error-code>>`. The host of
a WASI 0.3 world is thus the runtime together with the WASI implementation; a theory constrains
both, and the reading end of a stream given to `write-via-stream` is the host's.

**Async functions are observed sync-lowered.** `wait-for` and `open-at` are `async func`s. A
component that lowers them without `async` sees one blocking call whose answer is the callee's
`task.return` values; `Silmaril.Wasm.Component.Async.syncRun_result` proves this for every
interleaving. Their events here are those of the sync-lowered call.

## Functions (checked against `vendor/wasi/0.3.2`)

| Lean | WIT |
| --- | --- |
| `stdoutWrite3` | `wasi:cli/stdout@0.3.2` `write-via-stream: func(data: stream<u8>) -> future<result<_, error-code>>` (`cli/stdio.wit`) |
| `stdinRead3` | `wasi:cli/stdin@0.3.2` `read-via-stream: func() -> tuple<stream<u8>, future<result<_, error-code>>>` |
| `now3` | `wasi:clocks/monotonic-clock@0.3.2` `now: func() -> mark` (`mark = u64`) |
| `waitFor3` | `wasi:clocks/monotonic-clock@0.3.2` `wait-for: async func(how-long: duration)` (`duration = u64`) |
| `getDirs3` | `wasi:filesystem/preopens@0.3.2` `get-directories: func() -> list<tuple<descriptor, string>>` |
| `openAt3` | `wasi:filesystem/types@0.3.2` `[method]descriptor.open-at: async func(path-flags, path: string, open-flags, flags) -> result<descriptor, error-code>`; the slice keeps `self` and `path` |
| `readVia3` | `wasi:filesystem/types@0.3.2` `[method]descriptor.read-via-stream: func(offset: filesize) -> tuple<stream<u8>, future<result<_, error-code>>>` |
| `run3` | `wasi:cli/run@0.3.2` `run: async func() -> result` (an export) |

## Encodings (as in `Silmaril.Wasi.Theory`, handles are `u32`)

* `stream.new() -> [r, w]`; `stream.write(w, bytes) -> [packed]`; `stream.read(r, n) ->
  [packed, bytes]`; `packed` is `BLOCKED` or `result | count << 4` (`Async.packCopy`).
* `future.read(f) -> [packed, value]` (`value`: `ok` or `error(code)`) or `[BLOCKED]`.
* `waitable-set.wait(s) -> [code, index, payload]`.

## Theories

* `typed3`: the answers have their WIT types. `ok3` is **defined from the resolved WIT
  import** (`WitImport.p3P`): for the five functions of `WitImport.p3E` (`write-via-stream`,
  both `read-via-stream`s, `now`, `wait-for`) it looks the interface and signature up in the
  imported table and runs the resolved check `WitImport.resOkR`; the canonical built-ins (not WIT
  functions), `open-at` and `get-directories` (whose hand-written checks are not the WIT
  typing: `openAt3_not_witR`, `getDirs3_not_witR`) use the hand-written `ok3H`. The
  hand-written `ok3H` and `typed3H` stay as related variants; `P3.ok3_eq_hand` and
  `P3.typed3_eq_hand` (in `Silmaril.Wasi.Versions.P3.Wit`) prove them equal.
* `clockTh3`: `now` is monotonic, and after `wait-for(d)` returns, the next `now` is at least the
  instant before the wait plus `d`.
* `stdoutTh3` (loose): a `stream.write` reports `BLOCKED`, `DROPPED 0`, or `COMPLETED k` with
  `k ≤ |bytes|`; the future of `write-via-stream` reports `ok` only after the writable end of
  its stream has been dropped (all data handed over).
* `fsReadTh3 F` (loose in the contents `F`): reads on the stream of `read-via-stream(d, off)`
  deliver consecutive bytes of `(F d).drop off`, at most the requested count; at the end the
  stream reports `DROPPED 0` (closed).

## Concrete hosts

`stdout3Impl` (fresh handles; every write completes in full; the future reports `ok`),
`clock3Impl` (a tick clock where `wait-for d` advances the clock by `d`), and `fsRead3Impl F`
(every read delivers the next `min n remaining` bytes of the file).

## OS image

`osTrace3 ch`: the bytes a stdout stream accepted (immediately, or later through a
`stream-write` event of `waitable-set.wait`), as LPS write events on channel `ch`, as
`Silmaril.Wasi.Os.osTrace` does for WASI 0.2's `blocking-write-and-flush`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P3

open Silmaril.Games
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult blocked)

/-! ## Function names -/

/-- `wasi:cli/stdout@0.3.2.write-via-stream`. -/
def stdoutWrite3 : FnName := ⟨"wasi:cli/stdout@0.3.2", "write-via-stream"⟩
/-- `wasi:cli/stdin@0.3.2.read-via-stream`. -/
def stdinRead3 : FnName := ⟨"wasi:cli/stdin@0.3.2", "read-via-stream"⟩
/-- `wasi:clocks/monotonic-clock@0.3.2.now`. -/
def now3 : FnName := ⟨"wasi:clocks/monotonic-clock@0.3.2", "now"⟩
/-- `wasi:clocks/monotonic-clock@0.3.2.wait-for` (async, sync-lowered). -/
def waitFor3 : FnName := ⟨"wasi:clocks/monotonic-clock@0.3.2", "wait-for"⟩
/-- `wasi:filesystem/preopens@0.3.2.get-directories`. -/
def getDirs3 : FnName := ⟨"wasi:filesystem/preopens@0.3.2", "get-directories"⟩
/-- `wasi:filesystem/types@0.3.2.[method]descriptor.open-at` (async, sync-lowered). -/
def openAt3 : FnName := ⟨"wasi:filesystem/types@0.3.2", "[method]descriptor.open-at"⟩
/-- `wasi:filesystem/types@0.3.2.[method]descriptor.read-via-stream`. -/
def readVia3 : FnName := ⟨"wasi:filesystem/types@0.3.2", "[method]descriptor.read-via-stream"⟩
/-- `wasi:cli/run@0.3.2.run`. -/
def run3 : FnName := ⟨"wasi:cli/run@0.3.2", "run"⟩

/-- A `canon` built-in, imported from `$root`. -/
def canon (fn : String) : FnName := ⟨"$root", fn⟩
/-- `stream.new`. -/
def cStreamNew : FnName := canon "stream.new"
/-- `stream.write`. -/
def cStreamWrite : FnName := canon "stream.write"
/-- `stream.read`. -/
def cStreamRead : FnName := canon "stream.read"
/-- `stream.drop-readable`. -/
def cStreamDropR : FnName := canon "stream.drop-readable"
/-- `stream.drop-writable`. -/
def cStreamDropW : FnName := canon "stream.drop-writable"
/-- `future.read`. -/
def cFutureRead : FnName := canon "future.read"
/-- `future.drop-readable`. -/
def cFutureDropR : FnName := canon "future.drop-readable"
/-- `waitable-set.new`. -/
def cWsNew : FnName := canon "waitable-set.new"
/-- `waitable.join`. -/
def cJoin : FnName := canon "waitable.join"
/-- `waitable-set.wait`. -/
def cWait : FnName := canon "waitable-set.wait"

/-- The `canon` built-ins of the slice. -/
def canonFns : Set FnName :=
  {cStreamNew, cStreamWrite, cStreamRead, cStreamDropR, cStreamDropW, cFutureRead, cFutureDropR,
   cWsNew, cJoin, cWait}

/-- The WASI imports of the slice, **read from the vendored WIT** (`Silmaril.Wasi.Versions.WitImport`). Proofs that need
the members rewrite with `wasiFns3_eq`. -/
def wasiFns3 : Set FnName := {f | f ∈ WitImport.pick (WitImport.names WitImport.p3T) WitImport.keys3}

/-- **The imported functions of `wasiFns3` are the hand-written ones** (kernel-checked on the
imported table). -/
theorem wasiFns3_eq : wasiFns3 = {stdoutWrite3, stdinRead3, now3, waitFor3, getDirs3, openAt3, readVia3} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.p3T) WitImport.keys3 ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.p3T) WitImport.keys3).Perm [stdoutWrite3, stdinRead3, now3, waitFor3, getDirs3, openAt3, readVia3] by decide +kernel).mem_iff]
  simp

/-- The async WASI functions of the slice (observed sync-lowered): those the WIT marks `async`, **read from the vendored WIT** (`Silmaril.Wasi.Versions.WitImport`). Proofs that need
the members rewrite with `asyncFns3_eq`. -/
def asyncFns3 : Set FnName := {f | f ∈ WitImport.async3L}

/-- **The imported functions of `asyncFns3` are the hand-written ones** (kernel-checked on the
imported table). -/
theorem asyncFns3_eq : asyncFns3 = {waitFor3, openAt3} := by
  ext f
  show f ∈ WitImport.async3L ↔ _
  rw [(show (WitImport.async3L).Perm [waitFor3, openAt3] by decide +kernel).mem_iff]
  simp

/-- **The WASI 0.3 command slice.** -/
def p3World : World := ⟨wasiFns3 ∪ canonFns, {run3}⟩

/-! ## Answers -/

/-- A `u32` answer of a natural number. -/
def natV (n : Nat) : Val := .u32 (BitVec.ofNat 32 n)

/-- The numeric value of a `u32`. -/
def natOf : Val → Option Nat
  | .u32 x => some x.toNat
  | _ => none

/-- A packed copy result: `BLOCKED`, or `result | count << 4` with `result ∈ {0, 1, 2}`. -/
def copyOf (n : Nat) : Option (Option (CopyResult × Nat)) :=
  if n = blocked then some none
  else if n % 16 = 0 then some (some (.completed, n / 16))
  else if n % 16 = 1 then some (some (.dropped, n / 16))
  else if n % 16 = 2 then some (some (.cancelled, n / 16))
  else none

/-! ## Typing -/

/-- `result<_, error-code>`. -/
def resultOk : Val → Bool
  | .variant 0 none => true
  | .variant 1 (some (.variant _ none)) => true
  | _ => false

/-- The answers of the slice are well typed, as written by hand (`ok3_eq_hand`: equal to
`ok3`). -/
def ok3H : WEv → Bool
  | .imp f _ r =>
    if f = cStreamNew then (match r with | some [.u32 _, .u32 _] => true | _ => false)
    else if f = cStreamWrite then (match r with | some [.u32 _] => true | _ => false)
    else if f = cStreamRead then (match r with | some [.u32 _, .record _] => true | _ => false)
    else if f = cStreamDropR ∨ f = cStreamDropW ∨ f = cFutureDropR ∨ f = cJoin then
      (match r with | some [] => true | _ => false)
    else if f = cFutureRead then
      (match r with | some [.u32 _] => true | some [.u32 _, v] => resultOk v | _ => false)
    else if f = cWsNew then (match r with | some [.u32 _] => true | _ => false)
    else if f = cWait then (match r with | some [.u32 _, .u32 _, .u32 _] => true | _ => false)
    else if f = stdoutWrite3 then (match r with | some [.u32 _] => true | _ => false)
    else if f = stdinRead3 ∨ f = readVia3 then
      (match r with | some [.record [.u32 _, .u32 _]] => true | _ => false)
    else if f = now3 then (match r with | some [.u64 _] => true | _ => false)
    else if f = waitFor3 then (match r with | some [] => true | _ => false)
    else if f = getDirs3 then (match r with | some [.record ds] => ds.all preopenOk | _ => false)
    else if f = openAt3 then
      (match r with | some [.variant 0 (some (.u32 _))] => true
                    | some [.variant 1 (some _)] => true | _ => false)
    else true
  | _ => true

end Silmaril.Wasi.Versions.P3

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi.Versions.P3

/-- The slice functions whose hand-written check is exactly the resolved WIT result check
(`ok3H_eqR`; moved here from `WitImport.RP3`). -/
def p3E : List FnName := [stdoutWrite3, stdinRead3, now3, waitFor3, readVia3]

end Silmaril.Wasi.Versions.WitImport

namespace Silmaril.Wasi.Versions.P3

open Silmaril.Games
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult blocked)

/-- **The answers of the slice are well typed, from the WIT import.** For the functions of
`WitImport.p3E` the interface and signature are looked up in the resolved imported table
`WitImport.p3P` and the answer is checked with the resolved WIT typing `WitImport.resOkR`; the
other functions use the hand-written `ok3H`. `ok3_eq_hand`: this is `ok3H`. -/
def ok3 : WEv → Bool
  | .imp f a r =>
    match (WitImport.rrestrict WitImport.p3P WitImport.p3E).1.lookup f with
    | some (i, s) => WitImport.resOkR WitImport.p3P.2 i s r
    | none => ok3H (.imp f a r)
  | e => ok3H e

/-- **The typing theory of the WASI 0.3 slice.** -/
def typed3 : Protocol Unit WEv := pointwise ok3

/-- The typing theory with the hand-written `ok3H` (`typed3_eq_hand`: equal to `typed3`). -/
def typed3H : Protocol Unit WEv := pointwise ok3H

/-! ## Clocks -/

/-- The clock state: the last instant answered, and the lower bound owed by a finished
`wait-for`. -/
structure ClockSt where
  last : Option (BitVec 64) := none
  lb : Nat := 0

/-- One step of the clock theory. -/
def clockStep3 (q : ClockSt) : WEv → Option ClockSt
  | .imp f a r =>
    if f = now3 then
      match r with
      | some [.u64 x] =>
        if q.last.all (fun l => decide (l ≤ x)) ∧ q.lb ≤ x.toNat then some { last := some x, lb := 0 }
        else none
      | _ => none
    else if f = waitFor3 then
      match a, q.last with
      | [.u64 d], some l => some { q with lb := max q.lb (l.toNat + d.toNat) }
      | _, _ => some q
    else some q
  | _ => some q

/-- **The clock theory of WASI 0.3**: `now` is monotonic, and `wait-for d` makes the next `now`
at least the last instant plus `d`. -/
def clockTh3 : Protocol ClockSt WEv := ⟨{}, clockStep3⟩

/-! ## The stdout theory -/

/-- The stdout state: the stream pairs created (`r, w`), the stdout futures (`f`, the writable
end of its stream) and the dropped writable ends. -/
structure OutSt where
  pairs : List (Nat × Nat) := []
  futs : List (Nat × Nat) := []
  dropped : List Nat := []

/-- The writable end of the readable end `r`. -/
def OutSt.wOf (q : OutSt) (r : Nat) : Option Nat := (q.pairs.find? (·.1 = r)).map (·.2)

/-- A copy answer is allowed for a write of `len` items. -/
def copyOk (len : Nat) : Option (CopyResult × Nat) → Bool
  | none => true
  | some (.completed, k) => decide (k ≤ len)
  | some (.dropped, k) => decide (k = 0)
  | some (.cancelled, _) => false

/-- One step of the stdout theory. -/
def outStep (q : OutSt) : WEv → Option OutSt
  | .imp f a r =>
    if f = cStreamNew then
      match r with
      | some [rv, wv] =>
        match natOf rv, natOf wv with
        | some r', some w' => some { q with pairs := (r', w') :: q.pairs }
        | _, _ => none
      | _ => none
    else if f = stdoutWrite3 then
      match a, r with
      | [rv], some [fv] =>
        match natOf rv >>= q.wOf, natOf fv with
        | some w', some f' => some { q with futs := (f', w') :: q.futs }
        | _, some _ => some q
        | _, _ => none
      | _, _ => none
    else if f = cStreamWrite then
      match a, r with
      | [_, buf], some [pv] =>
        match natOf pv >>= copyOf with
        | some c => if copyOk (bytesOf buf).length c then some q else none
        | none => none
      | _, _ => none
    else if f = cStreamDropW then
      match a with
      | [wv] => some { q with dropped := ((natOf wv).toList) ++ q.dropped }
      | _ => some q
    else if f = cFutureRead then
      match a, r with
      | [fv], some [_, .variant 0 none] =>
        match natOf fv >>= fun f' => (q.futs.find? (·.1 = f')).map (·.2) with
        | some w' => if w' ∈ q.dropped then some q else none
        | none => some q
      | _, _ => some q
    else some q
  | _ => some q

/-- **The loose stdout theory of WASI 0.3.** -/
def stdoutTh3 : Protocol OutSt WEv := ⟨{}, outStep⟩

/-! ## The filesystem `read-via-stream` theory -/

/-- The read state: for each readable end of a `read-via-stream`, the bytes still to deliver. -/
abbrev RdSt : Type := List (Nat × List (BitVec 8))

/-- The bytes still to deliver on `r`. -/
def rest (q : RdSt) (r : Nat) : Option (List (BitVec 8)) := (q.find? (·.1 = r)).map (·.2)

/-- Replace the rest of `r`. -/
def setRest (q : RdSt) (r : Nat) (bs : List (BitVec 8)) : RdSt := (r, bs) :: q

/-- One step of the read theory over the file contents `F`. -/
def rdStep (F : BitVec 32 → List (BitVec 8)) (q : RdSt) : WEv → Option RdSt
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
          if 0 < k ∧ k ≤ n ∧ bytesOf items = bs.take k then
            (natOf rv).map fun r' => setRest q r' (bs.drop k)
          else none
        | some bs, some _, some (some (.dropped, 0)) => if bs = [] then some q else none
        | some _, some _, some none => some q
        | none, _, _ => some q
        | _, _, _ => none
      | _, _ => some q
    else some q
  | _ => some q

/-- **The loose read theory of WASI 0.3** over the contents `F` of the descriptors. -/
def fsReadTh3 (F : BitVec 32 → List (BitVec 8)) : Protocol RdSt WEv := ⟨[], rdStep F⟩

/-! ## Concrete hosts -/

/-- **The concrete stdout host**: fresh handles, every write completes in full, the future
reports `ok` (completed). -/
def stdout3Impl : Impl := fun p f a =>
  if f = cStreamNew then some [natV (2 * p.length + 1), natV (2 * p.length + 2)]
  else if f = stdoutWrite3 then some [natV (2 * p.length + 1)]
  else if f = cStreamWrite then
    some [natV (packCopy .completed (bytesOf (a.getD 1 (.record []))).length)]
  else if f = cStreamDropW then some []
  else if f = cFutureRead then some [natV CopyResult.completed.toNat, okV none]
  else none

/-- The instants and waits so far: the clock value after the answers `p`. -/
def clockVal : List WEv → Nat
  | [] => 0
  | .imp f [.u64 d] _ :: p => (if f = waitFor3 then d.toNat else 0) + clockVal p
  | .imp f _ _ :: p => (if f = now3 then 1 else 0) + clockVal p
  | _ :: p => clockVal p

/-- **The concrete clock host**: `now` ticks, `wait-for d` advances the clock by `d`. -/
def clock3Impl : Impl := fun p f _ =>
  if f = now3 then some [.u64 (BitVec.ofNat 64 (min (clockVal p) u64Max))]
  else if f = waitFor3 then some []
  else none

/-- The descriptor and offset of the readable end `r`, from a `read-via-stream` answer. -/
def srcOf (r : Nat) : List WEv → Option (BitVec 32 × Nat)
  | [] => none
  | .imp f [.u32 d, .u64 off] (some [.record [rv, _]]) :: p =>
    if f = readVia3 ∧ natOf rv = some r then some (d, off.toNat) else srcOf r p
  | _ :: p => srcOf r p

/-- The number of bytes delivered on `r` so far. -/
def deliveredOn (r : Nat) : List WEv → Nat
  | [] => 0
  | .imp f (rv :: _) (some [_, items]) :: p =>
    (if f = cStreamRead ∧ natOf rv = some r then (bytesOf items).length else 0) + deliveredOn r p
  | _ :: p => deliveredOn r p

/-- The bytes still to deliver on the readable end `r` after the answers `p`: the file rest of
its `read-via-stream`, minus what was delivered (none for a stream not from `read-via-stream`). -/
def remaining (F : BitVec 32 → List (BitVec 8)) (p : List WEv) (r : Nat) : List (BitVec 8) :=
  match srcOf r p with
  | some (d, off) => ((F d).drop off).drop (deliveredOn r p)
  | none => []

/-- The handle and count of a `stream.read` call. -/
def readArgs (a : List Val) : Nat × Nat :=
  match a with
  | [rv, nv] => ((natOf rv).getD 0, (natOf nv).getD 0)
  | _ => (0, 0)

/-- The items a `stream.read` delivers: the next `n` remaining bytes. -/
def readItems (F : BitVec 32 → List (BitVec 8)) (p : List WEv) (a : List Val) : List (BitVec 8) :=
  (remaining F p (readArgs a).1).take (readArgs a).2

/-- The packed result of a `stream.read`: `COMPLETED k`, or `DROPPED 0` at the end. -/
def readCode (F : BitVec 32 → List (BitVec 8)) (p : List WEv) (a : List Val) : Nat :=
  if remaining F p (readArgs a).1 = [] then packCopy .dropped 0
  else packCopy .completed (readItems F p a).length

/-- **The concrete read host over the contents `F`**: `read-via-stream` gives a fresh stream and
future; each `stream.read r n` delivers the next `min n remaining` bytes, and `DROPPED 0` at the
end (also for a stream it does not know). -/
def fsRead3Impl (F : BitVec 32 → List (BitVec 8)) : Impl := fun p f a =>
  if f = readVia3 then some [.record [natV (2 * p.length + 1), natV (2 * p.length + 2)]]
  else if f = cStreamRead then some [natV (readCode F p a), bytesV (readItems F p a)]
  else none

/-- **The concrete WASI 0.3 host of the slice** over the file contents `F`: reads as
`fsRead3Impl F`, clocks as `clock3Impl`, stdout as `stdout3Impl`; a fixed preopen `/`, fresh
descriptors from `open-at`, an empty stdin, and waitable sets that are never ready (this host
never blocks). -/
def host3 (F : BitVec 32 → List (BitVec 8)) : Impl := fun p f a =>
  if f = readVia3 ∨ f = cStreamRead then fsRead3Impl F p f a
  else if f = now3 ∨ f = waitFor3 then clock3Impl p f a
  else if f = cStreamDropR ∨ f = cFutureDropR ∨ f = cJoin then some []
  else if f = cWsNew then some [natV (2 * p.length + 1)]
  else if f = cWait then some [natV 0, natV 0, natV 0]
  else if f = stdinRead3 then some [.record [natV (2 * p.length + 1), natV (2 * p.length + 2)]]
  else if f = getDirs3 then some [.record [.record [.u32 0, strV "/"]]]
  else if f = openAt3 then some [okV (some (natV (2 * p.length + 1)))]
  else stdout3Impl p f a

/-! ## The OS image -/

/-- The OS image state: stdout writable ends, and the pending write of a writable end. -/
structure OsSt where
  outW : List Nat := []
  pairs : List (Nat × Nat) := []
  pend : List (Nat × List (BitVec 8)) := []

/-- One step of the OS image on channel `ch`. -/
def osStep3 (ch : Silmaril.Process.LPS.Word) (q : OsSt) :
    WEv → OsSt × List Silmaril.Process.LPS.Event
  | .imp f a r =>
    if f = cStreamNew then
      match r with
      | some [rv, wv] =>
        match natOf rv, natOf wv with
        | some r', some w' => ({ q with pairs := (r', w') :: q.pairs }, [])
        | _, _ => (q, [])
      | _ => (q, [])
    else if f = stdoutWrite3 then
      match a with
      | [rv] =>
        match natOf rv >>= fun r' => (q.pairs.find? (·.1 = r')).map (·.2) with
        | some w' => ({ q with outW := w' :: q.outW }, [])
        | none => (q, [])
      | _ => (q, [])
    else if f = cStreamWrite then
      match a, r with
      | [wv, buf], some [pv] =>
        match natOf wv, natOf pv >>= copyOf with
        | some w', some (some (.completed, k)) =>
          if w' ∈ q.outW then (q, ((bytesOf buf).take k).map (.writeEv ch)) else (q, [])
        | some w', some none => ({ q with pend := (w', bytesOf buf) :: q.pend }, [])
        | _, _ => (q, [])
      | _, _ => (q, [])
    else if f = cWait then
      match r with
      | some [cv, iv, pv] =>
        match natOf cv, natOf iv, natOf pv >>= copyOf with
        | some 3, some w', some (some (.completed, k)) =>
          match (q.pend.find? (·.1 = w')).map (·.2) with
          | some bs => if w' ∈ q.outW then (q, (bs.take k).map (.writeEv ch)) else (q, [])
          | none => (q, [])
        | _, _, _ => (q, [])
      | _ => (q, [])
    else (q, [])
  | _ => (q, [])

/-- The OS image from a state. -/
def osRun3 (ch : Silmaril.Process.LPS.Word) : OsSt → List WEv → List Silmaril.Process.LPS.Event
  | _, [] => []
  | q, e :: t => let (q', out) := osStep3 ch q e; out ++ osRun3 ch q' t

/-- **The OS image of a WASI 0.3 event list** on the stdout channel `ch`. -/
def osTrace3 (ch : Silmaril.Process.LPS.Word) (t : List WEv) : List Silmaril.Process.LPS.Event :=
  osRun3 ch {} t

/-! ## An example component -/

/-- A WASI 0.3 import of the slice. -/
abbrev P3Op : Type := (nsig p3World.imports).Op

/-- `stream.new()`. -/
def newOp : P3Op := (⟨cStreamNew, Or.inr (Or.inl rfl)⟩, [])
/-- `write-via-stream(r)`. -/
def wvsOp (r : Val) : P3Op := (⟨stdoutWrite3, Or.inl (by rw [wasiFns3_eq]; exact Or.inl rfl)⟩, [r])
/-- `stream.write(w, "hi")`. -/
def swOp (w : Val) : P3Op :=
  (⟨cStreamWrite, Or.inr (Or.inr (Or.inl rfl))⟩, [w, bytesV Silmaril.Wasi.Examples.hiBytes])
/-- `stream.drop-writable(w)`. -/
def dwOp (w : Val) : P3Op := (⟨cStreamDropW, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩, [w])
/-- `future.read(f)`. -/
def frOp (f : Val) : P3Op := (⟨cFutureRead, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩, [f])

/-- After `future.read`: `ok` when the future reports `ok`. -/
def h3K5 : Option (List Val) → BProg p3World.imports
  | some [_, .variant 0 none] => .pure (some [okV none])
  | _ => .pure (some [errV none])

/-- After the drop. -/
def h3K4 (f : Val) : Option (List Val) → BProg p3World.imports := fun _ => .call (frOp f) h3K5

/-- After the write. -/
def h3K3 (w f : Val) : Option (List Val) → BProg p3World.imports := fun _ => .call (dwOp w) (h3K4 f)

/-- After `write-via-stream`. -/
def h3K2 (w : Val) : Option (List Val) → BProg p3World.imports
  | some [f] => .call (swOp w) (h3K3 w f)
  | _ => .pure (some [errV none])

/-- After `stream.new`. -/
def h3K1 : Option (List Val) → BProg p3World.imports
  | some [r, w] => .call (wvsOp r) (h3K2 w)
  | _ => .pure (some [errV none])

/-- The program of `run`. -/
def hello3Prog : BProg p3World.imports := .call newOp h3K1

/-- **Hello over WASI 0.3**: create a stream, hand its readable end to `write-via-stream`,
write `hi`, drop the writable end, and await the future. -/
def hello3 : Body p3World.imports p3World.exports := fun _ => hello3Prog

/-- The export call `run`. -/
def run3Q : (nsig p3World.exports).Op := (⟨run3, rfl⟩, [])

/-- **One run of `hello3`** against `stdout3Impl`. -/
def hello3Run : List (Move (nsig p3World.imports) (nsig p3World.exports)) :=
  [.inr (.ask run3Q),
   .inl (.ask newOp), .inl (.ans newOp (some [natV 1, natV 2])),
   .inl (.ask (wvsOp (natV 1))), .inl (.ans (wvsOp (natV 1)) (some [natV 3])),
   .inl (.ask (swOp (natV 2))), .inl (.ans (swOp (natV 2)) (some [natV (packCopy .completed 2)])),
   .inl (.ask (dwOp (natV 2))), .inl (.ans (dwOp (natV 2)) (some [])),
   .inl (.ask (frOp (natV 3))), .inl (.ans (frOp (natV 3)) (some [natV 0, okV none])),
   .inr (.ans run3Q (some [okV none]))]

end Silmaril.Wasi.Versions.P3

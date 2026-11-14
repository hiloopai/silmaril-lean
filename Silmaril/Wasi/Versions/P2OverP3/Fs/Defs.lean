module

public import Silmaril.Wasi.Versions.P2OverP3.Comp.Defs
public import Silmaril.Wasi.Versions.P3OverP2.Theory.Defs

@[expose] public section

/-!
# WASI 0.2 over 0.3: the `wasi:filesystem` read slice

`p2OverP3Fs cap` extends the component `p2OverP3 cap` of relation (c)
(`Silmaril.Wasi.Versions.P2OverP3.Comp`) with the WASI 0.2 `wasi:filesystem` functions
`preopens.get-directories`, `descriptor.open-at`, `descriptor.read-via-stream` and
`[resource-drop]descriptor`, implemented over the WASI 0.3 filesystem.

## Worlds (checked against the vendored WIT)

* Exports `expF = exp2 ∪ fsExp`, `fsExp = {getDirs, openAt, fdReadStream, fdDrop}`: WIT
  `v0.2.9`, `filesystem/preopens.wit` (`get-directories: func() -> list<tuple<descriptor,
  string>>`) and `filesystem/types.wit` (`resource descriptor`, L298; `read-via-stream:
  func(offset: filesize) -> result<input-stream, error-code>`, L308; `open-at`).
* Imports `impF = imp3 ∪ {fdDrop3}`: `fdDrop3` is the drop of the WASI 0.3 `resource descriptor`
  (`vendor/wasi/0.3.2/filesystem/types.wit` L311). `get-directories`, the **async** `open-at`
  (L539) and `read-via-stream` (L329, returning `tuple<stream<u8>, future<result<_,
  error-code>>>`) are already in `imp3` (`P3.getDirs3`, `P3.openAt3`, `P3.readVia3`).

## Design

* **Descriptors are the WASI 0.3 descriptors**: `get-directories` and `open-at` forward their
  answers (lifted at the 0.2 type by `dirsFix`/`openFix`), and every descriptor argument is
  passed on unchanged. So the file contents `F d` of a descriptor are the same on both sides.
* **`open-at` is an `async func` in 0.3**; the component lowers it **synchronously**: one
  blocking call whose answer is the callee's `task.return` value
  (`Silmaril.Wasm.Component.Async.syncRun_result`), as `P3` observes async imports.
* **`read-via-stream(d, off)`** calls the 0.3 `read-via-stream(d, off)` and wraps its readable end
  `r` and future in a fresh 0.2 `input-stream` handle (`FEnt`, the table `fs`). A `read` of that
  stream is one `stream.read(r, len)`; a `blocking-read` repeats it, waiting on `r` with
  `waitable.join` + `waitable-set.wait`, at most `rounds` times. `[resource-drop]input-stream`
  drops `r` and the future.
* **Handles the component cannot vouch for are inert.** A file stream whose 0.3 readable end
  also became the end of a newer file stream is marked not `live` (`poison`), as is a dropped or
  ended one; reads of it answer `ok([])`. Calls of the `p2OverP3` code (stdin, stdout, pollables,
  …) never read the end of a live file stream: they run **sanitized** (`san`): a
  `stream.read` of such an end (or a `read-via-stream`) is not made and answered `BLOCKED`.
  Output-stream methods applied to a file-stream handle answer as on an open stream with nothing
  to do (`neutral`), so that they never close it.
* **Input pollables are probed** (this removes the simplification of `p2OverP3`, whose input
  pollables are always ready; `p2OverP3` stays as the eager variant). The pollable of an input
  stream (stdin or file) is ready when a zero-length `stream.read(r, 0)` does not report
  `BLOCKED`: in the reference machine a zero-length read completes at once exactly when the
  writer has a parked buffer or is gone, and otherwise stays pending until the writer arrives
  (`Silmaril.Wasm.Component.Async.RefZero`). `block`/`poll` then wait on the pending probes with
  `waitable-set.wait`, together with the in-flight writes (`pollLoopI`). A probe that is still
  pending when `rounds` runs out is not cancelled (the 0.3 slice has no `stream.cancel-read`), as
  for a `BLOCKED` read of `p2OverP3`. Probes are zero-length, so they never change what the 0.3
  read theory has left; the poll programs run sanitized against any other read (`badZ`).
* `skip`/`blocking-skip` of a file stream skip nothing (`ok(0)`): the 0.2 read theory
  `fsRead2 F` (`Silmaril.Wasi.Versions.P3OverP2.Theory`) does not track skips.

## The theories

* Imports: `T3 F = clockTh3 ⊗ fsReadTh3w F`, the WASI 0.3 clock theory and the loose 0.3 read
  theory (well-shaped calls, zero-length reads allowed) of `P3OverP2.Theory`.
* Exports: `P2 F = p2Th .loose ⊗ fsRead2 F`, the loose WASI 0.2 theory (with the base WASI theory's filesystem
  typing `fsTyped` and the result types `cliOk` of `read-via-stream`) and the loose 0.2 read
  theory: the input stream of `read-via-stream(d, off)` delivers consecutive bytes of
  `(F d).drop off`, and reports an error only at the end.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (CopyResult blocked)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2
open Silmaril.Wasi.Versions.P3OverP2 (fsReadTh3w fsRead2)

/-! ## Worlds -/

/-- `wasi:filesystem/types@0.3.2.[resource-drop]descriptor`. -/
def fdDrop3 : FnName := ⟨"wasi:filesystem/types@0.3.2", "[resource-drop]descriptor"⟩

/-- The imports: `imp3` and the drop of a WASI 0.3 descriptor. -/
def impF : Set FnName := imp3 ∪ {fdDrop3}

/-- The exported WASI 0.2 filesystem functions. -/
def fsExp : Set FnName := {getDirs, openAt, fdReadStream, fdDrop}

/-- The exports: `exp2` and the filesystem functions. -/
def expF : Set FnName := exp2 ∪ fsExp

/-- **The world of the filesystem extension.** -/
def p2OverP3FsWorld : World := ⟨impF, expF⟩

theorem imp3_sub : imp3 ⊆ impF := Set.subset_union_left

/-- A program over the imports `impF`. -/
abbrev PgF (A : Type) : Type := Prog (nsig impF) A

/-- A call of an import of `imp3`. -/
def opF (f : FnName) (h : f ∈ imp3) (a : List Val) : (nsig impF).Op := (⟨f, imp3_sub h⟩, a)

/-! ## Sanitizing and lifting `p2OverP3` programs -/

/-- Lift a program over `imp3` to `impF`, answering the calls `bad` rules out with `fake`
instead of making them. -/
def san {A : Type} (bad : FnName → List Val → Bool) (fake : Option (List Val)) :
    Pg A → PgF A
  | .pure a => .pure a
  | .call m k =>
    if bad m.1.1 m.2 then san bad fake (k fake)
    else .call (⟨m.1.1, imp3_sub m.1.2⟩, m.2) fun n => san bad fake (k n)

/-- The answer given instead of a ruled-out call: a `BLOCKED` copy. -/
def fakeA : Option (List Val) := some [natV blocked, .record []]

/-- The readable end named by the arguments of a `stream.read`. -/
def keyOf (a : List Val) : Option Nat := a.head?.bind natOf

/-! ## State -/

/-- A WASI 0.2 input stream over a WASI 0.3 file stream. -/
structure FEnt where
  /-- The readable end of the 0.3 stream. -/
  r : Val
  /-- The future of the 0.3 `read-via-stream`. -/
  fut : Val
  /-- The component reads the stream (not dropped, ended or superseded). -/
  live : Bool

/-- The file streams, by their 0.2 handle. -/
abbrev FsTab : Type := BitVec 32 → Option FEnt

/-- Point update. -/
def fsUpd (t : FsTab) (h : BitVec 32) (v : Option FEnt) : FsTab := fun x => if x = h then v else t x

/-- The readable end `k` belongs to a live file stream. -/
def Tracked (t : FsTab) (k : Nat) : Prop := ∃ h e, t h = some e ∧ e.live = true ∧ natOf e.r = some k

open Classical in
/-- The calls `p2OverP3` code must not make: `read-via-stream`, and `stream.read` of the end of
a live file stream. -/
noncomputable def badK (t : FsTab) (f : FnName) (a : List Val) : Bool :=
  decide (f = readVia3 ∨ (f = cStreamRead ∧ ∃ k, keyOf a = some k ∧ Tracked t k))

/-- The calls a wait must not make: no reads at all. -/
def badR (f : FnName) (_ : List Val) : Bool := decide (f = readVia3 ∨ f = cStreamRead)

/-- Mark the file streams on the readable end `k` as not live. -/
def poison (t : FsTab) (k : Nat) : FsTab :=
  fun x => (t x).map fun e => if natOf e.r = some k then { e with live := false } else e

/-- The state of the component. -/
structure StF where
  /-- The `wasi:io` state of the answers given so far. -/
  io : IoSt
  /-- The state of the `p2OverP3` part. -/
  impl : ISt
  /-- The file streams. -/
  fs : FsTab

/-- The initial state. -/
def StF.init : StF := ⟨ioInit, {}, fun _ => none⟩

/-- The result of a program: the next `p2OverP3` state, file streams and answer. -/
abbrev RF : Type := ISt × FsTab × Option (List Val)

/-! ## Filesystem functions -/

/-- An `error-code` answer (`access`, case `0`). -/
def errFs : Option (List Val) := some [errV (some (.variant 0 none))]

/-- `get-directories` lifted at its 0.2 type. -/
def dirsFix (r : Option (List Val)) : Option (List Val) :=
  if fsOk (.imp getDirs [] r) then r else some [.record []]

/-- `open-at` lifted at its 0.2 type. -/
def openFix (r : Option (List Val)) : Option (List Val) :=
  if fsOk (.imp openAt [] r) then r else errFs

theorem getDirs3_mem : getDirs3 ∈ imp3 := mem_wasi3 (by simp [wasiFns3_eq])
theorem openAt3_mem : openAt3 ∈ imp3 := mem_wasi3 (by simp [wasiFns3_eq])
theorem readVia3_mem : readVia3 ∈ imp3 := mem_wasi3 (by simp [wasiFns3_eq])
theorem cStreamRead_mem : cStreamRead ∈ imp3 := mem_canon (by simp [canonFns])
theorem cStreamDropR_mem : cStreamDropR ∈ imp3 := mem_canon (by simp [canonFns])
theorem cFutureDropR_mem : cFutureDropR ∈ imp3 := mem_canon (by simp [canonFns])

/-- `get-directories`: forwarded. -/
def getDirsP (s : StF) : PgF RF :=
  .call (opF getDirs3 getDirs3_mem []) fun r => .pure (s.impl, s.fs, dirsFix r)

/-- `open-at(self, path)`: the async 0.3 `open-at`, lowered synchronously. -/
def openAtP (s : StF) (a : List Val) : PgF RF :=
  .call (opF openAt3 openAt3_mem a) fun r => .pure (s.impl, s.fs, openFix r)

/-- `[resource-drop]descriptor`: drop the 0.3 descriptor. -/
def fdDropP (s : StF) (a : List Val) : PgF RF :=
  .call (⟨fdDrop3, Or.inr rfl⟩, a) fun _ => .pure (s.impl, s.fs, some [])

/-- `read-via-stream(d, off)`: a fresh 0.2 input stream over the 0.3 stream. -/
def rvsP (s : StF) (a : List Val) : PgF RF :=
  match a with
  | [.u32 d, .u64 off] =>
    let x := s.impl.fresh
    if s.io.closed x.2 then .pure (s.impl, s.fs, errFs) else
    .call (opF readVia3 readVia3_mem [.u32 d, .u64 off]) fun
      | some [.record [rv, fv]] =>
        match natOf rv with
        | some k => .pure (x.1, fsUpd (poison s.fs k) x.2 (some ⟨rv, fv, true⟩),
            some [okV (some (.u32 x.2))])
        | none => .pure (s.impl, s.fs, errFs)
      | _ => .pure (s.impl, s.fs, errFs)
  | _ => .pure (s.impl, s.fs, errFs)

/-! ## Reading a file stream -/

/-- The result of a `stream.read` answer. -/
def readRes : Option (List Val) → RdRes
  | some [pv, items] =>
    match natOf pv >>= copyOf with
    | some (some (.completed, _)) => .data (bytesOf items)
    | some (some (.dropped, _)) => .eof
    | _ => .blocked
  | _ => .blocked

/-- One `stream.read(r, len)`. -/
def readOnce (r : Val) (len : Nat) : PgF RdRes :=
  .call (opF cStreamRead cStreamRead_mem [r, natV len]) fun n => .pure (readRes n)

/-- Wait for an event of the readable end `r` (no reads). -/
def waitR (st : ISt) (r : Val) : PgF ISt := san badR fakeA (waitOn st [r])

/-- Read until some bytes arrive, the stream ends, or `n` rounds have passed. -/
def readLoopF : Nat → ISt → Val → Nat → PgF (ISt × RdRes)
  | 0, st, _, _ => .pure (st, .blocked)
  | n + 1, st, r, len => (readOnce r len).bind fun x =>
    match x with
    | .eof => .pure (st, .eof)
    | .data bs =>
      if bs.isEmpty && decide (0 < len) then (waitR st r).bind fun st' => readLoopF n st' r len
      else .pure (st, .data bs)
    | .blocked => (waitR st r).bind fun st' => readLoopF n st' r len

/-- The file streams after a read result of the stream `h`: an ended stream is no longer live. -/
def afterRead (t : FsTab) (h : BitVec 32) (e : FEnt) : RdRes → FsTab
  | .eof => fsUpd t h (some { e with live := false })
  | _ => t

/-- `read`/`blocking-read` of the live file stream `h`. -/
def fsReadP (s : StF) (h : BitVec 32) (e : FEnt) (len : Nat) (blocking : Bool) : PgF RF :=
  (if blocking then readLoopF rounds s.impl e.r len
   else (readOnce e.r len).bind fun x => .pure (s.impl, x)).bind fun x =>
    .pure (x.1, afterRead s.fs h e x.2, rdAns false len x.2)

/-- The first argument is a `u32` handle. -/
def u32Head : List Val → Bool
  | .u32 _ :: _ => true
  | _ => false

/-- The answer of a stream method of a file stream other than a read: as on an open stream with
nothing to do. -/
def neutral (s : IoSt) (o : IoOp) (a : List Val) : Option (List Val) :=
  match o with
  | .write | .writeZeroes =>
    if s.permit (selfOf a) < writeLen o a then none
    else if s.closed (selfOf a) then errAns else okUnit
  | .checkWrite | .splice | .bsplice | .skip | .bskip =>
    if s.closed (selfOf a) then errAns else okN 0
  | .read | .bread => if s.closed (selfOf a) then errAns else okBytes []
  | _ => if s.closed (selfOf a) then errAns else okUnit

/-- `[resource-drop]input-stream` of a file stream: drop the 0.3 end and future. -/
def fsDropP (s : StF) (h : BitVec 32) (e : FEnt) : PgF RF :=
  if e.live then
    .call (opF cStreamDropR cStreamDropR_mem [e.r]) fun _ =>
      .call (opF cFutureDropR cFutureDropR_mem [e.fut]) fun _ =>
        .pure (s.impl, fsUpd s.fs h (some { e with live := false }), some [])
  else .pure (s.impl, s.fs, some [])

/-- The methods of the file stream `selfOf a`. -/
def fsStreamP (s : StF) (f : FnName) (a : List Val) (e : FEnt) : PgF RF :=
  let h := selfOf a
  match ioOp f with
  | .read =>
    if !s.io.closed h && e.live && u32Head a then fsReadP s h e (lenOf a) false
    else .pure (s.impl, s.fs, neutral s.io .read a)
  | .bread =>
    if !s.io.closed h && e.live && u32Head a then fsReadP s h e (lenOf a) true
    else .pure (s.impl, s.fs, neutral s.io .bread a)
  | .other => if f = isDrop then fsDropP s h e else .pure (s.impl, s.fs, some [])
  | o => .pure (s.impl, s.fs, neutral s.io o a)

/-- The functions of a file-stream handle routed to `fsStreamP`. -/
def fsMethod (f : FnName) : Bool := (ioOp f).isStream || decide (f = osDrop) || decide (f = isDrop)

/-! ## Pollables of input streams: zero-length probes -/

/-- The readable end behind an input-stream handle: a live file stream's, or an open stdin
stream's. -/
def inEnd (st : ISt) (t : FsTab) (h : BitVec 32) : Option Val :=
  match t h with
  | some e => if e.live then some e.r else none
  | none => (look st.ins h).bind fun i => if i.eof then none else some i.r

/-- **A readiness probe**: a zero-length `stream.read(r, 0)`. It completes at once exactly when
the writer has a parked buffer or is gone (REF case 5 and the drop case,
`Silmaril.Wasm.Component.Async.RefZero`); otherwise it reports `BLOCKED` and stays pending until the
writer arrives (REF case 4). Ready unless `BLOCKED`. -/
def probe (r : Val) : Pg Bool :=
  .call (opStreamRead r 0) fun
    | some [pv, _] => .pure (match natOf pv >>= copyOf with | some none => false | _ => true)
    | _ => .pure true

/-- Whether the pollable `p` is ready now, and the readable ends whose probe is pending. -/
def readyNowI (t : FsTab) (st : ISt) (p : BitVec 32) : Pg (ISt × Bool × List Val) :=
  match look st.polls p with
  | some (.inp h) =>
    match inEnd st t h with
    | some r => (probe r).bind fun b => .pure (st, b, if b then [] else [r])
    | none => .pure (st, true, [])
  | _ => (readyNow st p).bind fun x => .pure (x.1, x.2, [])

/-- The ready indices among the indexed pollables, and the pending probes. -/
def readyListI (t : FsTab) (st : ISt) : List (Nat × BitVec 32) → Pg (ISt × List Nat × List Val)
  | [] => .pure (st, [], [])
  | (i, p) :: ps => (readyNowI t st p).bind fun x => (readyListI t x.1 ps).bind fun y =>
    .pure (y.1, (if x.2.1 then i :: y.2.1 else y.2.1), x.2.2 ++ y.2.2)

/-- Wait until one of the pollables is ready, at most `n` rounds: on the in-flight writable ends
and the pending probes with `waitable-set.wait`, or else on the first deadline. -/
def pollLoopI (t : FsTab) : Nat → ISt → List (BitVec 32) → Pg (ISt × List Nat)
  | 0, st, ps => (readyListI t st (indexed ps)).bind fun x => .pure (x.1, x.2.1)
  | n + 1, st, ps => (readyListI t st (indexed ps)).bind fun x =>
    if !x.2.1.isEmpty then .pure (x.1, x.2.1)
    else match inflightEnds x.1 ps ++ x.2.2, deadlines x.1 ps with
      | w :: ws, _ => (waitOn x.1 (w :: ws)).bind fun st' => pollLoopI t n st' ps
      | [], d :: _ => .call opNow fun r => .call (opWaitFor (d - nowOr d r)) fun _ =>
          pollLoopI t n x.1 ps
      | [], [] => .pure (x.1, x.2.1)

/-- `pollable.ready`, `pollable.block` and `poll`, with probed input pollables. -/
def pollPI (t : FsTab) (s : St) (o : IoOp) (a : List Val) : Pg (ISt × Option (List Val)) :=
  match o with
  | .ready => (readyNowI t s.impl (selfOf a)).bind fun x => .pure (x.1, some [.bool x.2.1])
  | .block => (pollLoopI t rounds s.impl [selfOf a]).bind fun x => .pure (x.1, some [])
  | _ =>
    match a with
    | [.record ps] =>
      if ps.isEmpty then .pure (s.impl, none)
      else (pollLoopI t rounds s.impl (handlesOf ps)).bind fun x =>
        .pure (x.1, some [pollAnsOf ps.length x.2])
    | _ => .pure (s.impl, some [.record []])

/-- The arguments of a zero-length `stream.read`. -/
def zeroRd : List Val → Bool
  | [_, nv] => natOf nv == some 0
  | _ => false

/-- The calls a probing program must not make: `read-via-stream`, and reads that are not
zero-length. -/
def badZ (f : FnName) (a : List Val) : Bool :=
  decide (f = readVia3) || (decide (f = cStreamRead) && !zeroRd a)

/-- The pollable functions. -/
def isPollOp (o : IoOp) : Bool := o == .ready || o == .block || o == .poll

/-- `ready`/`block`/`poll`, sanitized. -/
def pollF (s : StF) (f : FnName) (a : List Val) : PgF RF :=
  (san badZ fakeA (pollPI s.fs ⟨s.io, s.impl⟩ (ioOp f) a)).bind fun x => .pure (x.1, s.fs, x.2)

/-! ## The component -/

/-- A `p2OverP3` export call, sanitized. -/
noncomputable def baseP (cap : Nat) (s : StF) (f : FnName) (a : List Val) : PgF RF :=
  (san (badK s.fs) fakeA (prog cap ⟨s.io, s.impl⟩ f a)).bind fun x => .pure (x.1, s.fs, x.2)

/-- The program of an export call. -/
noncomputable def progF (cap : Nat) (s : StF) (f : FnName) (a : List Val) : PgF RF :=
  if f = getDirs then getDirsP s
  else if f = openAt then openAtP s a
  else if f = fdReadStream then rvsP s a
  else if f = fdDrop then fdDropP s a
  else if isPollOp (ioOp f) then pollF s f a
  else match s.fs (selfOf a) with
    | some e => if fsMethod f then fsStreamP s f a e else baseP cap s f a
    | none => baseP cap s f a

/-- The body: run the program, and record the answer in the 0.2 stream state. -/
noncomputable def bodyF (cap : Nat) : SBody StF impF expF := fun s q =>
  (progF cap s q.1.1 q.2).bind fun x => .pure (⟨ioUpd s.io (ioOp q.1.1) q.2 x.2.2, x.1, x.2.1⟩, x.2.2)

/-- **WASI 0.2 over WASI 0.3 with the `wasi:filesystem` read slice.** -/
noncomputable def p2OverP3Fs (cap : Nat) : Strategy (nsig impF) (nsig expF) :=
  ofSBody (bodyF cap) StF.init

/-! ## The theories -/

/-- **The WASI 0.3 theory used**: the clock theory and the loose read theory over `F`. -/
def t3F (F : BitVec 32 → List (BitVec 8)) : Protocol (ClockSt × RdSt) WEv :=
  clockTh3.prod (fsReadTh3w F)

/-- **The WASI 0.2 theory provided**: the loose 0.2 theory and the loose 0.2 read theory over
`F`. -/
def p2F (F : BitVec 32 → List (BitVec 8)) : Protocol (P2St × RdSt) WEv :=
  (p2Th .loose).prod (fsRead2 F)

end Silmaril.Wasi.Versions.P2OverP3

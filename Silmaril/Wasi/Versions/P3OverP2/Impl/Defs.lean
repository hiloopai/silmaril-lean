module

public import Silmaril.Wasi.Versions.P3OverP2.Theory.Defs
public import Silmaril.Wasi.Versions.Stateful.Defs

@[expose] public section

/-!
# WASI 0.3 over 0.2: the component

`p3OverP2` is a stateful component (`Silmaril.Wasi.Versions.Stateful`) importing the WASI 0.2
command world `P2.p2Command` and exporting the imports of the WASI 0.3 slice `P3.p3World`: the
WASI functions and the `canon` built-ins of streams, futures and waitable sets. Linked over a
0.2 host, it is a 0.3 host (`Silmaril.Wasi.Versions.P3OverP2.Impl.Thms`).

## State

* `Core.st`: a store of the Component Model async model (`Silmaril.Wasm.Component.Async.Store`):
  the 0.3 handle table, the channels of guest streams, waitable sets and their events.
  `stream.new` is `Store.alloc2` (handles `r`, `r + 1`, the channel is `r`), and `stream.write`,
  `stream.read`, the drops, `waitable.join`, `waitable-set.new` and `waitable-set.wait` of guest
  streams and sets are `Silmaril.Wasm.Component.Async.step`.
* `Core.outs`: the streams whose readable end was handed to `write-via-stream`: the 0.2
  `output-stream` (from `get-stdout`) and the future reporting the result.
* `Core.ins`: the readable ends fed by a 0.2 `input-stream` (from `get-stdin` or a
  `read-via-stream` of a descriptor): the stream, whether it is a file, its future and its mode
  (`live`, `eof` after the 0.2 stream reported its end, `dead` after a drop or a failure).
* `Core.pend`: the pending writes on stdout streams (a writable end, its `output-stream`, the
  bytes); `Core.wdrop`: the writable ends dropped; `Core.errF`: futures that report an error.
* `St.clk`: the state of the 0.3 clock theory, which the component maintains itself.

## The functions

* `stream.write` on a stdout stream: `check-write`; on a zero budget **the poll loop**
  (`subscribe`, `poll [p]`, drop `p`, `check-write` again, `rounds` times); then `write` of at
  most the budget and `cap` bytes. A positive count is `COMPLETED k`; a zero count leaves the
  write **pending** and answers `BLOCKED`; an error `DROPPED 0`.
* `waitable-set.wait s`: the event of `Silmaril.Wasm.Component.Async.step` if there is one; otherwise the first pending
  stdout write of a member of `s` is driven by the poll loop and completes with a
  `stream-write` event (code `3`); otherwise the event `none`.
* `stream.drop-writable` of a stdout stream flushes its pending bytes by
  `blocking-write-and-flush`; `future.read` of its future answers after the drop with the result
  of `blocking-flush`, and `BLOCKED` before.
* `stream.read` of a 0.2 input stream: `blocking-read` of at most `min n cap` bytes; bytes give
  `COMPLETED k`, none `BLOCKED`, an error `DROPPED 0` (end of stream, then the future reports
  `ok`). An answer with more bytes than asked marks the stream `dead`.
* `read-via-stream(d, off)` (0.3) is `read-via-stream(d, off)` (0.2); `stdin.read-via-stream`
  is `get-stdin`; the 0.3 stream's writable end is removed from the table (the component feeds
  it).
* `monotonic-clock.now`: 0.2 `now`, raised to the last answer and to the bound owed by
  `wait-for` (**clamped**: the 0.2 theory does not relate the readiness of
  `subscribe-duration` to `now`). `wait-for d` (async, sync-lowered): `subscribe-duration d`,
  `poll [p]`, drop `p`.
* `get-directories`, `open-at`: forwarded; answers that are not well typed become an empty list
  and `error`.

## Simplifications

Items delivered by an `Async` event are not part of the slice's encoding of
`waitable-set.wait` (three `u32`); the 0.2 input streams and pollables of dropped 0.3 ends are not
dropped; handles are allocated only while `next + 4 < 2^32` (otherwise the handle `0`, which the
component never allocates, and every operation on it blocks).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (Store Obj Res packCopy CopyResult blocked)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2 (osCheckWrite osWrite osBwf osBflush osSubscribe pollPoll pollDrop
  isBread fdReadStream monoSubDuration p2Imports p2Command)

/-! ## The 0.2 functions it calls -/

/-- The 0.2 functions the component calls other than reads. -/
def nrFns : Set FnName :=
  {osCheckWrite, osWrite, osBwf, osBflush, osSubscribe, pollPoll, pollDrop, getStdout,
   P2.getStdin, clockNow, monoSubDuration, getDirs, openAt}

/-- The 0.2 functions the component calls are 0.2 imports. -/
theorem nrFns_sub : nrFns ⊆ p2Imports := by
  intro f hf
  simp only [nrFns, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (apply Set.mem_union_left; apply Set.mem_union_left; apply Set.mem_union_left
       simp [P2.ioImports_eq]; done)
    | (apply Set.mem_union_left; apply Set.mem_union_left; apply Set.mem_union_right
       simp [P2.cliImports_eq]; done)
    | (apply Set.mem_union_left; apply Set.mem_union_right; simp [P2.clockImports_eq]; done)
    | (apply Set.mem_union_right; simp [P2.fsImports_eq])

/-- A program over the non-read 0.2 functions. -/
abbrev NProg (A : Type) : Type := Prog (nsig nrFns) A

/-- A program over the 0.2 imports. -/
abbrev IProg (A : Type) : Type := Prog (nsig p2Command.imports) A

/-- Embed a non-read program. -/
def emb {A : Type} : NProg A → IProg A
  | .pure a => .pure a
  | .call m k => .call (⟨m.1.1, nrFns_sub m.1.2⟩, m.2) fun n => emb (k n)

/-- Call a non-read 0.2 function. -/
def nc {A : Type} (f : FnName) (h : f ∈ nrFns) (a : List Val)
    (k : Option (List Val) → NProg A) : NProg A :=
  .call (⟨f, h⟩, a) k

/-- `blocking-read` as a 0.2 import. -/
def breadFn : {f // f ∈ p2Command.imports} :=
  ⟨isBread, by apply Set.mem_union_left; apply Set.mem_union_left; apply Set.mem_union_left; simp [P2.ioImports_eq]⟩

/-- `read-via-stream` (0.2) as a 0.2 import. -/
def rvsFn : {f // f ∈ p2Command.imports} :=
  ⟨fdReadStream, by apply Set.mem_union_right; simp [P2.fsImports_eq]⟩

/-! ## State -/

/-- A stream whose readable end was handed to `write-via-stream`. -/
structure OutB where
  /-- The 0.2 `output-stream`. -/
  os : BitVec 32
  /-- The readable end of the future reporting the result. -/
  fut : Nat

/-- The mode of a readable end fed by a 0.2 input stream. -/
inductive IMode where
  | live | eof | dead
  deriving DecidableEq, Repr

/-- A readable end fed by a 0.2 `input-stream`. -/
structure InB where
  /-- The 0.2 `input-stream`. -/
  is : BitVec 32
  /-- From a `read-via-stream` of a descriptor (not stdin). -/
  file : Bool
  /-- The readable end of its future. -/
  fut : Nat
  mode : IMode

/-- The state of the component apart from the clock. -/
structure Core where
  st : Store := {}
  outs : List (Nat × OutB) := []
  ins : List (Nat × InB) := []
  errF : List Nat := []
  pend : List (Nat × BitVec 32 × List (BitVec 8)) := []
  wdrop : List Nat := []

/-- The state of the component. -/
structure St where
  clk : ClockSt := {}
  core : Core := {}

/-- The binding of the stream channel `ch` to stdout. -/
def Core.outOf (c : Core) (ch : Nat) : Option OutB := (c.outs.find? (·.1 = ch)).map (·.2)

/-- The stdout stream whose future is `f`. -/
def Core.outFut (c : Core) (f : Nat) : Option (Nat × OutB) := c.outs.find? (·.2.fut = f)

/-- The binding of the readable end `r` to a 0.2 input stream. -/
def Core.inOf (c : Core) (r : Nat) : Option InB := (c.ins.find? (·.1 = r)).map (·.2)

/-- The input binding whose future is `f`. -/
def Core.inFut (c : Core) (f : Nat) : Option (Nat × InB) := c.ins.find? (·.2.fut = f)

/-- The pending stdout write of the writable end `w`. -/
def Core.pendOf (c : Core) (w : Nat) : Option (BitVec 32 × List (BitVec 8)) :=
  (c.pend.find? (·.1 = w)).map (·.2)

/-- Four more handles fit below `2^32`. -/
def Core.room (c : Core) : Bool := decide (c.st.next + 4 < 2 ^ 32)

/-- Set the mode of the readable end `r`. -/
def Core.setMode (c : Core) (r : Nat) (m : IMode) : Core :=
  { c with ins := c.ins.map fun e => if e.1 = r then (e.1, { e.2 with mode := m }) else e }

/-- Kill the live bindings of the 0.2 input stream `is` (the host gave the handle again). -/
def killIs (is : BitVec 32) (ins : List (Nat × InB)) : List (Nat × InB) :=
  ins.map fun e => if e.2.is = is then (e.1, { e.2 with mode := .dead }) else e

/-! ## Constants and encodings -/

/-- The most bytes moved by one copy. -/
def cap : Nat := 4096

/-- The poll rounds of `stream.write` before it leaves the write pending. -/
def rounds : Nat := 2

/-- An error value of `result<_, error-code>` (`error-code` case `0`). -/
def err3 : Val := errV (some (.variant 0 none))

/-- A packed copy result accepted for a write of `len` items. -/
def codeOk (len n : Nat) : Bool :=
  decide (n < 2 ^ 32) && match copyOf n with
    | some c => copyOk len c
    | none => false

/-- The code a `stream.write` answers: `n` when admissible, `BLOCKED` otherwise. -/
def wcode (len n : Nat) : Nat := if codeOk len n then n else blocked

/-- The answer of `future.read`. -/
inductive FAns where
  | blocked | ok | err

/-- The encoding of a `future.read` answer. -/
def FAns.enc : FAns → Option (List Val)
  | .blocked => some [natV Silmaril.Wasm.Component.Async.blocked]
  | .ok => some [natV CopyResult.completed.toNat, okV none]
  | .err => some [natV CopyResult.completed.toNat, err3]

/-! ## Arguments -/

/-- A handle argument. -/
def arg1 : List Val → Option Nat
  | [v] => natOf v
  | _ => none

/-- Two handle arguments. -/
def arg2 : List Val → Option (Nat × Nat)
  | [v, u] => match natOf v, natOf u with
    | some x, some y => some (x, y)
    | _, _ => none
  | _ => none

/-- The writable end and the bytes (at most `cap`) of `stream.write`. -/
def swArgs : List Val → Option (Nat × List (BitVec 8))
  | [wv, buf] => (natOf wv).map fun w => (w, (bytesOf buf).take cap)
  | _ => none

/-- The descriptor and offset of `read-via-stream`. -/
def rvArgs : List Val → Option (BitVec 32 × BitVec 64)
  | [.u32 d, .u64 off] => some (d, off)
  | _ => none

/-! ## 0.2 programs -/

/-- `check-write`: `some n` for `ok(n)`, `none` otherwise. -/
def checkW (os : BitVec 32) : NProg (Option Nat) :=
  nc osCheckWrite (by simp [nrFns]) [.u32 os] fun
    | some [.variant 0 (some (.u64 n))] => .pure (some n.toNat)
    | _ => .pure none

/-- Wait on a pollable: `poll [p]`, then drop `p`. -/
def pollOn (p : BitVec 32) : NProg Unit :=
  nc pollPoll (by simp [nrFns]) [.record [.u32 p]] fun _ =>
    nc pollDrop (by simp [nrFns]) [.u32 p] fun _ => .pure ()

/-- Subscribe to the output stream and wait until it is ready. -/
def pollOut (os : BitVec 32) : NProg Unit :=
  nc osSubscribe (by simp [nrFns]) [.u32 os] fun
    | some [.u32 p] => pollOn p
    | _ => .pure ()

/-- **The poll loop**: `check-write`; on a zero budget wait for the stream and ask again. -/
def permit (os : BitVec 32) : Nat → NProg (Option Nat)
  | 0 => checkW os
  | fuel + 1 => (checkW os).bind fun
    | some 0 => (pollOut os).bind fun _ => permit os fuel
    | r => .pure r

/-- Write at most the budget: `some k` bytes written (`0`: none), `none` an error. -/
def writeOut (os : BitVec 32) (xs : List (BitVec 8)) : NProg (Option Nat) :=
  (permit os rounds).bind fun
    | none => .pure none
    | some n =>
      if min n xs.length = 0 then .pure (some 0)
      else nc osWrite (by simp [nrFns]) [.u32 os, bytesV (xs.take (min n xs.length))] fun
        | some [.variant 0 none] => .pure (some (min n xs.length))
        | _ => .pure none

/-! ## The functions -/

/-- `stream.new`. -/
def finNew (c : Core) : Core × Nat × Nat :=
  if c.room then
    let (st', r, w) := c.st.alloc2 .streamR .streamW
    ({ c with st := st' }, r, w)
  else (c, 0, 0)

/-- The readable end handed to `write-via-stream`, when it is a live guest stream. -/
def wvsSrc (c : Core) (a : List Val) : Option Nat :=
  match arg1 a with
  | some r => if r ≠ 0 ∧ c.st.tbl r = some (.streamR r) then some r else none
  | none => none

/-- `write-via-stream`: the 0.2 program (`get-stdout`). -/
def ioWvs (c : Core) (a : List Val) : NProg (Option (BitVec 32)) :=
  match wvsSrc c a with
  | some _ =>
    if c.room then
      nc getStdout (by simp [nrFns]) [] fun
        | some [.u32 os] => .pure (some os)
        | _ => .pure none
    else .pure none
  | none => .pure none

/-- `write-via-stream`: bind the stream to stdout, answer a fresh future. -/
def finWvs (c : Core) (a : List Val) (d : Option (BitVec 32)) : Core × Nat :=
  if c.room then
    let (st', fr, _) := c.st.alloc2 .futureR .futureW
    match wvsSrc c a, d with
    | some r, some os => ({ c with st := st'.remove r, outs := (r, ⟨os, fr⟩) :: c.outs }, fr)
    | _, _ => ({ c with st := st', errF := fr :: c.errF }, fr)
  else (c, 0)

/-- The stdout binding of a writable end. -/
def outW (c : Core) (w : Nat) : Option OutB :=
  match c.st.tbl w with
  | some (.streamW ch) => c.outOf ch
  | _ => none

/-- `stream.write`: the 0.2 program. -/
def ioSw (c : Core) (a : List Val) : NProg (Option Nat) :=
  match swArgs a with
  | some (w, xs) =>
    match outW c w with
    | some ob => if xs = [] then .pure none else writeOut ob.os xs
    | none => .pure none
  | none => .pure none

/-- `stream.write`: the new state and the code. -/
def finSw (c : Core) (a : List Val) (d : Option Nat) : Core × Nat :=
  match swArgs a with
  | some (w, xs) =>
    match outW c w with
    | some ob =>
      if xs = [] then (c, packCopy .completed 0)
      else match d with
        | none => (c, packCopy .dropped 0)
        | some k =>
          if min k xs.length = 0 then ({ c with pend := (w, ob.os, xs) :: c.pend }, blocked)
          else (c, packCopy .completed (min k xs.length))
    | none =>
      match Silmaril.Wasm.Component.Async.step c.st (.streamWrite w (xs.map .u8)) with
      | some (st', .nat code) => ({ c with st := st' }, code)
      | _ => (c, blocked)
  | none => (c, blocked)

/-- `stream.read`: the 0.2 program (`blocking-read` of a live input stream). -/
def ioSr (c : Core) (a : List Val) : IProg (Option (List Val)) :=
  match arg2 a with
  | some (r, n) =>
    match c.inOf r with
    | some ib =>
      if ib.mode = .live then
        .call (breadFn, [.u32 ib.is, .u64 (BitVec.ofNat 64 (min n cap))]) fun ans => .pure ans
      else .pure none
    | none => .pure none
  | none => .pure none

/-- `stream.read`: the new state, the code and the items. -/
def finSr (c : Core) (a : List Val) (d : Option (List Val)) : Core × Nat × List Val :=
  match arg2 a with
  | some (r, n) =>
    if r = 0 then (c, blocked, []) else
    match c.inOf r with
    | some ib =>
      match ib.mode with
      | .eof => (c, packCopy .dropped 0, [])
      | .dead => (c, blocked, [])
      | .live =>
        match d with
        | some [.variant 0 (some v)] =>
          if bytesOf v = [] then (c, blocked, [])
          else if (bytesOf v).length ≤ min n cap then
            (c, packCopy .completed (bytesOf v).length, (bytesOf v).map .u8)
          else (c.setMode r .dead, blocked, [])
        | some [.variant 1 _] => (c.setMode r .eof, packCopy .dropped 0, [])
        | _ => (c, blocked, [])
    | none =>
      match Silmaril.Wasm.Component.Async.step c.st (.streamRead r n) with
      | some (st', .read code xs) => ({ c with st := st' }, code, xs)
      | some (st', .nat code) => ({ c with st := st' }, code, [])
      | _ => (c, blocked, [])
  | none => (c, blocked, [])

/-- `stream.drop-readable`. -/
def finDropR (c : Core) (a : List Val) : Core :=
  match arg1 a with
  | some r =>
    let c' := match Silmaril.Wasm.Component.Async.step c.st (.streamDropR r) with
      | some (st', _) => { c with st := st' }
      | none => c
    match c.inOf r with
    | some _ => c'.setMode r .dead
    | none => c'
  | none => c

/-- `stream.drop-writable`: the 0.2 program (flush a pending stdout write). -/
def ioDropW (c : Core) (a : List Val) : NProg Unit :=
  match arg1 a with
  | some w =>
    match c.pendOf w with
    | some (os, xs) => nc osBwf (by simp [nrFns]) [.u32 os, bytesV xs] fun _ => .pure ()
    | none => .pure ()
  | none => .pure ()

/-- `stream.drop-writable`. -/
def finDropW (c : Core) (a : List Val) : Core :=
  match arg1 a with
  | some w =>
    let c' := { c with pend := c.pend.filter (·.1 ≠ w), wdrop := w :: c.wdrop }
    match Silmaril.Wasm.Component.Async.step c.st (.streamDropW w) with
    | some (st', _) => { c' with st := st' }
    | none => c'
  | none => c

/-- `future.read`: the 0.2 program (`blocking-flush` once the stream is dropped). -/
def ioFr (c : Core) (a : List Val) : NProg (Option (List Val)) :=
  match arg1 a with
  | some f =>
    match c.outFut f with
    | some (ch, ob) =>
      if f ≠ 0 ∧ ch + 1 ∈ c.wdrop then
        nc osBflush (by simp [nrFns]) [.u32 ob.os] fun r => .pure r
      else .pure none
    | none => .pure none
  | none => .pure none

/-- `future.read`. -/
def finFr (c : Core) (a : List Val) (d : Option (List Val)) : FAns :=
  match arg1 a with
  | some f =>
    if f = 0 then .blocked else
    match c.outFut f with
    | some (ch, _) =>
      if ch + 1 ∈ c.wdrop then
        match d with
        | some [.variant 0 none] => .ok
        | _ => .err
      else .blocked
    | none =>
      match c.inFut f with
      | some (_, ib) => if ib.mode = .eof then .ok else .blocked
      | none => if f ∈ c.errF then .err else .blocked
  | none => .blocked

/-- `future.drop-readable`. -/
def finFDropR (c : Core) (a : List Val) : Core :=
  match arg1 a with
  | some f =>
    match Silmaril.Wasm.Component.Async.step c.st (.futureDropR f) with
    | some (st', _) => { c with st := st' }
    | none => c
  | none => c

/-- `waitable-set.new`. -/
def finWsNew (c : Core) : Core × Nat :=
  if c.room then
    match Silmaril.Wasm.Component.Async.step c.st .wsNew with
    | some (st', .nat h) => ({ c with st := st' }, h)
    | _ => (c, 0)
  else (c, 0)

/-- `waitable.join`. -/
def finJoin (c : Core) (a : List Val) : Core :=
  match arg2 a with
  | some (h, s) =>
    match Silmaril.Wasm.Component.Async.step c.st (.join h s) with
    | some (st', _) => { c with st := st' }
    | none => c
  | none => c

/-- The first pending stdout write of a member of the waitable set `s`. -/
def firstPend (c : Core) (s : Nat) : Option (Nat × BitVec 32 × List (BitVec 8)) :=
  c.pend.find? fun e => c.st.joined e.1 = some s

/-- `waitable-set.wait`: the 0.2 program (drive a pending stdout write by the poll loop). -/
def ioWait (c : Core) (a : List Val) : NProg (Option (Option Nat)) :=
  match arg1 a with
  | some s =>
    match Silmaril.Wasm.Component.Async.step c.st (.wait s) with
    | some (_, .event _) => .pure none
    | _ =>
      match firstPend c s with
      | some (_, os, xs) => (writeOut os xs).bind fun r => .pure (some r)
      | none => .pure none
  | none => .pure none

/-- `waitable-set.wait`: the new state and the event (code, index, payload). -/
def finWait (c : Core) (a : List Val) (d : Option (Option Nat)) : Core × Nat × Nat × Nat :=
  match arg1 a with
  | some s =>
    match Silmaril.Wasm.Component.Async.step c.st (.wait s) with
    | some (st', .event e) => ({ c with st := st' }, e.code.toNat, e.index, e.payload)
    | _ =>
      match firstPend c s, d with
      | some (w, _, xs), some (some k) =>
        if min k xs.length = 0 then (c, 0, 0, 0)
        else ({ c with pend := c.pend.filter (·.1 ≠ w) }, 3, w, packCopy .completed (min k xs.length))
      | some (w, _, _), some none => ({ c with pend := c.pend.filter (·.1 ≠ w) }, 3, w, packCopy .dropped 0)
      | _, _ => (c, 0, 0, 0)
  | none => (c, 0, 0, 0)

/-- Allocate a stream fed by the component and its future; bind the readable end to the 0.2
input stream `is` (or a dead binding without one). -/
def finIn (c : Core) (file : Bool) (d : Option (BitVec 32)) : Core × Nat × Nat :=
  if c.room then
    let (st1, r, w) := c.st.alloc2 .streamR .streamW
    let (st2, fr, _) := st1.alloc2 .futureR .futureW
    match d with
    | some is => ({ c with st := st2.remove w, ins := (r, ⟨is, file, fr, .live⟩) :: killIs is c.ins }, r, fr)
    | none => ({ c with st := st2.remove w, ins := (r, ⟨0, file, fr, .dead⟩) :: c.ins,
                        errF := fr :: c.errF }, r, fr)
  else (c, 0, 0)

/-- `stdin.read-via-stream`: the 0.2 program (`get-stdin`). -/
def ioStdin (c : Core) : NProg (Option (BitVec 32)) :=
  if c.room then
    nc P2.getStdin (by simp [nrFns]) [] fun
      | some [.u32 is] => .pure (some is)
      | _ => .pure none
  else .pure none

/-- The input stream of a 0.2 `read-via-stream` answer. -/
def isOf : Option (List Val) → Option (BitVec 32)
  | some [.variant 0 (some (.u32 is))] => some is
  | _ => none

/-- `read-via-stream` (0.3): the 0.2 program (`read-via-stream` of 0.2). -/
def ioRv (c : Core) (a : List Val) : IProg (Option (List Val)) :=
  match rvArgs a with
  | some (d, off) =>
    if c.room then .call (rvsFn, [.u32 d, .u64 off]) fun ans => .pure ans else .pure none
  | none => .pure none

/-- `read-via-stream` (0.3). -/
def finRv (c : Core) (a : List Val) (d : Option (List Val)) : Core × Nat × Nat :=
  match rvArgs a with
  | some _ => finIn c true (isOf d)
  | none => (c, 0, 0)

/-- `monotonic-clock.now`: the 0.2 program. -/
def ioNow : NProg Nat :=
  nc clockNow (by simp [nrFns]) [] fun
    | some [.u64 x] => .pure x.toNat
    | _ => .pure 0

/-- The clamped instant: at least the 0.2 instant, the last answer and the owed bound. -/
def clampNow (k : ClockSt) (x : Nat) : Nat :=
  min u64Max (max x (max (k.last.elim 0 BitVec.toNat) k.lb))

/-- `now`: the new clock state and the answer. -/
def finNow (k : ClockSt) (x : Nat) : ClockSt × BitVec 64 :=
  let v := BitVec.ofNat 64 (clampNow k x)
  ({ last := some v, lb := 0 }, v)

/-- `wait-for`: the 0.2 program (`subscribe-duration`, `poll`, drop). -/
def ioWaitFor (a : List Val) : NProg Unit :=
  match a with
  | [.u64 d] =>
    nc monoSubDuration (by simp [nrFns]) [.u64 d] fun
      | some [.u32 p] => pollOn p
      | _ => .pure ()
  | _ => .pure ()

/-- `wait-for`: the new clock state. -/
def finWaitFor (k : ClockSt) (a : List Val) : ClockSt :=
  match a, k.last with
  | [.u64 d], some l => { k with lb := max k.lb (min (l.toNat + d.toNat) u64Max) }
  | _, _ => k

/-- `get-directories`: forwarded when well typed. -/
def encDirs : Option (List Val) → Option (List Val)
  | some [.record ds] => if ds.all preopenOk then some [.record ds] else some [.record []]
  | _ => some [.record []]

/-- `open-at`: forwarded when well typed. -/
def encOpen : Option (List Val) → Option (List Val)
  | some [.variant 0 (some (.u32 h))] => some [.variant 0 (some (.u32 h))]
  | some [.variant 1 (some e)] => some [.variant 1 (some e)]
  | _ => some [err3]

/-! ## The component -/

/-- The functions of the 0.3 slice. -/
inductive Fn3 where
  | streamNew | streamWrite | streamRead | dropR | dropW | futRead | futDropR | wsNew | join
  | wait | wvs | stdin | now | waitFor | getDirs | openAt | readVia | other
  deriving DecidableEq, Repr

/-- The functions of the slice and their classes. -/
def fnTable : List (Fn3 × FnName) :=
  [(.streamNew, cStreamNew), (.streamWrite, cStreamWrite), (.streamRead, cStreamRead),
   (.dropR, cStreamDropR), (.dropW, cStreamDropW), (.futRead, cFutureRead),
   (.futDropR, cFutureDropR), (.wsNew, cWsNew), (.join, cJoin), (.wait, cWait),
   (.wvs, stdoutWrite3), (.stdin, stdinRead3), (.now, now3), (.waitFor, waitFor3),
   (.getDirs, getDirs3), (.openAt, openAt3), (.readVia, readVia3)]

/-- The class of a function name. -/
def cls (f : FnName) : Fn3 := ((fnTable.find? (·.2 = f)).map (·.1)).getD .other

/-- Finish a call: the clock unchanged, a new core and an answer. -/
def done (k : ClockSt) (r : Core × Option (List Val)) : St × Option (List Val) :=
  (⟨k, r.1⟩, r.2)

/-- Run a non-read program, then finish. -/
def thenFin {D : Type} (p : NProg D) (g : D → St × Option (List Val)) :
    IProg (St × Option (List Val)) :=
  (emb p).bind fun d => .pure (g d)

/-- **The component**: WASI 0.3 over WASI 0.2. -/
def body : SBody St p2Command.imports p3World.imports := fun s q =>
  let k := s.clk
  let c := s.core
  let a := q.2
  match cls q.1.1 with
  | .streamNew => .pure (done k (let r := finNew c; (r.1, some [natV r.2.1, natV r.2.2])))
  | .streamWrite => thenFin (ioSw c a) fun d =>
      done k (let r := finSw c a d
              (r.1, some [natV (wcode ((swArgs a).elim 0 fun x => x.2.length) r.2)]))
  | .streamRead => (ioSr c a).bind fun d =>
      .pure (done k (let r := finSr c a d; (r.1, some [natV r.2.1, .record r.2.2])))
  | .dropR => .pure (done k (finDropR c a, some []))
  | .dropW => thenFin (ioDropW c a) fun _ => done k (finDropW c a, some [])
  | .futRead => thenFin (ioFr c a) fun d => done k (c, (finFr c a d).enc)
  | .futDropR => .pure (done k (finFDropR c a, some []))
  | .wsNew => .pure (done k (let r := finWsNew c; (r.1, some [natV r.2])))
  | .join => .pure (done k (finJoin c a, some []))
  | .wait => thenFin (ioWait c a) fun d =>
      done k (let r := finWait c a d; (r.1, some [natV r.2.1, natV r.2.2.1, natV r.2.2.2]))
  | .wvs => thenFin (ioWvs c a) fun d => done k (let r := finWvs c a d; (r.1, some [natV r.2]))
  | .stdin => thenFin (ioStdin c) fun d =>
      done k (let r := finIn c false d; (r.1, some [.record [natV r.2.1, natV r.2.2]]))
  | .now => thenFin ioNow fun x => (⟨(finNow k x).1, c⟩, some [.u64 (finNow k x).2])
  | .waitFor => thenFin (ioWaitFor a) fun _ => (⟨finWaitFor k a, c⟩, some [])
  | .getDirs => thenFin (nc getDirs (by simp [nrFns]) [] .pure) fun r => done k (c, encDirs r)
  | .openAt => thenFin (nc openAt (by simp [nrFns]) a .pure) fun r => done k (c, encOpen r)
  | .readVia => (ioRv c a).bind fun d =>
      .pure (done k (let r := finRv c a d; (r.1, some [.record [natV r.2.1, natV r.2.2]])))
  | .other => .pure (s, none)

/-- The initial state. -/
def init : St := {}

/-- **WASI 0.3 over WASI 0.2** as a strategy. -/
def p3OverP2 : Strategy (nsig p2Command.imports) (nsig p3World.imports) := ofSBody body init

/-! ## The theories of the implementation morphism -/

/-- **The WASI 0.3 theory of the slice** (corrected, `Silmaril.Wasi.Versions.P3OverP2.Theory`):
typing, the saturated clock, loose stdout and loose reads over the contents `F`. -/
def p3Th (F : BitVec 32 → List (BitVec 8)) : Protocol (Unit × ClockSt × OutSt × RdSt) WEv :=
  typed3.prod (clockTh3s.prod (stdoutTh3w.prod (fsReadTh3w F)))

/-- **The WASI 0.2 theory assumed**: the loose 0.2 theory `P2.p2Th .loose` with the file
contents `F` behind `read-via-stream` (`fsRead2 F`). -/
def p2ThF (F : BitVec 32 → List (BitVec 8)) : Protocol (P2.P2St × RdSt) WEv :=
  (P2.p2Th .loose).prod (fsRead2 F)

end Silmaril.Wasi.Versions.P3OverP2

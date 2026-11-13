module

public import Silmaril.Wasm.Component.Streams.Pipes.Defs

/-!
# The callback-ABI driver loop of the generated stream components

`Kernel.KM.coreWat` generates a core module whose driver loop is fixed text: the functions
`$stopReading`, `$onread`, `$onwrite`, `$pump`, the `[async-lift]` entry and the
`[callback][async-lift]` export. This module transcribes that loop into Lean, **for any
transformer** `T : Tr σ Val Val` in place of the compiled kernel (`$k`, `$done`, `$kflush`), as a
small-step machine `CBStep` over the drop-faithful built-ins of `Silmaril.Wasm.Component.Streams.Drop`.
Each step is one built-in call, one event delivered to the callback, or one pass of `$pump`'s loop
that calls no built-in.

## The state (`CB`)

The globals of the module: `$eof`, `$rdropped`, `$flushed`, `$dead`, `$wpend`, `$rpend`; the
kernel state (`$st` and the kernel buffer) as `s`; the output buffer `0x1000[$outoff..$outlen)` as
the list `out`, whose first `wl` items are offered to a pending `stream.write`; `pc`: running
`$pump`, returned `WAIT` (`2 | ws << 4`) to the runtime, or returned `EXIT` (`0`).

Ghosts (not in the module): `got` (the items read), `ack` (the items written), `ended` (a read
reported `DROPPED`).

## Transcription choices (stated)

* `$stopReading` drops the readable end at once when no read is pending. Here it sets `pdrop`, and
  the drop happens at the head of the next pass of `$pump`. Every call of `$stopReading` in the
  module is followed by `$pump` (or by the next pass of its loop) with no built-in call in between,
  so the sequence of built-in calls is the same.
* The `[async-lift]` entry's `stream.new`, `waitable-set.new`, `task.return` and joins are the
  network's setup (`Net.initStore`, `Setup.setup_init`); `CB.init` is the state after the entry's
  `if (call $done) (then (call $stopReading))`, before its call of `$pump`.
* `$onread` feeds the items to `T` until it is done, which is `Tr.feed`. `writeLen` offers all
  pending output, or at most `wmax` bytes (`wmax > 0`); a read asks for `batch` items.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Callback

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res Event blocked)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net

/-- Where the module is. -/
inductive PC where
  /-- Running `$pump`. -/
  | run
  /-- Returned `WAIT`: the runtime will call the callback with an event. -/
  | wait
  /-- Returned `EXIT`. -/
  | exit
  deriving DecidableEq

/-- **The state of the generated module.** -/
structure CB (σ : Type) where
  pc : PC
  s : σ
  out : List Val
  wl : Nat
  eof : Bool
  rdropped : Bool
  flushed : Bool
  dead : Bool
  wpend : Bool
  rpend : Bool
  /-- `$stopReading` asked for the readable end to be dropped. -/
  pdrop : Bool
  got : List Val
  ack : List Val
  ended : Bool

variable {σ : Type}

/-- `$stopReading`. -/
def CB.stopReading (c : CB σ) : CB σ :=
  { c with eof := true, pdrop := c.pdrop || (!c.rdropped && !c.rpend) }

/-- `$onread p` with the items `ys`. -/
def CB.onread (T : Tr σ Val Val) (c : CB σ) (p : Nat) (ys : List Val) : CB σ :=
  let c₁ : CB σ :=
    { c with
      s := (T.feed c.s ys).1
      out := c.out ++ (T.feed c.s ys).2
      got := c.got ++ ys }
  let c₂ := if status p = 0 then c₁ else { c₁ with ended := true }.stopReading
  if T.done c₂.s then c₂.stopReading else c₂

/-- `$onwrite p`. -/
def CB.onwrite (c : CB σ) (p : Nat) : CB σ :=
  let c₁ : CB σ := { c with out := c.out.drop (count p), ack := c.ack ++ c.out.take (count p) }
  if status p = 0 then c₁ else { c₁ with dead := true }.stopReading

/-- The state after the `[async-lift]` entry, before its call of `$pump`. -/
def CB.init (T : Tr σ Val Val) : CB σ :=
  let c : CB σ :=
    { pc := .run, s := T.init, out := [], wl := 0, eof := false, rdropped := false
      flushed := false, dead := false, wpend := false, rpend := false, pdrop := false
      got := [], ack := [], ended := false }
  if T.done T.init then c.stopReading else c

/-- `writeLen`: all pending output, or at most `wmax` bytes. -/
def writeLen (wmax len : Nat) : Nat := if wmax = 0 then len else min wmax len

/-- **One step of the generated module** with input readable end `r`, output writable end `w`,
waitable set `ws`, read size `batch` and write bound `wmax`. -/
inductive CBStep (T : Tr σ Val Val) (r w ws batch wmax : Nat) :
    DStore → CB σ → DStore → CB σ → Prop where
  /-- The drop `$stopReading` asked for. -/
  | dropR {st c st' res} : c.pc = .run → c.pdrop = true →
      dstep st (.streamDropR r) = some (st', res) →
      CBStep T r w ws batch wmax st c st' { c with pdrop := false, rdropped := true }
  /-- A write is pending: return `WAIT`. -/
  | waitW {st c} : c.pc = .run → c.pdrop = false → c.wpend = true →
      CBStep T r w ws batch wmax st c st { c with pc := .wait }
  /-- Write pending output. -/
  | write {st c st' res} : c.pc = .run → c.pdrop = false → c.wpend = false → c.dead = false →
      c.out ≠ [] →
      dstep st (.streamWrite w (c.out.take (writeLen wmax c.out.length))) = some (st', .nat res) →
      CBStep T r w ws batch wmax st c st'
        (if res = blocked then { c with pc := .wait, wpend := true, wl := writeLen wmax c.out.length }
         else c.onwrite res)
  /-- At the end of the input: compute the flush. -/
  | flush {st c} : c.pc = .run → c.pdrop = false → c.wpend = false → c.out = [] →
      c.eof = true → c.flushed = false → c.dead = false →
      CBStep T r w ws batch wmax st c st { c with flushed := true, out := T.flush c.s }
  /-- At the end of the input with a read pending: return `WAIT`. -/
  | waitEof {st c} : c.pc = .run → c.pdrop = false → c.wpend = false →
      (c.dead = true ∨ c.out = []) → c.eof = true → (c.flushed = true ∨ c.dead = true) →
      c.rpend = true → CBStep T r w ws batch wmax st c st { c with pc := .wait, out := [] }
  /-- At the end: `$stopReading` (its drop happens at the head of the next pass). -/
  | stopEnd {st c} : c.pc = .run → c.pdrop = false → c.wpend = false →
      (c.dead = true ∨ c.out = []) → c.eof = true → (c.flushed = true ∨ c.dead = true) →
      c.rpend = false → c.rdropped = false →
      CBStep T r w ws batch wmax st c st { c with out := [] }.stopReading
  /-- At the end, the readable end dropped: drop the writable end and return `EXIT`. -/
  | dropW {st c st' res} : c.pc = .run → c.pdrop = false → c.wpend = false →
      (c.dead = true ∨ c.out = []) → c.eof = true → (c.flushed = true ∨ c.dead = true) →
      c.rpend = false → c.rdropped = true → dstep st (.streamDropW w) = some (st', res) →
      CBStep T r w ws batch wmax st c st' { c with pc := .exit, out := [] }
  /-- A read is pending: return `WAIT`. -/
  | waitR {st c} : c.pc = .run → c.pdrop = false → c.wpend = false →
      (c.dead = true ∨ c.out = []) → c.eof = false → c.rpend = true →
      CBStep T r w ws batch wmax st c st { c with pc := .wait, out := [] }
  /-- Read. -/
  | read {st c st' res} : c.pc = .run → c.pdrop = false → c.wpend = false →
      (c.dead = true ∨ c.out = []) → c.eof = false → c.rpend = false →
      dstep st (.streamRead r batch) = some (st', res) →
      CBStep T r w ws batch wmax st c st'
        (match res with
         | .read p ys => { c with out := [] }.onread T p ys
         | _ => { c with pc := .wait, rpend := true, out := [] })
  /-- The callback, with an event on the readable end. -/
  | evIn {st c st' e} : c.pc = .wait → DWait st ws r st' e →
      CBStep T r w ws batch wmax st c st'
        (if c.rpend then { c with pc := .run, rpend := false }.onread T e.payload e.items
         else { c with pc := .run, ended := true }.stopReading)
  /-- The callback, with an event on the writable end. -/
  | evOut {st c st' e} : c.pc = .wait → DWait st ws w st' e →
      CBStep T r w ws batch wmax st c st'
        (if c.wpend then { c with pc := .run, wpend := false }.onwrite e.payload
         else { c with pc := .run, dead := true }.stopReading)

/-! ## The node the module implements -/

/-- The flush still to be computed once the readable end is dropped. -/
def CB.fl (T : Tr σ Val Val) (c : CB σ) : List Val :=
  if c.rdropped && !c.flushed && !c.dead then T.flush c.s else []

/-- The output, as a `Net` output. -/
def CB.absOut (T : Tr σ Val Val) (c : CB σ) : Out :=
  ⟨if c.pc = .exit then .closed c.dead
   else if c.dead then .dead
   else if c.wpend then .busy (c.out.take c.wl) (c.out.drop c.wl ++ c.fl T)
   else .idle (c.out ++ c.fl T), c.ack⟩

/-- **The refinement map**: the state of the `Net` node that the module's state stands for. -/
def CB.abs (T : Tr σ Val Val) (c : CB σ) : NSt σ where
  s := c.s
  got := c.got
  rd := if c.rdropped then .gone c.ended else if c.rpend then .busy
    else if c.ended then .ended else .idle
  outs := [c.absOut T]

/-! ## The module as the transformer of a pipe -/

/-- A pipe whose transformer is the generated module: the source and the sink are nodes of
`Net`, the transformer is `CB`. -/
structure CSys (σ : Type) where
  st : DStore
  src : NSt Unit
  cb : CB σ
  snk : NSt Unit

/-- One step of the source, of the module or of the sink. -/
inductive CStep (xs : List Val) (T : Tr σ Val Val) (batch wmax : Nat) : CSys σ → CSys σ → Prop
  | src {c : CSys σ} {st' x'} : NStep (Pipes.src xs 0) ((Pipes.pipe xs T).ws 0) c.st c.src st' x' →
      CStep xs T batch wmax c { c with st := st', src := x' }
  | cb {c : CSys σ} {st' cb'} :
      CBStep T (rh 0) (wh 1) ((Pipes.pipe xs T).ws 1) batch wmax c.st c.cb st' cb' →
      CStep xs T batch wmax c { c with st := st', cb := cb' }
  | snk {c : CSys σ} {st' x'} : NStep (Pipes.sink 1) ((Pipes.pipe xs T).ws 2) c.st c.snk st' x' →
      CStep xs T batch wmax c { c with st := st', snk := x' }

/-- Steps, iterated. -/
inductive CSteps (xs : List Val) (T : Tr σ Val Val) (batch wmax : Nat) : CSys σ → CSys σ → Prop
  | refl (c : CSys σ) : CSteps xs T batch wmax c c
  | tail {c c' c'' : CSys σ} : CSteps xs T batch wmax c c' → CStep xs T batch wmax c' c'' →
      CSteps xs T batch wmax c c''

/-- The initial system. -/
def CSys.init (xs : List Val) (T : Tr σ Val Val) : CSys σ :=
  ⟨initStore (Pipes.pipe xs T), NSt.init (Pipes.src xs 0), CB.init T, NSt.init (Pipes.sink 1)⟩

/-- The system of `Pipes.pipe xs T` that a system with the module stands for. -/
def CSys.abs (xs : List Val) (T : Tr σ Val Val) (c : CSys σ) : Sys (Pipes.pipe xs T) :=
  ⟨c.st, fun i => match i with
    | ⟨0, _⟩ => c.src
    | ⟨1, _⟩ => c.cb.abs T
    | ⟨2, _⟩ => c.snk
    | ⟨n + 3, h⟩ => absurd (show n + 3 < 3 from h) (by omega)⟩

/-- The reachable systems. -/
def CReach (xs : List Val) (T : Tr σ Val Val) (batch wmax : Nat) (c : CSys σ) : Prop :=
  CSteps xs T batch wmax (CSys.init xs T) c

end Silmaril.Wasm.Component.Streams.Callback

module

public import Silmaril.Wasm.Component.Async.Defs
public import Silmaril.Wasm.Component.Async.Cabi.Defs

@[expose] public section

/-!
# The Silmaril async store model against the transcribed `definitions.py`

`Silmaril.Wasm.Component.Async` (the store model used by WASI 0.3) and
`Silmaril.Wasm.Component.Async.Cabi` (the transcription of `definitions.py` at `d095e2f`) are run
on the same operations and their answers compared.

**Translation** (`toSteps`). One component instance (`0`) runs one async stackful task
(thread `0`), which performs the operations of the store model, all `async`:

| Store model `Op` | Transcription |
|---|---|
| `streamNew`, `futureNew` | `stream.new`, `future.new` (element type `ty`) |
| `streamWrite w xs` | store `xs` at a fresh address, `stream.write` (async) of `|xs|` |
| `streamRead r n` | `stream.read` (async) of `n` into a fresh address |
| `futureWrite w v`, `futureRead r` | the same with one element |
| `stream/future drop-*` | `{stream,future}.drop-{readable,writable}` |
| `wsNew`, `join`, `poll`, `wsDrop` | the built-ins |
| `wait s` | `waitable-set.wait`, then a `tick` of thread `0` when it is ready |

Each operation gets its own memory region (`region k`), so a parked buffer is never
overwritten before the peer copies from it.

**Observations** (`Obs`). A trap; `BLOCKED`-suspension of `wait`; or the flat results with
the items delivered. The store model's `Res` is read as flat results: `.ends r w` is
`r | w << 32`, `.read code xs` is `[code]` with items `xs`, `.event e` is
`[code, index, payload]` with the items of the event. On the transcription side the items of
a read are read back from the read's region; the items of a `stream-read`/`future-read` event
from the region of the last read of that handle.

`firstDiff ops` runs both from their empty stores and returns the index of the first operation
on which they differ (`none`: they agree on all of `ops`). Runs stop at the first trap or
suspension (after comparing it).
-/

namespace Silmaril.Wasm.Component.Async.CabiAgree

open Silmaril.Wasm.Component (Val)

/-- The store model. -/
abbrev MOp := Silmaril.Wasm.Component.Async.Op
/-- The store model's state. -/
abbrev MStore := Silmaril.Wasm.Component.Async.Store

/-- The element type of all streams and futures. -/
def ty : Cabi.Ty := { id := 0, kind := .number }

/-- The memory region of the `k`-th operation. -/
def region (k : Nat) : Nat := 4096 * (k + 1)

/-- An observation. -/
inductive Obs where
  | trap
  /-- `waitable-set.wait` suspended (no event). -/
  | blocked
  /-- Flat results and delivered items. -/
  | ret (vs : List Nat) (items : List Val)
  deriving Repr

mutual
/-- Equality of values, by structural recursion (the derived `BEq Val` is opaque to the
kernel). -/
def valEq : Val → Val → Bool
  | .bool a, .bool b => a == b
  | .s8 a, .s8 b | .u8 a, .u8 b => a == b
  | .s16 a, .s16 b | .u16 a, .u16 b => a == b
  | .s32 a, .s32 b | .u32 a, .u32 b => a == b
  | .s64 a, .s64 b | .u64 a, .u64 b => a == b
  | .f32 a, .f32 b => a == b
  | .f64 a, .f64 b => a == b
  | .char a, .char b => a == b
  | .record xs, .record ys => valsEq xs ys
  | .variant c p, .variant d q => c == d && optEq p q
  | _, _ => false
/-- Equality of value lists. -/
def valsEq : List Val → List Val → Bool
  | [], [] => true
  | x :: xs, y :: ys => valEq x y && valsEq xs ys
  | _, _ => false
/-- Equality of optional values. -/
def optEq : Option Val → Option Val → Bool
  | none, none => true
  | some a, some b => valEq a b
  | _, _ => false
end

/-- Equality of observations. -/
def Obs.eqb : Obs → Obs → Bool
  | .trap, .trap => true
  | .blocked, .blocked => true
  | .ret vs xs, .ret ws ys => vs == ws && valsEq xs ys
  | _, _ => false

/-- The observation is a trap. -/
def Obs.isTrap : Obs → Bool
  | .trap => true
  | _ => false

/-- The store model's answer as an observation. -/
def obsOfRes : Silmaril.Wasm.Component.Async.Res → Obs
  | .unit => .ret [] []
  | .nat n => .ret [n] []
  | .ends r w => .ret [r + w * 2 ^ 32] []
  | .read code xs => .ret [code] xs
  | .event e => .ret [e.code.toNat, e.index, e.payload] e.items
  | .blocked => .blocked

/-- The transcription's steps for the `k`-th operation. -/
def toSteps (k : Nat) : MOp → List (Cabi.Step Val)
  | .streamNew => [.op (.streamNew ty)]
  | .streamWrite w xs => [.op (.memSet (region k) xs), .op (.copy .streamW ty true w (region k) xs.length)]
  | .streamRead r n => [.op (.copy .streamR ty true r (region k) n)]
  | .streamDropR r => [.op (.dropEnd .streamR ty r)]
  | .streamDropW w => [.op (.dropEnd .streamW ty w)]
  | .futureNew => [.op (.futureNew ty)]
  | .futureWrite w v => [.op (.memSet (region k) [v]), .op (.copy .futureW ty true w (region k) 1)]
  | .futureRead r => [.op (.copy .futureR ty true r (region k) 1)]
  | .futureDropR r => [.op (.dropEnd .futureR ty r)]
  | .futureDropW w => [.op (.dropEnd .futureW ty w)]
  | .wsNew => [.op .wsNew]
  | .join h s => [.op (.join h s)]
  | .wait s => [.op (.wsWait s)]
  | .poll s => [.op (.wsPoll s)]
  | .wsDrop s => [.op (.wsDrop s)]
  | .callAsync | .subtaskDrop _ | .taskReturn _ _ => []

/-- The transcription's state for the comparison: the store and the region of the last read
of each handle. -/
structure RState where
  st : Cabi.Store Val
  lastRead : Nat → Nat := fun _ => 0

/-- The initial transcription state: instance `0` running an async stackful task. -/
def rInit : RState :=
  match (Cabi.Store.init 1 : Cabi.Store Val).runStep (.invoke (.guest 0 true true false 0) []) with
  | .ok st => { st := st }
  | .error _ => { st := Cabi.Store.init 1 }

/-- `count` cells of instance `0` from `ptr`. -/
def cells (st : Cabi.Store Val) (ptr count : Nat) : List Val :=
  match st.insts 0 with
  | some ins => (List.range count).map fun j => ins.mem (ptr + j)
  | none => []

/-- The number of items a packed copy result reports, for a stream; `1`/`0` for a future. -/
def itemCount (stream : Bool) (payload : Nat) : Nat :=
  if stream then payload / 16 else if payload = 0 then 1 else 0

/-- Run the transcription on the `k`-th operation: the observation and the next state. -/
def rStep (rs : RState) (k : Nat) (o : MOp) : Obs × RState :=
  match rs.st.run (toSteps k o) with
  | .error _ => (.trap, rs)
  | .ok st =>
    -- a `wait` that blocked: resume thread 0 if it is ready
    let st := match o, st.cur with
      | .wait _, none => if st.ready 0 then
          match st.runStep (.tick 0) with
          | .ok st' => st'
          | .error _ => st
        else st
      | _, _ => st
    match st.cur with
    | none => (.blocked, { rs with st := st })
    | some _ =>
      let out := match st.threads 0 with
        | some t => t.out
        | none => []
      match o, out with
      | .streamRead r _, [p] =>
        if p = Cabi.BLOCKED then (.ret out [], { st := st, lastRead := upd rs.lastRead r (region k) })
        else (.ret out (cells st (region k) (itemCount true p)), { rs with st := st })
      | .futureRead r, [p] =>
        if p = Cabi.BLOCKED then (.ret out [], { st := st, lastRead := upd rs.lastRead r (region k) })
        else (.ret out (cells st (region k) (itemCount false p)), { rs with st := st })
      | .wait _, [c, h, p] | .poll _, [c, h, p] =>
        let items := if c = Cabi.EventCode.streamRead.toNat then
            cells st (rs.lastRead h) (itemCount true p)
          else if c = Cabi.EventCode.futureRead.toNat then cells st (rs.lastRead h) (itemCount false p)
          else []
        (.ret out items, { rs with st := st })
      | _, _ => (.ret out [], { rs with st := st })
where
  upd (f : Nat → Nat) (a v : Nat) : Nat → Nat := fun b => if b = a then v else f b

/-- Compare the two models on `ops` from operation index `k`. -/
def compareFrom (m : MStore) (rs : RState) (k : Nat) : List MOp → Option Nat
  | [] => none
  | o :: os =>
    let mo := match Silmaril.Wasm.Component.Async.step m o with
      | some (_, r) => obsOfRes r
      | none => .trap
    let (ro, rs') := rStep rs k o
    if mo.eqb ro then
      match mo, Silmaril.Wasm.Component.Async.step m o with
      | .ret _ _, some (m', _) => compareFrom m' rs' (k + 1) os
      | _, _ => none
    else some k

/-- Like `compareFrom`, but a step on which the transcription traps and the store model does
not ends the comparison successfully: the trace left the fragment where `definitions.py` is
defined (a protocol violation it rejects). -/
def compareRFrom (m : MStore) (rs : RState) (k : Nat) : List MOp → Option Nat
  | [] => none
  | o :: os =>
    let mo := match Silmaril.Wasm.Component.Async.step m o with
      | some (_, r) => obsOfRes r
      | none => .trap
    let (ro, rs') := rStep rs k o
    if ro.isTrap && !mo.isTrap then none
    else if mo.eqb ro then
      match mo, Silmaril.Wasm.Component.Async.step m o with
      | .ret _ _, some (m', _) => compareRFrom m' rs' (k + 1) os
      | _, _ => none
    else some k

/-- The comparison up to transcription traps. -/
def compareR (ops : List MOp) : Option Nat :=
  compareRFrom Silmaril.Wasm.Component.Async.Store.empty rInit 0 ops

/-! ## Bounded families of traces -/

/-- One stream (`r = 1`, `w = 2`) with both ends joined to the waitable set `3`. -/
def pre : List MOp := [.streamNew, .wsNew, .join 1 3, .join 2 3]

/-- All traces of exactly `n` operations over `alpha`. -/
def exact (alpha : List MOp) : Nat → List (List MOp)
  | 0 => [[]]
  | n + 1 => (exact alpha n).flatMap fun t => alpha.map fun o => o :: t

/-- All traces of at most `n` operations over `alpha`. -/
def upTo (alpha : List MOp) (n : Nat) : List (List MOp) := (List.range (n + 1)).flatMap (exact alpha)

/-- Two item values. -/
def va : Val := .bool true
/-- Two item values. -/
def vb : Val := .bool false

/-- Writes and reads of one item, `poll` and `wait`. -/
def alpha1 : List MOp := [.streamWrite 2 [va], .streamRead 1 1, .poll 3, .wait 3]

/-- Writes and reads of two items, `poll` and `wait`. -/
def alpha2 : List MOp := [.streamWrite 2 [va, vb], .streamRead 1 2, .poll 3, .wait 3]

/-- Mixed lengths and drops: the alphabet on which the differences show. -/
def alphaMixed : List MOp :=
  [.streamWrite 2 [va], .streamWrite 2 [va, vb], .streamRead 1 1, .streamRead 1 2,
   .streamDropR 1, .streamDropW 2, .poll 3]

/-- **The comparison**: the index of the first operation on which the models differ. -/
def firstDiff (ops : List MOp) : Option Nat :=
  compareFrom Silmaril.Wasm.Component.Async.Store.empty rInit 0 ops

/-- Both models' observations on `ops`, for display. -/
def observe (ops : List MOp) : List (Obs × Obs) :=
  go Silmaril.Wasm.Component.Async.Store.empty rInit 0 ops
where
  go (m : MStore) (rs : RState) (k : Nat) : List MOp → List (Obs × Obs)
    | [] => []
    | o :: os =>
      let (mo, m') := match Silmaril.Wasm.Component.Async.step m o with
        | some (m', r) => (obsOfRes r, m')
        | none => (.trap, m)
      let (ro, rs') := rStep rs k o
      (mo, ro) :: go m' rs' (k + 1) os

/-- At operation `k` of `ops`, the store model answers `m` and the transcription `r`. -/
def answersAre (ops : List MOp) (k : Nat) (m r : Obs) : Bool :=
  match (observe ops)[k]? with
  | some (a, b) => a.eqb m && b.eqb r
  | none => false

end Silmaril.Wasm.Component.Async.CabiAgree

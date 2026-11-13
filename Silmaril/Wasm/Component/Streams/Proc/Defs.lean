module

public import Silmaril.Wasm.Component.Async.Defs
public import Silmaril.Wasm.Component.Streams.Spec.Defs
public import Silmaril.Wasm.Component.Streams.Chunks.Defs

/-!
# Stream transformer components over the Component Model stream built-ins

The transformers of `Silmaril.Wasm.Component.Streams.Spec` as **concurrent components** that talk
only through the stream and waitable-set built-ins of `Silmaril.Wasm.Component.Async` (imported, not
modified): every step of a component is one call of `Async.step` on the shared handle table
(or a purely local step), and the components run in **any interleaving**.

The pipeline `producer → transformer → consumer`:

* channel `A` (stream id `1`): readable end `1` (held by the transformer), writable end `2`
  (held by the producer);
* channel `B` (stream id `3`): readable end `3` (held by the consumer), writable end `4` (held by
  the transformer);
* waitable sets `5` (the transformer's: ends `1` and `4` joined), `6` (the producer's: end `2`),
  `7` (the consumer's: end `3`).

`setupOps` creates exactly these handles from the empty store (`stream.new` twice,
`waitable-set.new` three times and four `waitable.join`s).

## The components

* **Producer** (`PPc`, `pStep`): writes the given chunks in order with `stream.write 2 c`. A write
  that finds no pending read is `BLOCKED` and the producer waits on its set; a rendezvous of
  `k < |c|` items leaves the rest `c.drop k` to be written again; `DROPPED` (the reader has gone)
  stops it. At the end it drops its writable end (`stream.drop-writable`).
* **Transformer** (`TPc`, `tStep T N`), for any `T : Tr σ Val Val` and batch size `N`:
  `stream.read 1 N`; the items received are fed to `T`; its outputs are written to `4` (again
  completing partial copies); when `T` is `done` (e.g. `take`) it drops its readable end at once,
  and when the input ends (`DROPPED`) it drops its readable end too; then it writes `T`'s flush
  and drops its writable end.
* **Consumer** (`CPc`, `cStep n`): reads with `stream.read 3 n` (any `n` at every step,
  `Step.cons`), accumulating the items, until `DROPPED`; then drops its readable end.

`Step` is the interleaving of the three; `Reach cs T N` the systems reachable from the setup
store with the producer about to write the chunks `cs`.

## Simplifications

Those of `Async` (one handle table, items are values, no zero-length-copy special case, no
cancellation or backpressure). The components are given as step functions over the built-ins,
not as core modules: the link to the jco adaptor's async lifts (`Silmaril.Wasm.Jco.Async`) is
not made here.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Proc

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async
open scoped Silmaril.Wasm.Component.Streams.Tr

/-! ## Handles -/

/-- The setup: the two streams, the three waitable sets and the joins. -/
def setupOps : List Op :=
  [.streamNew, .streamNew, .wsNew, .join 1 5, .join 4 5, .wsNew, .join 2 6, .wsNew, .join 3 7]

/-- Run a list of built-ins, discarding results. -/
def runOps : Store → List Op → Option Store
  | st, [] => some st
  | st, op :: ops => (step st op).bind fun p => runOps p.1 ops

/-- The status of a packed copy result (`result | count << 4`). -/
def copyStatus (p : Nat) : Nat := p % 16

/-- The count of a packed copy result. -/
def copyCount (p : Nat) : Nat := p / 16

/-! ## The producer -/

/-- The producer's program counter. -/
inductive PPc where
  /-- About to write the first of these chunks (or to drop the writable end when none is left). -/
  | send (cs : List (List Val))
  /-- The write of `c` was issued; the chunks `cs` follow. -/
  | wait (c : List Val) (cs : List (List Val))
  /-- The reader has gone: drop the writable end. -/
  | close
  /-- Finished. -/
  | fin

/-- What remains after `k` items of `c` were copied. -/
def PPc.after (c : List Val) (k : Nat) (cs : List (List Val)) : PPc :=
  if c.drop k = [] then .send cs else .send (c.drop k :: cs)

/-- The producer's continuation after a copy with packed result `p`. -/
def PPc.onCopy (c : List Val) (cs : List (List Val)) (p : Nat) : PPc :=
  if copyStatus p = 0 then PPc.after c (copyCount p) cs else .close

/-- **One step of the producer**: one built-in call. -/
def pStep (st : Store) : PPc → Option (Store × PPc)
  | .send [] | .close =>
    (step st (.streamDropW 2)).map fun p => (p.1, .fin)
  | .send (c :: cs) =>
    match step st (.streamWrite 2 c) with
    | some (st', .nat p) => some (st', if p = blocked then .wait c cs else PPc.onCopy c cs p)
    | _ => none
  | .wait c cs =>
    match step st (.wait 6) with
    | some (st', .event e) => some (st', PPc.onCopy c cs e.payload)
    | _ => none
  | .fin => none

/-! ## The transformer -/

/-- The transformer's program counter. `next = some s`: back to reading in state `s` after the
write; `next = none`: close after the write. -/
inductive TPc (σ : Type) where
  /-- About to read (or to stop when `T` is done). -/
  | rd (s : σ)
  /-- The read was issued. -/
  | wtR (s : σ)
  /-- The input has ended: drop the readable end. -/
  | eoi (s : σ)
  /-- About to write `ys`. -/
  | wr (ys : List Val) (next : Option σ)
  /-- The write of `ys` was issued. -/
  | wtW (ys : List Val) (next : Option σ)
  /-- Drop the writable end. -/
  | cl
  /-- Finished. -/
  | fin
  /-- The consumer went away while the transformer was writing (not reachable here). -/
  | fault

variable {σ : Type}

/-- After receiving `xs` in state `s`, or the end of the input (`DROPPED`). -/
def TPc.onRead (T : Tr σ Val Val) (s : σ) (p : Nat) (xs : List Val) : TPc σ :=
  if copyStatus p = 0 then .wr (T.feed s xs).2 (some (T.feed s xs).1) else .eoi s

/-- After a write with packed result `p`. -/
def TPc.onWrite (ys : List Val) (next : Option σ) (p : Nat) : TPc σ :=
  if copyStatus p = 0 then .wr (ys.drop (copyCount p)) next else .fault

/-- Where a finished write continues. -/
def TPc.resume : Option σ → TPc σ
  | some s => .rd s
  | none => .cl

/-- **One step of the transformer** `T` reading batches of `N` items. -/
def tStep (T : Tr σ Val Val) (N : Nat) (st : Store) : TPc σ → Option (Store × TPc σ)
  | .rd s =>
    if T.done s then (step st (.streamDropR 1)).map fun p => (p.1, .wr (T.flush s) none)
    else
      match step st (.streamRead 1 N) with
      | some (st', .nat _) => some (st', .wtR s)
      | some (st', .read p xs) => some (st', TPc.onRead T s p xs)
      | _ => none
  | .wtR s =>
    match step st (.wait 5) with
    | some (st', .event e) => some (st', TPc.onRead T s e.payload e.items)
    | _ => none
  | .eoi s => (step st (.streamDropR 1)).map fun p => (p.1, .wr (T.flush s) none)
  | .wr [] next => some (st, TPc.resume next)
  | .wr (y :: ys) next =>
    match step st (.streamWrite 4 (y :: ys)) with
    | some (st', .nat p) =>
      some (st', if p = blocked then .wtW (y :: ys) next else TPc.onWrite (y :: ys) next p)
    | _ => none
  | .wtW ys next =>
    match step st (.wait 5) with
    | some (st', .event e) => some (st', TPc.onWrite ys next e.payload)
    | _ => none
  | .cl => (step st (.streamDropW 4)).map fun p => (p.1, .fin)
  | .fin | .fault => none

/-! ## The consumer -/

/-- The consumer's program counter, with the items received so far. -/
inductive CPc where
  /-- About to read. -/
  | recv (acc : List Val)
  /-- The read was issued. -/
  | wait (acc : List Val)
  /-- The input has ended: drop the readable end. -/
  | close (acc : List Val)
  /-- Finished with these items. -/
  | fin (acc : List Val)

/-- After a read with packed result `p` delivering `xs`. -/
def CPc.onRead (acc : List Val) (p : Nat) (xs : List Val) : CPc :=
  if copyStatus p = 0 then .recv (acc ++ xs) else .close acc

/-- **One step of the consumer**, reading up to `n` items. -/
def cStep (n : Nat) (st : Store) : CPc → Option (Store × CPc)
  | .recv acc =>
    match step st (.streamRead 3 n) with
    | some (st', .nat _) => some (st', .wait acc)
    | some (st', .read p xs) => some (st', CPc.onRead acc p xs)
    | _ => none
  | .wait acc =>
    match step st (.wait 7) with
    | some (st', .event e) => some (st', CPc.onRead acc e.payload e.items)
    | _ => none
  | .close acc => (step st (.streamDropR 3)).map fun p => (p.1, .fin acc)
  | .fin _ => none

/-! ## The system -/

/-- The shared store and the three program counters. -/
structure Sys (σ : Type) where
  st : Store
  p : PPc
  t : TPc σ
  c : CPc

/-- **One step of the pipeline**: a step of any one component (the consumer may choose any
positive read size). -/
inductive Step (T : Tr σ Val Val) (N : Nat) : Sys σ → Sys σ → Prop where
  | prod {s : Sys σ} {st' p'} : pStep s.st s.p = some (st', p') →
      Step T N s { s with st := st', p := p' }
  | trans {s : Sys σ} {st' t'} : tStep T N s.st s.t = some (st', t') →
      Step T N s { s with st := st', t := t' }
  | cons {s : Sys σ} {st' c'} (n : Nat) : 0 < n → cStep n s.st s.c = some (st', c') →
      Step T N s { s with st := st', c := c' }

/-- The steps of the pipeline, iterated. -/
inductive Steps (T : Tr σ Val Val) (N : Nat) : Sys σ → Sys σ → Prop where
  | refl (s : Sys σ) : Steps T N s s
  | tail {s s' s'' : Sys σ} : Steps T N s s' → Step T N s' s'' → Steps T N s s''

/-- **The systems reachable** from the setup store, with the producer about to write `cs`. -/
def Reach (T : Tr σ Val Val) (N : Nat) (cs : List (List Val)) (s : Sys σ) : Prop :=
  ∃ st₀, runOps Store.empty setupOps = some st₀ ∧
    Steps T N { st := st₀, p := .send cs, t := .rd T.init, c := .recv [] } s

/-! ## Lines and uniform chunks of a byte stream -/

/-- The line splitter on a stream of items: each line becomes a `record` of its items. -/
def linesV (sep : Val → Bool) : Tr ((Unit × List Val) × Unit) Val Val :=
  (Tr.map (fun x => [x]) ⟫ Tr.linesT sep) ⟫ Tr.map Val.record

/-- The uniform rechunker on a stream of items: records of `n` items. -/
def rechunkV (n : Nat) : Tr ((Unit × List Val) × Unit) Val Val :=
  (Tr.map (fun x => [x]) ⟫ Tr.rechunk n) ⟫ Tr.map Val.record

end Silmaril.Wasm.Component.Streams.Proc

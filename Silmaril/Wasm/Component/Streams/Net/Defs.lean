module

public import Silmaril.Wasm.Component.Streams.Drop.Defs
public import Silmaril.Wasm.Component.Streams.Spec.Defs

/-!
# Networks of stream components over the drop-faithful built-ins

Stream transformer components as concurrent nodes of a **network** of streams, talking only
through the built-ins of `Silmaril.Wasm.Component.Streams.Drop` (the Component Model's drop
behaviour: `DROPPED` with a count, `DROPPED` on an idle end). One generic node program covers
the producer, transformers, `tee` and the consumer:

* a **node** (`Node`) has a transformer `T : Tr σ Val Val`, at most one input stream and a list of
  output streams. A node without input is a **source**: it emits `T.flush T.init` (`Tr.source xs`
  emits `xs`). A node with two outputs and `T = Tr.id` is a **tee**; a node without outputs is a
  **sink**, whose result is what it has read (`got`).
* a **network** (`Net`): `k` nodes and `m` streams; stream `c` has the readable end `2c+1`
  (also its id) and the writable end `2c+2`; node `i` waits on its waitable set `2m+1+i`, joined
  by its ends. `wr c` is the writer of `c` (a node and an output position) and `rd c` its reader.

## The node program (`NStep`)

Every step is one built-in call (or one `waitable-set.wait`). The program is nondeterministic, so
the theorems hold for every policy a real component could follow (read sizes, write sizes, and
the order in which reads, writes and drops are issued):

* `read`: `stream.read` of any `n > 0` items when the input is idle and `T` is not done; the items
  are fed to `T` and its outputs are queued on every live output;
* `write`: `stream.write` of any nonempty prefix of an idle output's queue;
* `waitIn` / `waitOut`: `waitable-set.wait` delivers an event of one of the node's ends, which it
  **dispatches on the event's handle**: a read event feeds the items (and `DROPPED` ends the
  input), a write event completes or kills the copy (`DROPPED`: the reader has gone, the output is
  dead). Events on idle ends (the peer dropped) are handled the same way;
* `dropIn`: `stream.drop-readable` when the input has ended, or `T` is done, or every output is
  dead; `T`'s flush is queued;
* `dropOut`: `stream.drop-writable` of an output that is dead or idle with an empty queue, once
  the input has been dropped.

`Reach net s`: the systems reachable from `init net`, the store after creating the `m` streams
and the `k` waitable sets and joining every end to its node's set.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Net

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event blocked upd)
open Silmaril.Wasm.Component.Streams.Drop

/-- The status of a packed copy result (`result | count << 4`). -/
def status (p : Nat) : Nat := p % 16

/-- The count of a packed copy result. -/
def count (p : Nat) : Nat := p / 16

/-- A source of the items `xs`: reads nothing, emits `xs` as its flush. -/
def _root_.Silmaril.Wasm.Component.Streams.Tr.source (xs : List Val) : Tr Unit Val Val where
  init := ()
  step _ _ := ((), [])
  flush _ := xs

/-- **A node** of a network. -/
structure Node where
  σ : Type
  T : Tr σ Val Val
  /-- The input stream (`none`: a source). -/
  inp : Option Nat
  /-- The output streams, in order. -/
  outs : List Nat

/-- **A network**: `k` nodes, `m` streams, the writer and reader of every stream. -/
structure Network where
  k : Nat
  node : Fin k → Node
  m : Nat
  /-- The writer of a stream: a node and its output position. -/
  wr : Nat → Fin k × Nat
  /-- The reader of a stream. -/
  rd : Nat → Fin k

/-- The network is well formed: the writer and reader maps agree with the nodes. -/
structure Network.WF (net : Network) : Prop where
  rd_inp : ∀ c, c < net.m → (net.node (net.rd c)).inp = some c
  wr_out : ∀ c, c < net.m → (net.node (net.wr c).1).outs[(net.wr c).2]? = some c
  inp_rd : ∀ i c, (net.node i).inp = some c → c < net.m ∧ net.rd c = i
  out_wr : ∀ i j c, (net.node i).outs[j]? = some c → c < net.m ∧ net.wr c = (i, j)
  no_loop : ∀ c, c < net.m → (net.wr c).1 ≠ net.rd c

/-- A Boolean check of `Network.WF` (`Network.WF.of_check`), by evaluation. -/
def Network.check (net : Network) : Bool :=
  (List.range net.m).all (fun c =>
    (net.node (net.rd c)).inp == some c &&
    (net.node (net.wr c).1).outs[(net.wr c).2]? == some c &&
    (net.wr c).1 != net.rd c) &&
  (List.finRange net.k).all (fun i =>
    (match (net.node i).inp with
      | some c => decide (c < net.m) && net.rd c == i
      | none => true) &&
    (List.range (net.node i).outs.length).all (fun j =>
      match (net.node i).outs[j]? with
      | some c => decide (c < net.m) && net.wr c == (i, j)
      | none => true))

/-- The readable end of stream `c` (also the stream's id). -/
def rh (c : Nat) : Nat := 2 * c + 1

/-- The writable end of stream `c`. -/
def wh (c : Nat) : Nat := 2 * c + 2

/-- The waitable set of node `i`. -/
def Network.ws (net : Network) (i : Nat) : Nat := 2 * net.m + 1 + i

/-! ## Node states -/

/-- The input side of a node. -/
inductive RV where
  | idle
  /-- A read is in progress. -/
  | busy
  /-- `DROPPED` received: the input has ended. -/
  | ended
  /-- The readable end has been dropped (`eof`: after the input ended). -/
  | gone (eof : Bool)
  deriving DecidableEq

/-- The state of one output. -/
inductive OS where
  /-- No copy in progress; `q` waits to be written. -/
  | idle (q : List Val)
  /-- A write of `xs` is in progress; `q` follows. -/
  | busy (xs q : List Val)
  /-- The reader has gone. -/
  | dead
  /-- The writable end has been dropped (`dead`: after the reader had gone). -/
  | closed (dead : Bool)

/-- An output: its state and the ghost list of the items it knows were transferred. -/
structure Out where
  st : OS
  ack : List Val

/-- The state of a node. -/
structure NSt (σ : Type) where
  /-- The transformer's state. -/
  s : σ
  /-- The items read so far. -/
  got : List Val
  rd : RV
  outs : List Out

variable {σ : Type}

/-- Queue `ys` on a live output. -/
def Out.push (ys : List Val) : Out → Out
  | ⟨.idle q, a⟩ => ⟨.idle (q ++ ys), a⟩
  | ⟨.busy xs q, a⟩ => ⟨.busy xs (q ++ ys), a⟩
  | o => o

/-- After a write event (or result) with packed result `p`. -/
def Out.onWrite (o : Out) (p : Nat) : Out :=
  match o.st with
  | .busy xs q =>
    if status p = 0 then ⟨.idle (xs.drop (count p) ++ q), o.ack ++ xs.take (count p)⟩
    else ⟨.dead, o.ack ++ xs.take (count p)⟩
  | .idle _ => if status p = 0 then o else ⟨.dead, o.ack⟩
  | _ => o

/-- After the result `r` of a write of `xs` (then `q`). -/
def Out.afterWrite (xs q ack : List Val) (r : Nat) : Out :=
  if r = blocked then ⟨.busy xs q, ack⟩ else Out.onWrite ⟨.busy xs q, ack⟩ r

/-- After a read event (or result) with packed result `p` delivering `xs`. -/
def NSt.onRead (T : Tr σ Val Val) (x : NSt σ) (p : Nat) (xs : List Val) : NSt σ :=
  { s := (T.feed x.s xs).1, got := x.got ++ xs,
    rd := if status p = 0 then .idle else .ended,
    outs := x.outs.map (Out.push (T.feed x.s xs).2) }

/-- An output that no longer has a reader. -/
def Out.isDead (o : Out) : Prop := o.st = .dead ∨ o.st = .closed true

/-- The node may drop its readable end. -/
def NSt.mayStop (T : Tr σ Val Val) (x : NSt σ) : Prop :=
  x.rd = .ended ∨ (x.rd = .idle ∧ (T.done x.s = true ∨ (x.outs ≠ [] ∧ ∀ o ∈ x.outs, o.isDead)))

/-- After dropping the readable end: `T`'s flush is queued. -/
def NSt.stop (T : Tr σ Val Val) (x : NSt σ) : NSt σ :=
  { x with rd := .gone (decide (x.rd = .ended)), outs := x.outs.map (Out.push (T.flush x.s)) }

/-- **One step of a node** (`ws`: its waitable set). -/
inductive NStep (N : Node) (ws : Nat) : DStore → NSt N.σ → DStore → NSt N.σ → Prop where
  | readBlk {st x c n st'} : N.inp = some c → x.rd = .idle → N.T.done x.s = false → 0 < n →
      dstep st (.streamRead (rh c) n) = some (st', .nat blocked) →
      NStep N ws st x st' { x with rd := .busy }
  | readNow {st x c n st' p ys} : N.inp = some c → x.rd = .idle → N.T.done x.s = false → 0 < n →
      dstep st (.streamRead (rh c) n) = some (st', .read p ys) →
      NStep N ws st x st' (x.onRead N.T p ys)
  | write {st x j c q a n st' r} : N.outs[j]? = some c → x.outs[j]? = some ⟨.idle q, a⟩ →
      0 < n → n ≤ q.length →
      dstep st (.streamWrite (wh c) (q.take n)) = some (st', .nat r) →
      NStep N ws st x st' { x with outs := x.outs.set j (Out.afterWrite (q.take n) (q.drop n) a r) }
  | waitIn {st x c st' e} : N.inp = some c → DWait st ws (rh c) st' e →
      NStep N ws st x st' (x.onRead N.T e.payload e.items)
  | waitOut {st x j c o st' e} : N.outs[j]? = some c → x.outs[j]? = some o →
      DWait st ws (wh c) st' e →
      NStep N ws st x st' { x with outs := x.outs.set j (o.onWrite e.payload) }
  | dropIn {st x c st' r} : N.inp = some c → x.mayStop N.T →
      dstep st (.streamDropR (rh c)) = some (st', r) →
      NStep N ws st x st' (x.stop N.T)
  | dropOut {st x j c a d st' r} : N.outs[j]? = some c → (∃ b, x.rd = .gone b) →
      (x.outs[j]? = some ⟨.idle [], a⟩ ∧ d = false ∨ x.outs[j]? = some ⟨.dead, a⟩ ∧ d = true) →
      dstep st (.streamDropW (wh c)) = some (st', r) →
      NStep N ws st x st' { x with outs := x.outs.set j ⟨.closed d, a⟩ }

/-! ## Systems -/

/-- The shared store and the state of every node. -/
structure Sys (net : Network) where
  st : DStore
  ns : (i : Fin net.k) → NSt (net.node i).σ

/-- **One step of the network**: a step of any one node. -/
inductive Step (net : Network) : Sys net → Sys net → Prop where
  | node {s : Sys net} (i : Fin net.k) {st' x'} :
      NStep (net.node i) (net.ws i) s.st (s.ns i) st' x' →
      Step net s ⟨st', Function.update s.ns i x'⟩

/-- Steps, iterated. -/
inductive Steps (net : Network) : Sys net → Sys net → Prop where
  | refl (s : Sys net) : Steps net s s
  | tail {s s' s'' : Sys net} : Steps net s s' → Step net s' s'' → Steps net s s''

/-- The handle table of a network whose streams are in the states `ch`: the ends not yet
dropped, and the waitable sets. -/
def tblOf (net : Network) (ch : Nat → DChan) (h : Nat) : Option Obj :=
  if h = 0 then none
  else if h ≤ 2 * net.m then
    if h % 2 = 1 then (if (ch h).r.gone then none else some (.streamR h))
    else (if (ch (h - 1)).w.gone then none else some (.streamW (h - 1)))
  else if h ≤ 2 * net.m + net.k then some .wset else none

/-- The waitable-set membership of a network: every end not yet dropped is in its node's set. -/
def joinedOf (net : Network) (ch : Nat → DChan) (h : Nat) : Option Nat :=
  if h = 0 then none
  else if h ≤ 2 * net.m then
    if h % 2 = 1 then (if (ch h).r.gone then none else some (net.ws (net.rd (h / 2))))
    else (if (ch (h - 1)).w.gone then none else some (net.ws (net.wr (h / 2 - 1)).1))
  else none

/-- The store after creating the streams and sets and joining every end to its node's set. -/
def initStore (net : Network) : DStore where
  next := 2 * net.m + 1 + net.k
  tbl := tblOf net fun _ => {}
  chans := fun _ => {}
  joined := joinedOf net fun _ => {}

/-- The initial state of a node: a source has queued its flush. -/
def NSt.init (N : Node) : NSt N.σ where
  s := N.T.init
  got := []
  rd := if N.inp = none then .gone true else .idle
  outs := N.outs.map fun _ => ⟨.idle (if N.inp = none then N.T.flush N.T.init else []), []⟩

/-- The initial system. -/
def init (net : Network) : Sys net := ⟨initStore net, fun i => NSt.init (net.node i)⟩

/-- **The reachable systems.** -/
def Reach (net : Network) (s : Sys net) : Prop := Steps net (init net) s

end Silmaril.Wasm.Component.Streams.Net

module

public import Silmaril.Wasm.JcoTool.KCore.Defs
public import Silmaril.Wasm.Component.Streams.Net.Defs

/-!
# Generated stream modules under the Component Model's drop behaviour

`Silmaril.Wasm.JcoTool.KCore` generates callback-ABI core modules from byte kernels and proves them
correct over the built-ins of `Silmaril.Wasm.Component.Async`. That model lacks two behaviours of
the Component Model (`definitions.py`, `End.drop`, `StreamEnd.notify`, `End.copy`; and wasmtime
50.0.0): **dropping one end posts `DROPPED` on the other end even when it is idle**, after which a
copy on it traps, and **a copy can end `DROPPED` with a nonzero count** (the items copied before
the peer dropped are delivered). `KCore.gen` follows `Proc.tStep`, which has no transition for an
event on an idle end and none out of `TPc.fault` (the reader of its output dropped): in chains of
generated components, wasmtime delivers such events and the module traps (`docs/
wasm-streams.md`, *asyncmodel*).

This module gives the generator `genD` of modules that handle them, with a semantics over the
drop-faithful built-ins of `Silmaril.Wasm.Component.Streams.Drop`:

* **The fragment** is `KCore`'s (`E`, `S`, `Out`, `E.eval`, `lab`, `loopN`); only the built-in
  calls change: `dexec` is `KCore.exec` with `dcallBI` in place of `callBI`, over a state `DSt`
  whose store is a `DStore`. A `stream.read` result must deliver as many items as its count says
  and no more than were asked for (`dcallBI` traps otherwise).
* **The runtime** `DRStep` is `KCore.rstep` with `DWait` (any member of the waitable set with a
  pending event, relationally) in place of `Async.step (.wait s)`; it delivers only well-formed
  events (`wfD`: `KCore.wellFormed`, and a stream-read event delivers `count` items).
* **The generator** `genD k N`: `KCore`'s kernel compilation (`feedLoop`, `flushOut`), and a
  callback written as a state machine over the states of a `Net` node with one input and one
  output: `RD`, `WTR` (read pending), `WTRD` (read pending, output dead), `EOI`, `WR`, `WTW`
  (write pending), `CL`, `FIN`, `DEAD` (drop the input, then close). The global `NXT` says where
  a write continues: `1` reading, `2` at the end of the input, `0` closing. The callback dispatches
  on the event's code and index: a read event (with `DROPPED` and a count, its items are fed) or
  `DROPPED` on the idle input while a write is pending (the input has ended); a write event, or
  `DROPPED` on the idle output while a read is pending (the output is dead: the module waits for
  its read, then drops both ends).

The theorems (`KDrop.Thms`): every step of the runtime from a state related to a `Net` node state
is a step of the node program `Net.NStep` (or a step that changes neither the store nor the
node's state), so `Net`'s network theorems hold for networks whose transformer nodes are these
modules.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KDrop

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res Event EventCode blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (NSt OS RV Node status count)
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore

/-! ## The fragment over the drop-faithful built-ins -/

/-- The state of an invocation: globals, memory, locals, the store, the pending read. -/
structure DSt where
  g : Nat → Nat
  m : Nat → Nat
  l : Nat → Nat
  st : DStore
  rp : Option (Nat × Nat)

/-- The `KCore` state with the same globals, memory, locals and pending read (the `Async`
store is not used by expressions or by statements without calls). -/
def DSt.down (s : DSt) : St := ⟨s.g, s.m, s.l, {}, s.rp, 0⟩

/-- Back from a `KCore` state, with the store `d`. -/
def DSt.up (s : St) (d : DStore) : DSt := ⟨s.g, s.m, s.l, d, s.rp⟩

/-- **The built-ins** `stream.read`, `stream.write` and the drops, over `dstep`, on evaluated
arguments. -/
def dcallBI (b : BI) (as : List Nat) (dst : List Nat) (s : DSt) : Option (KCore.Out × DSt) :=
  match b, as, dst with
  | .streamRead, [h, p, n], [d] =>
    match dstep s.st (.streamRead h n) with
    | some (st', .read code xs) =>
      if code < M32 ∧ code / 16 = xs.length ∧ xs.length ≤ n then
        some (.norm, { s with st := st', m := writeBytes s.m p (xs.map byteOf), l := upd s.l d code })
      else none
    | some (st', .nat r) =>
      if r = blocked then some (.norm, { s with st := st', rp := some (h, p), l := upd s.l d r })
      else none
    | _ => none
  | .streamWrite, [h, p, n], [d] =>
    match dstep s.st (.streamWrite h ((slice s.m p n).map u8v)) with
    | some (st', .nat r) => if r < M32 then some (.norm, { s with st := st', l := upd s.l d r }) else none
    | _ => none
  | .dropR, [h], [] =>
    (dstep s.st (.streamDropR h)).map fun p => (.norm, { s with st := p.1 })
  | .dropW, [h], [] =>
    (dstep s.st (.streamDropW h)).map fun p => (.norm, { s with st := p.1 })
  | _, _, _ => none

/-- **The semantics of statements** with the drop-faithful built-ins: `KCore.exec` with
`dcallBI`. -/
def dexec : S → Nat → DSt → Option (KCore.Out × DSt)
  | .nop, _, s => some (.norm, s)
  | .unreachable, _, _ => none
  | .lset i e, _, s => some (.norm, { s with l := upd s.l i (e.eval s.down) })
  | .gset i e, _, s => some (.norm, { s with g := upd s.g i (e.eval s.down) })
  | .st8 a v, _, s => some (.norm, { s with m := upd s.m (a.eval s.down) (v.eval s.down % 256) })
  | .mcopy d src n, _, s =>
    some (.norm, { s with m := mcopy s.m (d.eval s.down) (src.eval s.down) (n.eval s.down) })
  | .seq a b, f, s =>
    match dexec a f s with
    | some (.norm, s') => dexec b f s'
    | r => r
  | .ite c t e, f, s => dlab (if c.eval s.down ≠ 0 then dexec t f s else dexec e f s)
  | .block b, f, s => dlab (dexec b f s)
  | .loop b, f, s => dloopN (dexec b f) f s
  | .br k, _, s => some (.br k, s)
  | .brIf k c, _, s => if c.eval s.down ≠ 0 then some (.br k, s) else some (.norm, s)
  | .ret e, _, s => some (.ret (e.eval s.down), s)
  | .call b args dst, _, s => dcallBI b (args.map (·.eval s.down)) dst s
where
  /-- `KCore.lab`. -/
  dlab : Option (KCore.Out × DSt) → Option (KCore.Out × DSt)
    | some (.br 0, s') => some (.norm, s')
    | some (.br (k + 1), s') => some (.br k, s')
    | r => r
  /-- `KCore.loopN`. -/
  dloopN (body : DSt → Option (KCore.Out × DSt)) : Nat → DSt → Option (KCore.Out × DSt)
    | 0, _ => none
    | n + 1, s =>
      match body s with
      | some (.br 0, s') => dloopN body n s'
      | some (.br (k + 1), s') => some (.br k, s')
      | r => r

/-! ## The runtime -/

/-- Run `body` with the parameters `ps`; it must `return` a callback code. -/
def dinvoke (body : S) (ps : List Nat) (st : DStore) (ms : MS) : Option (DStore × MS) :=
  match dexec body FUEL ⟨ms.g, ms.m, locals ps, st, ms.rp⟩ with
  | some (.ret code, s') => (modeOf code).map fun md => (s'.st, ⟨s'.g, s'.m, s'.rp, md⟩)
  | _ => none

/-- The events the runtime delivers: `KCore.wellFormed`, and a stream-read event delivers as many
items as its count says. -/
def wfD (e : Event) : Bool :=
  wellFormed e && (e.code != .streamRead || decide (e.payload / 16 = e.items.length))

/-- **One step of the callback runtime**: call the callback after `YIELD`, or take an event of
the waitable set (any member with a pending event) and call the callback with it. -/
inductive DRStep (P : Prog) : DStore → MS → DStore → MS → Prop where
  | ready {st ms st' ms'} : ms.mode = .ready → dinvoke P.cb [0, 0, 0] st ms = some (st', ms') →
      DRStep P st ms st' ms'
  | event {st ms s h st₁ e st' ms'} : ms.mode = .waiting s → DWait st s h st₁ e → wfD e = true →
      dinvoke P.cb [e.code.toNat, e.index, e.payload] st₁ (deliver e ms) = some (st', ms') →
      DRStep P st ms st' ms'

/-! ## The generator -/

/-- The values of `pc` beyond `KCore`'s: wait for the read with a dead output; drop the input of
a dead node. -/
def pWTRD : Nat := 8
def pDEAD : Nat := 7

/-- `NXT` after a read with packed result `p`: `1` (go on reading) on `COMPLETED`, `2` (the input
has ended) otherwise. -/
def nxtOf (p : E) : E := .bin .add (.c 1) (.bin .ne (.bin .remu p (.c 16)) (.c 0))

/-- After a read with packed result `p` (`COMPLETED` or `DROPPED`, with its count of bytes in the
input buffer): feed them, then write the output and continue reading, or end the input. -/
def onReadD (k : KM) (p : E) : S :=
  seqs [.gset NXT (nxtOf p), .lset LN (.bin .divu p (.c 16)), .lset LI (.c 0), feedLoop k,
    .gset PC (.c pWR)]

/-- After a write with packed result `p`: on `COMPLETED` advance the offset; on `DROPPED` the
output is dead: close at once if the input is already dropped (`NXT = 0`), else drop it first. -/
def onWriteD (p : E) : S :=
  .ite (.bin .remu p (.c 16))
    (.ite (.g NXT) (.gset PC (.c pDEAD)) (.gset PC (.c pCL)))
    (seqs [.lset LN (.bin .divu p (.c 16)),
      .ite (.bin .geu (.l LN) (.bin .sub (.g OLEN) (.g OOFF))) (.gset OOFF (.g OLEN))
        (.gset OOFF (.bin .add (.g OOFF) (.l LN))),
      .gset PC (.c pWR)])

/-- `l = v`. -/
def isE (a : E) (v : Nat) : E := .bin .eq a (.c v)

/-- `a ∧ b` on `0/1` values. -/
def andE (a b : E) : E := .eqz (.bin .add (.eqz a) (.eqz b))

/-- The event is a read event of the input. -/
def evIn : E := andE (isE (.l 0) 2) (.bin .eq (.l 1) (.g INSR))

/-- The event is a write event of the output. -/
def evOut : E := andE (isE (.l 0) 3) (.bin .eq (.l 1) (.g OUTSW))

/-- The event is `DROPPED` (a nonzero status). -/
def evDropped : E := .bin .ne (.bin .remu (.l 2) (.c 16)) (.c 0)

/-- The event is `DROPPED` with a count of `0`. -/
def evDropped0 : E := andE evDropped (isE (.bin .divu (.l 2) (.c 16)) 0)

/-- `RD`: stop when the kernel is done, else read up to `N` bytes. Every case of the callback is
a tree of `if`s whose every branch ends in `return` or `unreachable`. -/
def dRD (k : KM) (N : Nat) : S :=
  .seq (.lset LB (.c 0))
    (.ite (cE k.done) (seqs [.call .dropR [.g INSR] [], flushOut k, yield_])
      (.seq (.call .streamRead [.g INSR, .c IN, .c N] [LR])
        (.ite (isE (.l LR) blocked) (.seq (.gset PC (.c pWTR)) (.ret waitCode))
          (.seq (onReadD k (.l LR)) yield_))))

/-- `WTR`: the read's event, or `DROPPED` on the idle output (then wait for the read). -/
def dWTR (k : KM) : S :=
  .ite evIn (.seq (onReadD k (.l 2)) yield_)
    (.ite (andE evOut evDropped) (.seq (.gset PC (.c pWTRD)) (.ret waitCode)) .unreachable)

/-- `WTRD`: the read's event; then drop both ends. -/
def dWTRD : S := .ite evIn (.seq (.gset PC (.c pDEAD)) yield_) .unreachable

/-- `EOI`: drop the input, run the flush. -/
def dEOI (k : KM) : S := seqs [.call .dropR [.g INSR] [], flushOut k, yield_]

/-- `DEAD`: drop the input; then close. -/
def dDEAD : S := seqs [.call .dropR [.g INSR] [], .gset PC (.c pCL), yield_]

/-- Where a written output continues: `NXT = 1` reading, `2` at the end of the input, else
closing. -/
def nextPC : S :=
  .ite (isE (.g NXT) 1) (.gset PC (.c pRD)) (.ite (isE (.g NXT) 2) (.gset PC (.c pEOI)) (.gset PC (.c pCL)))

/-- `WR`: continue when the output is written, else write the rest. -/
def dWR : S :=
  .ite (.bin .geu (.g OOFF) (.g OLEN))
    (seqs [.gset OOFF (.c 0), .gset OLEN (.c 0), nextPC, yield_])
    (.seq (.call .streamWrite [.g OUTSW, .bin .add (.c OUT) (.g OOFF), .bin .sub (.g OLEN) (.g OOFF)] [LR])
      (.ite (isE (.l LR) blocked) (.seq (.gset PC (.c pWTW)) (.ret waitCode))
        (.seq (onWriteD (.l LR)) yield_)))

/-- `WTW`: the write's event, or `DROPPED` (count `0`) on the idle input while reading
(`NXT = 1`): the input has ended; wait again. -/
def dWTW : S :=
  .ite evOut (.seq (onWriteD (.l 2)) yield_)
    (.ite (andE (andE evIn evDropped0) (isE (.g NXT) 1)) (.seq (.gset NXT (.c 2)) (.ret waitCode))
      .unreachable)

/-- `CL`: drop the output and exit. -/
def dCL : S := seqs [.call .dropW [.g OUTSW] [], .gset PC (.c pFIN), .ret (.c 0)]

/-- **The callback** of the generated module: a dispatch on `pc`. -/
def callbackD (k : KM) (N : Nat) : S :=
  .ite (pcIs pWTR) (dWTR k) <| .ite (pcIs pWTW) dWTW <| .ite (pcIs pRD) (dRD k N) <|
    .ite (pcIs pEOI) (dEOI k) <| .ite (pcIs pWR) dWR <| .ite (pcIs pCL) dCL <|
    .ite (pcIs pDEAD) dDEAD <| .ite (pcIs pWTRD) dWTRD .unreachable

/-- **The core module generated from the kernel `k`**, reading up to `N` bytes at a time: the
lift of `KCore` (result stream, waitable set, `task.return`, joins) and the callback above. -/
def genD (k : KM) (N : Nat) : Prog := ⟨entry, callbackD k N, initG k⟩

/-- The machine after the lift, in a network: input readable end `r`, output writable end `w`,
waitable set `s`. -/
def initMSD (k : KM) (r w s : Nat) : MS :=
  ⟨upd (upd (upd (initG k) INSR r) OUTSW w) WS s, fun _ => 0, none, .ready⟩

/-! ## The relation with a `Net` node -/

/-- The handles and the bounds of the buffers. -/
def okD (ms : MS) (r w s : Nat) : Prop :=
  ms.g INSR = r ∧ ms.g OUTSW = w ∧ ms.g WS = s ∧ ms.g BLEN ≤ CAP ∧ ms.g OLEN ≤ CAP ∧
    ms.g OOFF ≤ ms.g OLEN

/-- The output is queued `q`, or dead. -/
def outIs (x : NSt KSt) (st : OS) : Prop := ∃ a, x.outs = [⟨st, a⟩]

/-- Where a write continues, and the input side it stands for. -/
def NxtRel (ms : MS) (x : NSt KSt) : Prop :=
  (ms.g NXT = 1 ∧ x.rd = .idle ∧ ms.kst = x.s) ∨ (ms.g NXT = 2 ∧ x.rd = .ended ∧ ms.kst = x.s) ∨
    (ms.g NXT = 0 ∧ ∃ b, x.rd = .gone b)

/-- The cases of `RelD` for a running machine, by its `pc`. -/
def RelL (r s : Nat) (ms : MS) (x : NSt KSt) : Prop :=
    ((ms.mode = .ready ∧ ms.g PC = pRD ∧ ms.kst = x.s ∧ ms.g OLEN = 0 ∧ ms.g OOFF = 0 ∧
        x.rd = .idle ∧ outIs x (.idle [])) ∨
     (ms.mode = .waiting s ∧ ms.g PC = pWTR ∧ ms.kst = x.s ∧ ms.g OLEN = 0 ∧ ms.g OOFF = 0 ∧
        ms.rp = some (r, IN) ∧ x.rd = .busy ∧ outIs x (.idle [])) ∨
     (ms.mode = .waiting s ∧ ms.g PC = pWTRD ∧ ms.rp = some (r, IN) ∧ x.rd = .busy ∧
        outIs x .dead) ∨
     (ms.mode = .ready ∧ ms.g PC = pEOI ∧ ms.kst = x.s ∧ x.rd = .ended ∧ outIs x (.idle [])) ∨
     (ms.mode = .ready ∧ ms.g PC = pWR ∧ outIs x (.idle ms.pending) ∧ NxtRel ms x) ∨
     (ms.mode = .waiting s ∧ ms.g PC = pWTW ∧ outIs x (.busy ms.pending []) ∧ NxtRel ms x ∧
        ms.pending ≠ []) ∨
     (ms.mode = .ready ∧ ms.g PC = pCL ∧ (∃ b, x.rd = .gone b) ∧
        (outIs x (.idle []) ∨ outIs x .dead)) ∨
     (ms.mode = .ready ∧ ms.g PC = pDEAD ∧ (x.rd = .idle ∨ x.rd = .ended) ∧ outIs x .dead))

/-- **The simulation relation** between the machine and the state of a `Net` node with one input
(readable end `r`) and one output (writable end `w`), waiting on the set `s`. -/
def RelD (r w s : Nat) (ms : MS) (x : NSt KSt) : Prop :=
  if ms.mode = .exited then ∃ b, x.rd = .gone b ∧ ∃ d, outIs x (.closed d)
  else okD ms r w s ∧ RelL r s ms x


/-- A node with one input and one output, running the kernel over `u8` values. -/
def node (k : KM) (c c' : Nat) : Node := ⟨KSt, trV k, some c, [c']⟩

/-! ## Chains of generated modules -/

open Silmaril.Wasm.Component.Streams.Net (Network Sys initStore NStep rh wh)

/-- A source of `xs`, over `KSt`: reads nothing, emits `xs` at the end. -/
def srcK (xs : List Val) : Tr KSt Val Val := ⟨⟨0, []⟩, fun s _ => (s, []), fun _ => xs, fun _ => false⟩

/-- A sink, over `KSt`. -/
def sinkK : Tr KSt Val Val := ⟨⟨0, []⟩, fun s _ => (s, []), fun _ => [], fun _ => false⟩

/-- The transformer of node `i` of a chain: the source, the kernels, the sink. -/
def chainT (xs : List Val) (ks : List KM) (i : Nat) : Tr KSt Val Val :=
  if i = 0 then srcK xs else match ks[i - 1]? with
    | some k => trV k
    | none => sinkK

/-- **Source → kernels `ks` → sink**: node `i` writes stream `i`, which node `i + 1` reads. -/
def kchain (xs : List Val) (ks : List KM) : Network where
  k := ks.length + 2
  node i := ⟨KSt, chainT xs ks i.val, if i.val = 0 then none else some (i.val - 1),
    if i.val = ks.length + 1 then [] else [i.val]⟩
  m := ks.length + 1
  wr c := (⟨c % (ks.length + 2), Nat.mod_lt _ (by omega)⟩, 0)
  rd c := ⟨(c + 1) % (ks.length + 2), Nat.mod_lt _ (by omega)⟩

/-- A chain whose kernels run as generated modules: the store, the source and the sink (`Net`
nodes) and the machine of every module. -/
structure KSys (n : Nat) where
  st : DStore
  src : NSt KSt
  ms : Fin n → MS
  snk : NSt KSt

/-- One step of the source, of a module (with read size `Nb i`), or of the sink. -/
inductive KStep (xs : List Val) (ks : List KM) (Nb : Nat → Nat) : KSys ks.length → KSys ks.length → Prop
  | src {c : KSys ks.length} {st' x'} :
      NStep ((kchain xs ks).node ⟨0, by simp [kchain]⟩) ((kchain xs ks).ws 0) c.st c.src st' x' →
      KStep xs ks Nb c { c with st := st', src := x' }
  | mod {c : KSys ks.length} {st' m'} (i : Fin ks.length) :
      DRStep (genD (ks.get i) (Nb i)) c.st (c.ms i) st' m' →
      KStep xs ks Nb c { c with st := st', ms := Function.update c.ms i m' }
  | snk {c : KSys ks.length} {st' x'} :
      NStep ((kchain xs ks).node ⟨ks.length + 1, by simp [kchain]⟩) ((kchain xs ks).ws (ks.length + 1))
        c.st c.snk st' x' →
      KStep xs ks Nb c { c with st := st', snk := x' }

/-- Steps, iterated. -/
inductive KSteps (xs : List Val) (ks : List KM) (Nb : Nat → Nat) : KSys ks.length → KSys ks.length → Prop
  | refl (c : KSys ks.length) : KSteps xs ks Nb c c
  | tail {c c' c''} : KSteps xs ks Nb c c' → KStep xs ks Nb c' c'' → KSteps xs ks Nb c c''

/-- The start: the network's setup store, every module after its lift. -/
def KSys.init (xs : List Val) (ks : List KM) : KSys ks.length where
  st := initStore (kchain xs ks)
  src := NSt.init ((kchain xs ks).node ⟨0, by simp [kchain]⟩)
  ms i := initMSD (ks.get i) (rh i) (wh (i + 1)) ((kchain xs ks).ws (i + 1))
  snk := NSt.init ((kchain xs ks).node ⟨ks.length + 1, by simp [kchain]⟩)

/-- The reachable systems. -/
def KReach (xs : List Val) (ks : List KM) (Nb : Nat → Nat) (c : KSys ks.length) : Prop :=
  KSteps xs ks Nb (KSys.init xs ks) c

/-- The composite: the kernels' runs, in order. -/
def runs (ks : List KM) (xs : List Val) : List Val := ks.foldl (fun a k => (trV k).run a) xs

end Silmaril.Wasm.JcoTool.KDrop

module

public import Silmaril.Wasm.JcoTool.KDrop.Defs
public import Silmaril.Wasm.JcoTool.KCoreEmit.Defs
public import Silmaril.Wasm.FX.Asyncify.Tool.Core.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation

/-!
# The KCore/KDrop fragment on silmaril-lean's Core 3.0 `Step`, with the built-ins as host calls

`Silmaril.Wasm.JcoTool.KDrop` gives the generated stream modules (`genD k N`) a big-step
semantics `dexec` over a fragment of WebAssembly, with the canonical built-ins over the
drop-faithful store `Streams.Drop.DStore`. `Silmaril.Wasm.JcoTool.KCoreEmit.toModule` is the
Core 3.0 module the emitted bytes encode, with each construct as the instruction sequence
`sCode`/`eCode`. This module states what it means for that code to run, under **Core 3.0's
small-step `Step`** (the semantics the component reference machine runs core code with), as
`dexec` says, including the built-in calls:

* **The host state** `HQ`: the drop store and the pending read (`DSt.st`, `DSt.rp`): what
  the canonical built-ins of the component machine keep outside the core instance.
* **The built-ins on bytes**, `bi`: `dcallBI` without the locals (its result values are
  returned), on a byte memory `Nat → Nat`; `bans ma`: the same as an answer of a Core host
  function, on the Core store: it reads memory `ma` (the instance's memory, which the
  canonical ABI options name), and writes back the bytes `bi` leaves (`encMem`).
* **`HStep hb ma`**: Core 3.0 reduction with the built-ins as host calls: a Core step under
  the empty host (`core`), or the host-call redex of a function whose code is `.host (hb b)`,
  answered by `bans ma b` in the current host state (`host`), in every evaluation context
  (`instrs`, `label`, `frame`). Each `HStep` is a Core `Step` against the stateless host
  `hostAt hb ma q q'` of its host-state transition (`KCoreRun.Thms`, `hstep_core`).
* **The checked semantics** `bexec nl`: `dexec` with the conditions under which Core does not
  trap where the fragment does not: divisors are nonzero, loads and stores are below `MSZ`
  (the module's two pages), `memory.copy` copies forward (`d ≤ s`) within memory, local
  indices are below `nl`, global indices below `9`, branch depths below `2 ^ 32`, the
  built-ins' buffers lie in memory. `bexec_dexec`: it agrees with `dexec` where it is
  defined.
* **The relation** `Rel nl ma cs F s`: the Core frame `F` holds the `i32` locals `0..nl-1`,
  the store `cs` the nine globals (`GlobalsAre`) and, at address `ma`, memory `0` of `MSZ`
  bytes with `s.m` below `MSZ`; the imported functions `0..7` are the host functions
  `hb b` with the types of `KCoreEmit.types`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Component.Async (blocked)
open Silmaril.Wasm.Component.Streams.Drop (DStore dstep)
open Silmaril.Wasm.JcoTool.KCore (E Bin S BI Out M32 upd slice writeBytes mcopy byteOf u8v)
open Silmaril.Wasm.JcoTool.KDrop (DSt dexec)
open Silmaril.Wasm.JcoTool.KCoreEmit (ix biFn sCode eCode)
open Silmaril.Wasm.FX.Asyncify.Tool (W GlobalsAre stackA)

/-- Bytes of the memory of the generated modules (two pages). -/
def MSZ : Nat := 2 * 65536

/-- Globals of the generated modules. -/
def NG : Nat := 9

/-- The `i32` of a number. -/
abbrev w (n : Nat) : W := BitVec.ofNat 32 n

/-! ## The host state and the built-ins on bytes -/

/-- The host state: the drop store and the pending read. -/
abbrev HQ := DStore × Option (Nat × Nat)

/-- **The built-ins** `stream.read`, `stream.write` and the drops on a byte memory: `dcallBI`
with its results returned instead of stored in locals. -/
def bi (b : BI) (as : List Nat) (q : HQ) (m : Nat → Nat) : Option (HQ × (Nat → Nat) × List Nat) :=
  match b, as with
  | .streamRead, [h, p, n] =>
    match dstep q.1 (.streamRead h n) with
    | some (st', .read code xs) =>
      if code < M32 ∧ code / 16 = xs.length ∧ xs.length ≤ n then
        some ((st', q.2), writeBytes m p (xs.map byteOf), [code])
      else none
    | some (st', .nat r) => if r = blocked then some ((st', some (h, p)), m, [r]) else none
    | _ => none
  | .streamWrite, [h, p, n] =>
    match dstep q.1 (.streamWrite h ((slice m p n).map u8v)) with
    | some (st', .nat r) => if r < M32 then some ((st', q.2), m, [r]) else none
    | _ => none
  | .dropR, [h] => (dstep q.1 (.streamDropR h)).map fun p => ((p.1, q.2), m, [])
  | .dropW, [h] => (dstep q.1 (.streamDropW h)).map fun p => ((p.1, q.2), m, [])
  | _, _ => none

/-- The buffer of a `stream.read`/`stream.write` lies in the first `sz` bytes. -/
def memOK (sz : Nat) : BI → List Nat → Bool
  | .streamRead, [_, p, n] => decide (p + n ≤ sz)
  | .streamWrite, [_, p, n] => decide (p + n ≤ sz)
  | _, _ => true

/-- A Core memory's bytes as a byte function (`0` past its end). -/
def memOf (mi : MemInst) : Nat → Nat := fun a =>
  if h : a < mi.bytes.size then (mi.bytes[a]'h).toNat else 0

/-- The first `sz` bytes of a byte function, as a Core memory's bytes. -/
def encMem (sz : Nat) (m : Nat → Nat) : ByteArray :=
  ⟨(Array.range sz).map fun a => UInt8.ofNat (m a)⟩

variable {H : Type}

/-- **A built-in as a Core host function**: the answer to the call of `b` on the `i32`s `args`
in host state `q`, with memory `ma` of the store `s`: the new host state, the store with the
bytes `bi` leaves in memory `ma`, the results. -/
def bans (ma : Nat) (b : BI) (q : HQ) (s : Store H) (args : List W) :
    Option (HQ × Store H × List W) := do
  let mi ← s.mems[ma]?
  let as := args.map BitVec.toNat
  if memOK mi.bytes.size b as then
    let (q', m', res) ← bi b as q (memOf mi)
    pure (q', s.setMem ma { mi with bytes := encMem mi.bytes.size m' }, res.map w)
  else none

/-- The stateless Core host of one host-state transition `q → q'`: the host function `hb b`
answers as `bans ma b` does from `q`, moving to `q'`. -/
def hostAt (hb : BI → H) (ma : Nat) (q q' : HQ) : HostSemantics H := fun h s vs out =>
  ∃ b args s' res, h = hb b ∧ vs = args.map Val.i32 ∧ bans ma b q s args = some (q', s', res) ∧
    out = .returned s' (.values (res.map Val.i32))

/-- **Core 3.0 reduction with the built-ins as host calls**, on the host state and a Core
configuration. -/
inductive HStep (Pf : Numerics.Profile) (hb : BI → H) (ma : Nat) :
    HQ × Config H → HQ × Config H → Prop where
  /-- A Core step under the empty host. -/
  | core {q : HQ} {C C' : Config H} (h : Step Pf (fun _ _ _ _ => False) C C') :
      HStep Pf hb ma (q, C) (q, C')
  /-- The call of the host function `hb b`, answered by `bans ma b` (Core's `callRefHost`). -/
  | host {q q' : HQ} {s s' : Store H} {f : Frame} {c : Admin} {args res : List W} {a : Nat}
      {fi : FuncInst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} {b : BI}
      (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
      (hn : args.length = ps.length) (hcode : fi.code = .host (hb b))
      (hans : bans ma b q s args = some (q', s', res)) :
      HStep Pf hb ma (q, ⟨s, f, vals (args.map Val.i32) ++ [.ref (.func a), c]⟩)
        (q', ⟨s', f, vals (res.map Val.i32)⟩)
  /-- `Step/ctxt-instrs`. -/
  | instrs {q q' : HQ} {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
      (h : HStep Pf hb ma (q, ⟨s, f, is⟩) (q', ⟨s', f', is'⟩)) (hne : vs ≠ [] ∨ rest ≠ []) :
      HStep Pf hb ma (q, ⟨s, f, vals vs ++ is ++ rest⟩) (q', ⟨s', f', vals vs ++ is' ++ rest⟩)
  /-- `Step/ctxt-label`. -/
  | label {q q' : HQ} {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
      {is is' : List Admin} (h : HStep Pf hb ma (q, ⟨s, f, is⟩) (q', ⟨s', f', is'⟩)) :
      HStep Pf hb ma (q, ⟨s, f, [.label n cont is]⟩) (q', ⟨s', f', [.label n cont is']⟩)
  /-- `Step/ctxt-frame`. -/
  | frame {q q' : HQ} {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
      (h : HStep Pf hb ma (q, ⟨s, fi, is⟩) (q', ⟨s', fi', is'⟩)) :
      HStep Pf hb ma (q, ⟨s, f, [.frame n fi is]⟩) (q', ⟨s', f, [.frame n fi' is']⟩)

/-- `HStep`, iterated. -/
abbrev HSteps (Pf : Numerics.Profile) (hb : BI → H) (ma : Nat) :=
  Relation.ReflTransGen (HStep Pf hb ma)

/-! ## The checked semantics -/

/-- The value of an expression where Core computes it without trapping: locals below `nl`,
globals below `NG`, nonzero divisors, loads below `MSZ`. -/
def cev (nl : Nat) (s : DSt) : E → Option Nat
  | .c n => some (n % M32)
  | .l i => if i < nl then some (s.l i) else none
  | .g i => if i < NG then some (s.g i) else none
  | .bin o a b => do
    let x ← cev nl s a
    let y ← cev nl s b
    if (o = .divu ∨ o = .remu) ∧ y = 0 then none else some (o.eval x y)
  | .eqz a => (cev nl s a).map fun x => if x = 0 then 1 else 0
  | .ld8 a => do
    let x ← cev nl s a
    if x < MSZ then some (s.m x) else none

/-- Set the locals `ds` to the values `vs`. -/
def setLs (l : Nat → Nat) : List Nat → List Nat → Nat → Nat
  | d :: ds, v :: vs => setLs (upd l d v) ds vs
  | _, _ => l

/-- A built-in call where Core runs it: the arguments' values, the buffer in memory, as many
result locals as results, all below `nl`, results below `2 ^ 32`. -/
def bcall (nl : Nat) (b : BI) (as : List Nat) (dst : List Nat) (s : DSt) : Option (Out × DSt) :=
  if memOK MSZ b as then
    match bi b as (s.st, s.rp) s.m with
    | some (q', m', res) =>
      if dst.length = res.length ∧ (∀ d ∈ dst, d < nl) ∧ (∀ r ∈ res, r < M32) then
        some (.norm, { s with st := q'.1, rp := q'.2, m := m', l := setLs s.l dst res })
      else none
    | none => none
  else none

/-- **The checked semantics**: `dexec` where Core does not trap. -/
def bexec (nl : Nat) : S → Nat → DSt → Option (Out × DSt)
  | .nop, _, s => some (.norm, s)
  | .unreachable, _, _ => none
  | .lset i e, _, s =>
    if i < nl then (cev nl s e).map fun v => (.norm, { s with l := upd s.l i v }) else none
  | .gset i e, _, s =>
    if i < NG then (cev nl s e).map fun v => (.norm, { s with g := upd s.g i v }) else none
  | .st8 a v, _, s => do
    let x ← cev nl s a
    let y ← cev nl s v
    if x < MSZ then some (.norm, { s with m := upd s.m x (y % 256) }) else none
  | .mcopy d src n, _, s => do
    let x ← cev nl s d
    let y ← cev nl s src
    let z ← cev nl s n
    if x ≤ y ∧ y + z ≤ MSZ then some (.norm, { s with m := mcopy s.m x y z }) else none
  | .seq a b, f, s =>
    match bexec nl a f s with
    | some (.norm, s') => bexec nl b f s'
    | r => r
  | .ite c t e, f, s =>
    match cev nl s c with
    | some v => dexec.dlab (if v ≠ 0 then bexec nl t f s else bexec nl e f s)
    | none => none
  | .block b, f, s => dexec.dlab (bexec nl b f s)
  | .loop b, f, s => dexec.dloopN (bexec nl b f) f s
  | .br k, _, s => if k < M32 then some (.br k, s) else none
  | .brIf k c, _, s =>
    if k < M32 then (cev nl s c).map fun v => if v ≠ 0 then (.br k, s) else (.norm, s) else none
  | .ret e, _, s => (cev nl s e).map fun v => (.ret v, s)
  | .call b args dst, _, s => do
    let as ← args.mapM (cev nl s)
    bcall nl b as dst s

/-! ## The relation with a Core configuration -/

/-- The `i32` globals of a state. -/
def gsOf (g : Nat → Nat) : List W := (List.range NG).map fun i => w (g i)

/-- The import types of the built-ins (`KCoreEmit.types`): arity of the parameters. -/
def arity : BI → Nat
  | .streamRead => 3
  | .streamWrite => 3
  | .dropR => 1
  | .dropW => 1
  | .taskReturn => 1
  | .join => 2
  | _ => 0

/-- The arities of the built-ins when `task.return` takes `n` values. -/
def arityN (n : Nat) : BI → Nat
  | .taskReturn => n
  | b => arity b

/-- **The relation**: locals, globals, memory, imports (`task.return`'s arity is left open: see
`RetAt`). -/
structure Rel (hb : BI → H) (nl ma : Nat) (cs : Store H) (F : Frame) (s : DSt) : Prop where
  nl32 : nl ≤ M32
  loc : ∀ i, i < nl → F.locals[i]? = some (some (Val.i32 (w (s.l i)))) ∧ s.l i < M32
  glob : GlobalsAre cs F (gsOf s.g)
  glt : ∀ i, i < NG → s.g i < M32
  mem : ∃ mi, F.module.mems[0]? = some ma ∧ cs.mems[ma]? = some mi ∧ mi.bytes.size = MSZ ∧
    ∀ a (h : a < mi.bytes.size), (mi.bytes[a]'h).toNat = s.m a
  imp : ∀ b, ∃ a fi ps rs, F.module.funcs[biFn b]? = some a ∧ cs.funcs[a]? = some fi ∧
    fi.code = .host (hb b) ∧ Expand fi.type (.func ps rs) ∧ (b ≠ .taskReturn → ps.length = arity b)


/-! ## Invocations of the callback -/

/-- **The instance part of `Rel`**: the globals, memory `0` and imported built-ins of the module
instance `mi` in the store `cs` hold `g` and `m`. -/
structure InstR (hb : BI → H) (ma : Nat) (cs : Store H) (mi : ModuleInst) (g m : Nat → Nat) :
    Prop where
  glob : GlobalsAre cs ⟨[], mi⟩ (gsOf g)
  glt : ∀ i, i < NG → g i < M32
  mem : ∃ x, mi.mems[0]? = some ma ∧ cs.mems[ma]? = some x ∧ x.bytes.size = MSZ ∧
    ∀ a (h : a < x.bytes.size), (x.bytes[a]'h).toNat = m a
  imp : ∀ b, ∃ a fi ps rs, mi.funcs[biFn b]? = some a ∧ cs.funcs[a]? = some fi ∧
    fi.code = .host (hb b) ∧ Expand fi.type (.func ps rs) ∧ (b ≠ .taskReturn → ps.length = arity b)

/-- **The `task.return` import takes `n` values**: the instance `mi`'s import of `task.return` is
the host function `hb .taskReturn` with `n` parameters. `Rel` and `InstR` leave this arity open
(the callback never calls `task.return`), so the lift of a module returning one stream (`n = 1`,
`KCore.entry`) and the lift of the tee returning two (`n = 2`, `KTee.entryT`) share them. -/
def RetAt (hb : BI → H) (cs : Store H) (mi : ModuleInst) (n : Nat) : Prop :=
  ∃ a fi ps rs, mi.funcs[biFn .taskReturn]? = some a ∧ cs.funcs[a]? = some fi ∧
    fi.code = .host (hb .taskReturn) ∧ Expand fi.type (.func ps rs) ∧ ps.length = n

/-- The callback's declared locals (`KCoreEmit.toModule`): four `i32`, one `i64`. -/
def cbLocals : List ValType := [KCoreEmit.i32, KCoreEmit.i32, KCoreEmit.i32, KCoreEmit.i32, KCoreEmit.i64]

/-- The `i32` locals of the callback: its three parameters and four locals. -/
def CBL : Nat := 7

/-- **The store holds the callback of `P`** at function address `a`, in module instance `mi`, with
the code `KCoreEmit.toModule` gives it (`sCode P.cb`, then `unreachable`). -/
def CbAt (cs : Store H) (mi : ModuleInst) (P : Silmaril.Wasm.JcoTool.KCore.Prog) (a : Nat) : Prop :=
  ∃ fi ty ps rs, cs.funcs[a]? = some fi ∧ fi.module = mi ∧
    fi.code = .wasm ⟨ty, cbLocals, sCode P.cb ++ [.unreachable]⟩ ∧ Expand fi.type (.func ps rs) ∧
    ps.length = 3 ∧ rs.length = 1


/-! ## The callback runtime on Core 3.0 -/

/-- **The runtime's delivery of a completed read on Core**: the items written into memory `ma`
at the pending read's buffer (`KCore.deliver`, on the Core store). -/
def deliverC (ma : Nat) (cs : Store H) (e : Silmaril.Wasm.Component.Async.Event)
    (rp : Option (Nat × Nat)) : Store H × Option (Nat × Nat) :=
  match e.code, rp with
  | .streamRead, some (h, p) =>
    if h = e.index then
      match cs.mems[ma]? with
      | some mi =>
        (cs.setMem ma { mi with bytes := encMem mi.bytes.size (writeBytes (memOf mi) p (e.items.map byteOf)) },
          none)
      | none => (cs, rp)
    else (cs, rp)
  | _, _ => (cs, rp)

/-- **One step of the callback runtime on Core 3.0**, over the host state, the Core store, the
pending read and the runtime's mode: after `YIELD`, the Core invocation of the callback (at
function address `a`) with no event; after `WAIT`, an event of the waitable set (`DWait`), its
items delivered into memory, then the invocation with the event. The callback's result is the
next mode (`KCore.modeOf`). -/
inductive CRStep (Pf : Numerics.Profile) (hb : BI → H) (ma a : Nat) :
    DStore × Store H × Option (Nat × Nat) × Silmaril.Wasm.JcoTool.KCore.Mode →
      DStore × Store H × Option (Nat × Nat) × Silmaril.Wasm.JcoTool.KCore.Mode → Prop where
  | ready {st st' : DStore} {cs cs' : Store H} {rp rp' : Option (Nat × Nat)} {code : Nat}
      {md : Silmaril.Wasm.JcoTool.KCore.Mode}
      (hrun : HSteps Pf hb ma ((st, rp), invoke cs a ([0, 0, 0].map (Val.i32 ∘ w)))
        ((st', rp'), ⟨cs', {}, vals [Val.i32 (w code)]⟩))
      (hmd : Silmaril.Wasm.JcoTool.KCore.modeOf code = some md) :
      CRStep Pf hb ma a (st, cs, rp, .ready) (st', cs', rp', md)
  | event {st st₁ st' : DStore} {cs cs₁ cs' : Store H} {rp rp₁ rp' : Option (Nat × Nat)}
      {s h code : Nat} {e : Silmaril.Wasm.Component.Async.Event} {md : Silmaril.Wasm.JcoTool.KCore.Mode}
      (hw : Silmaril.Wasm.Component.Streams.Drop.DWait st s h st₁ e)
      (hwf : Silmaril.Wasm.JcoTool.KDrop.wfD e = true) (hd : deliverC ma cs e rp = (cs₁, rp₁))
      (hrun : HSteps Pf hb ma ((st₁, rp₁), invoke cs₁ a ([e.code.toNat, e.index, e.payload].map (Val.i32 ∘ w)))
        ((st', rp'), ⟨cs', {}, vals [Val.i32 (w code)]⟩))
      (hmd : Silmaril.Wasm.JcoTool.KCore.modeOf code = some md) :
      CRStep Pf hb ma a (st, cs, rp, .waiting s) (st', cs', rp', md)

/-- The parameters the runtime calls the callback with: no event, or a well-formed event. -/
def ParamsOK (ps : List Nat) : Prop :=
  ps = [0, 0, 0] ∨ ∃ e : Silmaril.Wasm.Component.Async.Event,
    Silmaril.Wasm.JcoTool.KDrop.wfD e = true ∧ ps = [e.code.toNat, e.index, e.payload]

/-- **Where Core does not trap where `dexec` does not**: every successful `dexec` run of the
callback with the globals `g`, any memory, host state and pending read, and parameters the
runtime gives, is a `bexec` run. -/
def CbSafe (P : Silmaril.Wasm.JcoTool.KCore.Prog) (g : Nat → Nat) : Prop :=
  ∀ (ps : List Nat) (m : Nat → Nat) (st : DStore) (rp : Option (Nat × Nat))
    (r : Out × DSt), ParamsOK ps → dexec P.cb Silmaril.Wasm.JcoTool.KCore.FUEL ⟨g, m, Silmaril.Wasm.JcoTool.KCore.locals ps, st, rp⟩ = some r →
    bexec CBL P.cb Silmaril.Wasm.JcoTool.KCore.FUEL ⟨g, m, Silmaril.Wasm.JcoTool.KCore.locals ps, st, rp⟩ = some r

/-- The code a statement ends with: nothing, a branch, or a return of a value. -/
def outCode : Out → List Admin
  | .norm => []
  | .br k => [.plain (.br (ix k))]
  | .ret v => [(Val.i32 (w v)).toAdmin, .plain .return_]

/-! ## Instantiation of the emitted module -/

/-- **The imports of `KCoreEmit.toModule`, supplied as host functions**: the addresses `as` of the
eight imported built-ins, in `KCoreEmit.biFn` order, each the host function `hb b` of its arity. -/
def ImpsOK (hb : BI → H) (s : Store H) (as : List Nat) : Prop :=
  as.length = 8 ∧ ∀ b, ∃ a fi ps rs, as[biFn b]? = some a ∧ s.funcs[a]? = some fi ∧
    fi.code = .host (hb b) ∧ Expand fi.type (.func ps rs) ∧ ps.length = arity b

/-- **`ImpsOK` with `task.return` of `n` values** (`ImpsOK` is `n = 1`; the tee's is `n = 2`). -/
def ImpsOKN (n : Nat) (hb : BI → H) (s : Store H) (as : List Nat) : Prop :=
  as.length = 8 ∧ ∀ b, ∃ a fi ps rs, as[biFn b]? = some a ∧ s.funcs[a]? = some fi ∧
    fi.code = .host (hb b) ∧ Expand fi.type (.func ps rs) ∧ ps.length = arityN n b

/-- The lift's declared locals (`KCoreEmit.toModule`): six `i32`, one `i64`. -/
def entryLocals : List ValType :=
  [KCoreEmit.i32, KCoreEmit.i32, KCoreEmit.i32, KCoreEmit.i32, KCoreEmit.i32, KCoreEmit.i32, KCoreEmit.i64]

/-- **The store holds the lift of `P`** (`[async-lift]name`) at function address `a`, in module
instance `mi`, with the code `KCoreEmit.toModule` gives it (`sCode P.entry`, then `unreachable`). -/
def EntryAt (cs : Store H) (mi : ModuleInst) (P : Silmaril.Wasm.JcoTool.KCore.Prog) (a : Nat) : Prop :=
  ∃ fi ty ps rs, cs.funcs[a]? = some fi ∧ fi.module = mi ∧
    fi.code = .wasm ⟨ty, entryLocals, sCode P.entry ++ [.unreachable]⟩ ∧ Expand fi.type (.func ps rs) ∧
    ps.length = 1 ∧ rs.length = 1

/-! ## The lift: the `Async` built-ins as Core host functions -/

/-- The host state of the lift and the runtime: the drop store, the pending read, and the values
the task returned (`task.return`). -/
abbrev HL := HQ × List Nat

/-- The `i32` values of a list of Core values (`none` if one is not an `i32`). -/
def i32s? : List Val → Option (List W)
  | [] => some []
  | .num ⟨.int .i32, x⟩ :: vs => (i32s? vs).map (x :: ·)
  | _ :: _ => none

/-- **The lift's built-ins** on the host state: `stream.new` (a fresh stream in the drop store; its
two ends packed into an `i64`, the readable end in the low half, as the lift unpacks them),
`waitable-set.new` (a fresh set), `waitable.join` (an end joins a set) and `task.return` (its `i32` values, any number of them,
are recorded as the task's results: one stream for `KCore.entry`, two for the tee). -/
def lans : BI → HL → List Val → Option (HL × List Val)
  | .streamNew, ((st, rp), t), [] =>
    match dstep st .streamNew with
    | some (st', .ends r w') =>
      if r < M32 ∧ w' < M32 then
        some (((st', rp), t), [Val.i64 (BitVec.ofNat 64 (r + w' * M32))])
      else none
    | _ => none
  | .wsNew, ((st, rp), t), [] =>
    match dstep st .wsNew with
    | some (st', .nat n) => if n < M32 then some (((st', rp), t), [Val.i32 (w n)]) else none
    | _ => none
  | .join, ((st, rp), t), [.num ⟨.int .i32, h⟩, .num ⟨.int .i32, x⟩] =>
    (dstep st (.join h.toNat x.toNat)).map fun p => (((p.1, rp), t), [])
  | .taskReturn, (q, t), vs => (i32s? vs).map fun xs => ((q, t ++ xs.map BitVec.toNat), [])
  | _, _, _ => none

/-- The built-ins of the lift (the others are the runtime's, `bi`). -/
def isLift : BI → Bool
  | .streamNew | .wsNew | .join | .taskReturn => true
  | _ => false

/-- **Every built-in as a Core host function**: the lift's (`lans`, no memory access) and the
runtime's (`bans ma`, on `i32` arguments). -/
def lansAll (ma : Nat) (b : BI) (x : HL) (s : Store H) (vs : List Val) :
    Option (HL × Store H × List Val) :=
  if isLift b then (lans b x vs).map fun p => (p.1, s, p.2)
  else do
    let args ← i32s? vs
    let (q', s', res) ← bans ma b x.1 s args
    pure ((q', x.2), s', res.map Val.i32)

/-- The stateless Core host of one transition `x → x'` of `HL`. -/
def hostAtL (hb : BI → H) (ma : Nat) (x x' : HL) : HostSemantics H := fun h s vs out =>
  ∃ b s' res, h = hb b ∧ lansAll ma b x s vs = some (x', s', res) ∧ out = .returned s' (.values res)

/-- **Core 3.0 reduction with every built-in as a host call**, on `HL` and a Core configuration:
`HStep` with `lansAll` in place of `bans` (so it also answers the lift's built-ins). -/
inductive LStep (Pf : Numerics.Profile) (hb : BI → H) (ma : Nat) :
    HL × Config H → HL × Config H → Prop where
  | core {x : HL} {C C' : Config H} (h : Step Pf (fun _ _ _ _ => False) C C') :
      LStep Pf hb ma (x, C) (x, C')
  | host {x x' : HL} {s s' : Store H} {f : Frame} {c : Admin} {vs res : List Val} {a : Nat}
      {fi : FuncInst H} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} {b : BI}
      (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
      (hn : vs.length = ps.length) (hcode : fi.code = .host (hb b))
      (hans : lansAll ma b x s vs = some (x', s', res)) :
      LStep Pf hb ma (x, ⟨s, f, vals vs ++ [.ref (.func a), c]⟩) (x', ⟨s', f, vals res⟩)
  | instrs {x x' : HL} {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
      (h : LStep Pf hb ma (x, ⟨s, f, is⟩) (x', ⟨s', f', is'⟩)) (hne : vs ≠ [] ∨ rest ≠ []) :
      LStep Pf hb ma (x, ⟨s, f, vals vs ++ is ++ rest⟩) (x', ⟨s', f', vals vs ++ is' ++ rest⟩)
  | label {x x' : HL} {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
      {is is' : List Admin} (h : LStep Pf hb ma (x, ⟨s, f, is⟩) (x', ⟨s', f', is'⟩)) :
      LStep Pf hb ma (x, ⟨s, f, [.label n cont is]⟩) (x', ⟨s', f', [.label n cont is']⟩)
  | frame {x x' : HL} {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
      (h : LStep Pf hb ma (x, ⟨s, fi, is⟩) (x', ⟨s', fi', is'⟩)) :
      LStep Pf hb ma (x, ⟨s, f, [.frame n fi is]⟩) (x', ⟨s', f, [.frame n fi' is']⟩)

/-- `LStep`, iterated. -/
abbrev LSteps (Pf : Numerics.Profile) (hb : BI → H) (ma : Nat) :=
  Relation.ReflTransGen (LStep Pf hb ma)

/-- The globals after the lift: the input's readable end `r`, the output's writable end `wr`, the
waitable set `ws` (as `KDrop.initMSD`). -/
def liftG (g : Nat → Nat) (r wr ws : Nat) : Nat → Nat :=
  upd (upd (upd g Silmaril.Wasm.JcoTool.KCore.INSR r) Silmaril.Wasm.JcoTool.KCore.OUTSW wr)
    Silmaril.Wasm.JcoTool.KCore.WS ws

end Silmaril.Wasm.JcoTool.KCoreRun

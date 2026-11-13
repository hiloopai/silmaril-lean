module

public import Silmaril.X86.MemEvent.Defs

/-!
# Litmus event extraction from real thread bytes

A litmus thread is given as
machine-code bytes at a base address (`Thread`). `extract` decodes it with the `Atomic9`
listing decoder (`Ext9` + the atomic forms) and runs it **with the values read from memory
left symbolic**: every read returns any value of the test's finite value domain `dom`, and
each choice gives one candidate per-thread trace (`Trace`): a list of steps, each with its
memory actions (`Act`: a `MemEvent.Event` with the bytes read and written and a
`Flavor`) and the core after it, and the final core.

How a step is computed (`stepSym`):

* the instruction at `rip` is decoded from the code bytes (`Thread.fetch`; the slice of
  exactly the decoded length must decode to the same form, which is what a listing law
  for `Atomic9` needs);
* its access list `MemEvent.atomic9Accesses` is computed from the core;
* **inert** instructions (every event is a fence, or there is none) are run with the
  unchanged executor `Atomic9.exec` on the regions-only memory `Thread.frame` (no bytes; the
  executor never looks at them, by the locality of `MemEvent`), and their fence events become actions;
* **memory forms** of the litmus subset are run by `memStep`, a pure transcription of their
  `Atomic9.exec` semantics with the loaded value as a parameter: `mov m, r`, `mov m, imm32`
  (stores), `mov r, m` (`Ext` `load`), `xchg m, r`, `[lock] xadd m, r` and
  `[lock] cmpxchg m, r` at 32 and 64 bits; and `mov m8, imm8`, `mov r8, m8`,
  unlocked `inc`/`dec m`, `lock inc`/`dec m` and `lock add/or/and/sub/xor m, imm` at 32 and 64
  bits. Stores check the write permission on the regions,
  loads the read permission, and read-modify-writes both;
* anything else (another memory form, a fault, code that runs out of the image, or fuel
  exhausted) makes the whole extraction `none`: a trace set is never silently truncated.

The soundness statement (`Replay`, proved as `extract_sound` in `Extract/Thms.lean`): at every
step, on **every** memory with the thread's regions and code that answers the step's reads with
the trace's bytes (`Answers`), `Atomic9.step` goes to the trace's next core and writes exactly
the trace's bytes (`applyWrites`). Other threads may change memory between steps; the
statement is per step, so it composes with any interleaving. `Solo` is the single-thread
special case (`Replay.reaches`).

Not here: non-temporal stores (no decoder has `movnti`/`movntdq`), string forms (`Str9` is a
sibling machine of `Atomic9`, not combined with it), byte/word accesses other than the
`mov m8, imm8` store and the `mov r8, m8` load, `lock bts`, register-operand locked ALU forms. `Flavor` already has the `nonTemporal` and `string`
cases for the axiomatic models; this extractor only produces `plain`.
-/

@[expose] public section

namespace Silmaril.X86.Litmus

open Silmaril.X86 (State MState Word Byte Reg Flags maxInstrLength)
open Silmaril.X86.Ext (Sz Mem RM leBytes leValue)
open Silmaril.Process (Memory Region)
open MemEvent (Event Kind)

/-! ## Actions and traces -/

/-- How a store is ordered: plain write-back, non-temporal, or part of a string operation.
Only `plain` is produced today. -/
inductive Flavor where
  | plain
  | nonTemporal
  | string
  deriving DecidableEq, Repr

/-- One memory action of a thread: a memory event, the bytes it read (`[]` if it does not read)
and the bytes it wrote (`[]` if it does not write). -/
structure Act where
  ev : Event
  flavor : Flavor
  rd : List Byte
  wr : List Byte
  deriving DecidableEq, Repr

/-- The little-endian value read. -/
def Act.rval (a : Act) : Nat := leValue a.rd

/-- The little-endian value written. -/
def Act.wval (a : Act) : Nat := leValue a.wr

/-- A compact view of an action, for `decide`: kind, address, size, `locked`, the value read
and the value written (little-endian, `0` when absent). -/
structure Brief where
  kind : Kind
  addr : Nat
  size : Nat
  locked : Bool
  rval : Nat
  wval : Nat
  deriving DecidableEq, Repr

/-- The compact view of an action. -/
def Act.brief (a : Act) : Brief := ⟨a.ev.kind, a.ev.addr, a.ev.size, a.ev.locked, a.rval, a.wval⟩

/-- The action of an event that neither reads nor writes (a fence). -/
def Act.inert (e : Event) : Act := ⟨e, .plain, [], []⟩

/-- One step of a trace: the actions of one instruction, and the core after it. -/
structure StepRec where
  acts : List Act
  post : State

/-- A candidate per-thread trace. -/
structure Trace where
  steps : List StepRec
  final : State

/-- All actions of a trace, in program order. -/
def Trace.acts (tr : Trace) : List Act := tr.steps.flatMap StepRec.acts

/-- The compact view of a trace: its actions and the final values of some registers. -/
structure View where
  acts : List Brief
  regs : List Nat
  deriving DecidableEq, Repr

/-- The compact view of a trace, with the final values of `regs`. -/
def Trace.view (regs : List Reg) (tr : Trace) : View :=
  ⟨tr.acts.map Act.brief, regs.map fun r => (tr.final.read r).toNat⟩

/-! ## Threads -/

/-- A litmus thread: code bytes at `base`, the process mapping list `regions` (code and data),
and the initial core (`rip = base`). -/
structure Thread where
  base : Word
  code : List Byte
  regions : List Region
  init : State

/-- The address just past the code: the thread has finished when `rip` reaches it. -/
def Thread.endRip (t : Thread) : Word := t.base + BitVec.ofNat 64 t.code.length

/-- The regions-only memory: the thread's mapping list and no bytes. -/
def Thread.frame (t : Thread) : Memory := ⟨t.regions, ∅⟩

/-- Decode the instruction at `rip`: offset `o = rip - base`, the listing decoder on the
15-byte window, and the same form on exactly its own slice inside the code. -/
def Thread.fetch (t : Thread) (s : State) : Option (Atomic9.Instr × Nat) :=
  let o := (s.rip - t.base).toNat
  match Atomic9.decode ((t.code.drop o).take maxInstrLength) with
  | some (i, n) =>
    if o + n ≤ t.code.length ∧ Atomic9.decode ((t.code.drop o).take n) = some (i, n) then
      some (i, n)
    else none
  | none => none

/-- An initial core: `rip = base`, the listed registers set, the others zero, flags
undefined. -/
def initCore (base : Word) (regs : List (Reg × Word)) : State where
  regs := fun r => ((regs.find? fun p => p.1 = r).map Prod.snd).getD 0
  rip := base
  flags := ⟨none, none, none, none, none, none⟩

/-! ## Symbolic steps -/

/-- The event neither reads nor writes. -/
def Event.inert (e : Event) : Bool := !e.kind.reads && !e.kind.writes

/-- The loaded word of a byte list (as `Ext.loadN`). -/
def ldVal (bs : List Byte) : Word := BitVec.ofNat 64 (leValue bs)

/-- The bytes of value `v` at size `k`. -/
def valBytes (v : Nat) (k : Nat) : List Byte := leBytes (BitVec.ofNat 64 v) k

/-- The regions permit a write of `k` bytes at `a`. -/
def writeOk (R : List Region) (a k : Nat) : Bool := (⟨R, ∅⟩ : Memory).checkSpan .write a k

/-- The regions permit a read of `k` bytes at `a`. Loads and read-modify-writes check it, so a
load from an unreadable address aborts extraction instead of yielding traces whose replay
hypothesis no memory can meet. -/
def readOk (R : List Region) (a k : Nat) : Bool := (⟨R, ∅⟩ : Memory).checkSpan .read a k

/-- A plain store of the low `sz.bytes` bytes of `v`. -/
def storeStep (R : List Region) (sz : Sz) (a : Ext.Mem) (v : Word) (s : State) (next : Word) :
    Option (List (List Act × State)) :=
  let addr := (a.addr s next).toNat
  if writeOk R addr sz.bytes then
    some [([⟨⟨.store, addr, sz.bytes, false⟩, .plain, [], leBytes v sz.bytes⟩],
      { s with rip := next })]
  else none

/-- A plain one-byte store of the low byte of `v` (`mov m8, imm8`). -/
def store8Step (R : List Region) (a : Ext.Mem) (v : Word) (s : State) (next : Word) :
    Option (List (List Act × State)) :=
  let addr := (a.addr s next).toNat
  if writeOk R addr 1 then
    some [([⟨⟨.store, addr, 1, false⟩, .plain, [], leBytes v 1⟩], { s with rip := next })]
  else none

/-- One `rmw` branch per value of the domain: `f x` gives the bytes written and the core. -/
def rmwStep (R : List Region) (dom : List Nat) (sz : Sz) (lk : Bool) (a : Ext.Mem) (s : State)
    (next : Word) (f : BitVec sz.bits → Word × State) : Option (List (List Act × State)) :=
  let addr := (a.addr s next).toNat
  if readOk R addr sz.bytes && writeOk R addr sz.bytes then
    some (dom.map fun v =>
      let bs := valBytes v sz.bytes
      let r := f ((ldVal bs).setWidth sz.bits)
      ([⟨⟨.rmw, addr, sz.bytes, lk⟩, .plain, bs, leBytes r.1 sz.bytes⟩], { r.2 with rip := next }))
  else none

/-- The memory forms of the litmus subset, one branch per read value. -/
def memStep (R : List Region) (dom : List Nat) (i : Atomic9.Instr) (s : State) (n : Nat) :
    Option (List (List Act × State)) :=
  let next := s.rip + BitVec.ofNat 64 n
  match i with
  | .open9 (.ext8 (.base (.mov sz (.mem a) src))) =>
    storeStep R sz a ((sz.read s src).setWidth 64) s next
  | .open9 (.ext8 (.base (.movI sz (.mem a) imm))) =>
    storeStep R sz a ((imm.signExtend sz.bits).setWidth 64) s next
  | .open9 (.ext8 (.base (.load sz dst a))) =>
    let addr := (a.addr s next).toNat
    if readOk R addr sz.bytes then
      some (dom.map fun v =>
        let bs := valBytes v sz.bytes
        ([⟨⟨.load, addr, sz.bytes, false⟩, .plain, bs, []⟩],
          { sz.write s dst ((ldVal bs).setWidth sz.bits) with rip := next }))
    else none
  | .new (.xadd sz lk (.mem a) src) =>
    rmwStep R dom sz lk a s next fun x =>
      let y := sz.read s src
      (((x + y).setWidth 64), { sz.write s src x with flags := Silmaril.X86.Ext.addFlagsN x y })
  | .new (.xchg sz (.mem a) src) =>
    rmwStep R dom sz true a s next fun x => ((sz.read s src).setWidth 64, sz.write s src x)
  | .new (.cmpxchg sz lk (.mem a) src) =>
    rmwStep R dom sz lk a s next fun x =>
      let acc := sz.read s .rax
      let fl := Silmaril.X86.Ext.subFlagsN acc x
      if acc = x then ((sz.read s src).setWidth 64, { s with flags := fl })
      else (x.setWidth 64, { sz.write s .rax x with flags := fl })
  | .open9 (.ext8 (.base (.mov8 dst (.mem a)))) =>
    let addr := (a.addr s next).toNat
    if readOk R addr 1 then
      some (dom.map fun v =>
        let bs := valBytes v 1
        ([⟨⟨.load, addr, 1, false⟩, .plain, bs, []⟩],
          { Silmaril.X86.Ext.writeByte s dst ((ldVal bs).setWidth 8) with rip := next }))
    else none
  | .open9 (.ext8 (.base (.movI8 (.mem a) imm))) =>
    store8Step R a (imm.setWidth 64) s next
  | .open9 (.ext8 (.base (.incdec sz dec (.mem a)))) =>
    rmwStep R dom sz false a s next fun x =>
      (((if dec then x - 1#sz.bits else x + 1#sz.bits).setWidth 64),
        { s with flags := if dec then Silmaril.X86.Ext.decFlagsN x s.flags
          else Silmaril.X86.Ext.incFlagsN x s.flags })
  | .new (.lockIncDec sz dec a) =>
    rmwStep R dom sz true a s next fun x =>
      (((if dec then x - 1#sz.bits else x + 1#sz.bits).setWidth 64),
        { s with flags := if dec then Silmaril.X86.Ext.decFlagsN x s.flags
          else Silmaril.X86.Ext.incFlagsN x s.flags })
  | .new (.lockAluI sz op a imm) =>
    if op = .cmp then none
    else
      rmwStep R dom sz true a s next fun x =>
        let y := imm.signExtend sz.bits
        ((Silmaril.X86.Ext.AluOp.resultN op x y).setWidth 64,
          { s with flags := Silmaril.X86.Ext.AluOp.flagsN op x y })
  | _ => none

/-- **One symbolic step**: the branches `(actions, next core)` of the instruction at `rip`,
or `none` (undecodable, unsupported, or a fault). -/
def stepSym (t : Thread) (dom : List Nat) (s : State) : Option (List (List Act × State)) :=
  match t.fetch s with
  | none => none
  | some (i, n) =>
    let es := MemEvent.atomic9Accesses i s n
    if es.all Event.inert then
      match Atomic9.exec i s t.frame n with
      | .ok c _ => some [(es.map Act.inert, c)]
      | _ => none
    else memStep t.regions dom i s n

/-- Prepend a step to each trace. -/
def consStep (acts : List Act) (c : State) (trs : List Trace) : List Trace :=
  trs.map fun tr => ⟨⟨acts, c⟩ :: tr.steps, tr.final⟩

/-- Explore every branch from a core, with `fuel` instructions at most. -/
def explore (t : Thread) (dom : List Nat) : Nat → State → Option (List Trace)
  | fuel, s =>
    if s.rip = t.endRip then some [⟨[], s⟩]
    else
      match fuel with
      | 0 => none
      | f + 1 =>
        match stepSym t dom s with
        | none => none
        | some outs =>
          (outs.mapM fun o => (explore t dom f o.2).map (consStep o.1 o.2)).map List.flatten

/-- **The candidate traces of a thread** over the value domain `dom`, or `none` if some
branch is unsupported, faults or needs more than `fuel` instructions. -/
def extract (t : Thread) (dom : List Nat) (fuel : Nat) : Option (List Trace) :=
  explore t dom fuel t.init

/-! ## Soundness statement -/

/-- The memory answers every read of `acts` with the bytes the action records. -/
def Answers (m : Memory) (acts : List Act) : Prop :=
  ∀ a ∈ acts, a.ev.kind.reads = true → m.readBytes a.ev.addr a.ev.size = some a.rd

/-- Write the bytes of the writing actions, in order. -/
def applyWrites : Memory → List Act → Option Memory
  | m, [] => some m
  | m, a :: as =>
    if a.ev.kind.writes then (m.writeBytes a.ev.addr a.wr).bind (applyWrites · as)
    else applyWrites m as

/-- **The trace replays on the sequential machine**: at each step, on every memory with the
thread's regions, its code loaded, and answering the step's reads, one `Atomic9.step` reaches
the recorded core and performs exactly the recorded writes; the last core is the final one
and has finished. -/
inductive Replay (t : Thread) : State → List StepRec → State → Prop
  | done (s : State) (h : s.rip = t.endRip) : Replay t s [] s
  | step (s : State) (r : StepRec) (rest : List StepRec) (s' : State)
      (h : ∀ m : Memory, m.regions = t.regions → Silmaril.X86.Ext.Loaded m t.base t.code →
        Answers m r.acts →
        ∃ m', Atomic9.step ⟨s, m⟩ = some ⟨r.post, m'⟩ ∧ applyWrites m r.acts = some m')
      (tail : Replay t r.post rest s') : Replay t s (r :: rest) s'

/-- A single-thread run with no interference: at each step the current memory has the
thread's regions and code and answers the step's reads, and the next memory is the current
one with the step's writes. -/
def Solo (t : Thread) : Memory → List StepRec → Memory → Prop
  | m, [], m' => m' = m
  | m, r :: rest, m'' =>
    m.regions = t.regions ∧ Silmaril.X86.Ext.Loaded m t.base t.code ∧ Answers m r.acts ∧
      ∃ m', applyWrites m r.acts = some m' ∧ Solo t m' rest m''

/-! ## Non-vacuity check -/

/-- A step's replay hypothesis is satisfiable by a memory built from the code and the read
bytes: the code is executable under the regions, and the step reads at most once, from a
readable span of the right size disjoint from the code. Checked by `decide` per test. -/
def Thread.placed (t : Thread) (acts : List Act) : Bool :=
  t.frame.checkSpan .execute t.base.toNat t.code.length &&
    match acts.filter (fun a => a.ev.kind.reads) with
    | [] => true
    | [a] => t.frame.checkSpan .read a.ev.addr a.rd.length && a.rd.length == a.ev.size &&
      (t.base.toNat + t.code.length ≤ a.ev.addr || a.ev.addr + a.rd.length ≤ t.base.toNat)
    | _ => false

/-- Every step of every trace is `placed`. -/
def Thread.allPlaced (t : Thread) (trs : List Trace) : Bool :=
  trs.all fun tr => tr.steps.all fun r => t.placed r.acts

end Silmaril.X86.Litmus

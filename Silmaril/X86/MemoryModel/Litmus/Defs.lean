module

public import Silmaril.X86.Atomic9.Defs
public import Silmaril.X86.MemEvent.Defs

/-!
# x86 litmus tests: data shapes and outcome conditions

This module fixes what a test is, so that event extraction, the axiomatic SC/TSO/XL models,
operational TSO and the verdict proofs consume test data without depending on the tool that
generates a corpus. No corpus is included here.

## A test

* `locs`: the shared locations at fixed absolute addresses (one 64-byte-aligned slot each,
  from `0x10000`), with their size in bytes and initial value (little-endian; arrays start at
  zero). Every other byte is unmapped.
* `threads`: per thread, the instructions as the canonical AT&T text the tool gave to GNU `as`
  together with **the bytes `as` produced** (`Insn.bytes`); `Thread.code` is their
  concatenation. `Insn.events` is the list of memory events (`MemEvent.Event`: kind, address,
  size, `locked`) that the tool's checker reads the instruction as, computed from the tool's
  IR, not from the bytes; `none` for forms with no `MemEvent` counterpart (`movnti`,
  `rep stosb`). `Insn.eventsMatch` checks it against the events `MemEvent.atomic9Accesses`
  gives for the decoded bytes. Memory operands are absolute 32-bit addresses (ModRM `04`,
  SIB `25`), so the bytes need no relocation. `regs` are the nonzero initial registers
  (System V names; every other register starts at zero; `rflags.DF` is clear, as the System V
  ABI requires on entry).
* `quant`/`cond`: herd's final condition, resolved to registers and addresses. A register atom
  `.reg t r bits v` compares the low `bits` bits of thread `t`'s 64-bit `r` with `v` (herd's
  `EAX` is `rax` at 32 bits); a memory atom `.mem a n v` compares the `n` little-endian bytes at
  `a` with `v`.
* `witness`: the formula a verdict is about: the condition for `exists`/`~exists`, its negation
  for `forall`. `Verdict.allowed` means some final state of the model satisfies the witness.
* `coverage`: `.tso` for tests whose accesses are aligned write-back accesses of at most 8
  bytes, locked RMWs and fences, where x86-TSO applies; `.xl` for the loose corners
  (mixed-size, misaligned, non-temporal and string stores), which are **not covered by
  x86-TSO; XL verdict only**.
* `tso`: the recorded x86-TSO verdict (`none` for `.xl` tests), cited in `basis` (herd7's
  recorded `.expected` output, the x86-TSO paper's tables, or the tool's checker). The tool
  refuses to generate the corpus unless its own transcription of herd's `x86tso.cat` gives the
  same verdict.
* `xl`: the intended XL verdict: equal to `tso` on `.tso` tests (XL is defined to coincide with
  x86-TSO there), stated from the XL design on `.xl` tests. Not machine-checked here.
* `sc`: the SC verdict computed by the tool's checker (`none` for `.xl` tests). Tested only.

`Verdict.Holds v t Reach` states a verdict against any set `Reach` of reachable final states,
so a model can prove, for instance, `(t.tso.getD .allowed).Holds t TsoFinal`.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Litmus

open Silmaril.X86 (Reg)

/-- A byte. -/
abbrev Byte := BitVec 8

/-- Whether a test's witness is reachable. -/
inductive Verdict where
  | allowed
  | forbidden
  deriving DecidableEq, Repr

/-- herd's quantifiers: `exists`, `~exists`, `forall`. -/
inductive Quant where
  | exists_
  | notExists
  | forall_
  deriving DecidableEq, Repr

/-- `.tso`: covered by x86-TSO; `.xl`: a loose corner, XL verdict only. -/
inductive Coverage where
  | tso
  | xl
  deriving DecidableEq, Repr

/-- A comparison in a final condition. -/
inductive Atom where
  /-- The low `bits` bits of thread `thread`'s register `r` equal `value`. -/
  | reg (thread : Nat) (r : Reg) (bits : Nat) (value : Nat)
  /-- The `size` little-endian bytes at `addr` equal `value`. -/
  | mem (addr : Nat) (size : Nat) (value : Nat)
  deriving DecidableEq, Repr

/-- A final-condition formula. -/
inductive Cond where
  | tt
  | atom (a : Atom)
  | not (p : Cond)
  | and (p q : Cond)
  | or (p q : Cond)
  deriving DecidableEq, Repr

/-- A shared location: name, first address, size in bytes, initial little-endian value. -/
structure Loc where
  name : String
  addr : Nat
  size : Nat
  init : Nat
  deriving DecidableEq, Repr

/-- One instruction: the AT&T text given to the assembler, the bytes it produced, and the
memory events the tool's checker reads it as (`none`: no `MemEvent` form today). -/
structure Insn where
  asm : String
  bytes : List Byte
  events : Option (List Silmaril.X86.MemEvent.Event)
  deriving DecidableEq, Repr

/-- A thread: its instructions and its nonzero initial registers. -/
structure Thread where
  insns : List Insn
  regs : List (Reg × Nat)
  deriving DecidableEq, Repr

/-- The thread's machine code. -/
def Thread.code (th : Thread) : List Byte := (th.insns.map Insn.bytes).flatten

/-- The initial value of a register (zero unless listed). -/
def Thread.initReg (th : Thread) (r : Reg) : BitVec 64 :=
  match th.regs.find? (·.1 == r) with
  | some (_, v) => BitVec.ofNat 64 v
  | none => 0

/-- A litmus test (see the module documentation for each field). -/
structure Test where
  name : String
  source : String
  doc : String
  locs : List Loc
  threads : List Thread
  quant : Quant
  cond : Cond
  coverage : Coverage
  tso : Option Verdict
  xl : Verdict
  sc : Option Verdict
  basis : String
  deriving Repr

/-! ## Final states and conditions -/

/-- A final state: every thread's registers and the byte memory. -/
structure Final where
  regs : Nat → Reg → BitVec 64
  mem : Nat → Option Byte

/-- The little-endian value of `n` bytes from `addr`, if all are mapped. -/
def leValue (mem : Nat → Option Byte) (addr : Nat) : Nat → Option Nat
  | 0 => some 0
  | n + 1 => do
    let b ← mem addr
    let r ← leValue mem (addr + 1) n
    pure (b.toNat + 256 * r)

/-- Evaluate an atom. -/
def Atom.eval (f : Final) : Atom → Bool
  | .reg t r bits v => (f.regs t r).toNat % 2 ^ bits == v
  | .mem a n v => leValue f.mem a n == some v

/-- Evaluate a formula. -/
def Cond.eval (f : Final) : Cond → Bool
  | .tt => true
  | .atom a => a.eval f
  | .not p => !p.eval f
  | .and p q => p.eval f && q.eval f
  | .or p q => p.eval f || q.eval f

/-- The formula a verdict is about. -/
def Test.witness (t : Test) : Cond :=
  match t.quant with
  | .forall_ => .not t.cond
  | _ => t.cond

/-- Some final state in `Reach` satisfies the witness. -/
def Test.Allowed (t : Test) (Reach : Final → Prop) : Prop :=
  ∃ f, Reach f ∧ t.witness.eval f = true

/-- A verdict holds for `t` against the reachable final states `Reach`. -/
def Verdict.Holds (v : Verdict) (t : Test) (Reach : Final → Prop) : Prop :=
  match v with
  | .allowed => t.Allowed Reach
  | .forbidden => ¬ t.Allowed Reach

/-- The byte at `a` of a location list's initial memory (`none` outside every location). -/
def initByte (locs : List Loc) (a : Nat) : Option Byte :=
  (locs.find? fun l => l.addr ≤ a && a < l.addr + l.size).map fun l =>
    BitVec.ofNat 8 (l.init / 256 ^ (a - l.addr))

/-- The initial memory of a test. -/
def Test.initMem (t : Test) : Nat → Option Byte := initByte t.locs

/-- The initial registers of thread `i` (all zero for a missing thread). -/
def Test.initRegs (t : Test) (i : Nat) (r : Reg) : BitVec 64 :=
  match t.threads[i]? with
  | some th => th.initReg r
  | none => 0

/-! ## Byte checks -/

/-- The instruction's bytes are exactly one instruction of `Atomic9`'s listing decoder (the
decoder of the atomic machine: `Ext9`/`Open9` plus locked RMWs, `xchg`, fences, `pause`). -/
def Insn.decodes (i : Insn) : Bool :=
  match Silmaril.X86.Atomic9.decode i.bytes with
  | some (_, n) => n == i.bytes.length
  | none => false

/-- Every instruction of every thread decodes as one `Atomic9` instruction. -/
def Test.decodes (t : Test) : Bool := t.threads.all fun th => th.insns.all Insn.decodes

/-- The architectural state a thread starts in: its initial registers, `rip = 0`, no flag
known. -/
def Thread.initState (th : Thread) : Silmaril.X86.State :=
  { regs := th.initReg, rip := 0, flags := ⟨none, none, none, none, none, none⟩ }

/-- The memory events of the instruction's **bytes**: decode them with `Atomic9.decode` (which
must consume all of them) and take `MemEvent.atomic9Accesses` in state `s`. Every memory
operand the tool emits is absolute (no base, no index), so the addresses do not depend on
`s`. -/
def Insn.byteEvents (s : Silmaril.X86.State) (i : Insn) :
    Option (List Silmaril.X86.MemEvent.Event) :=
  match Silmaril.X86.Atomic9.decode i.bytes with
  | some (d, n) =>
    if n == i.bytes.length then some (Silmaril.X86.MemEvent.atomic9Accesses d s n) else none
  | none => none

/-- The recorded events (when present) are exactly the events of the bytes, in state `s`. -/
def Insn.eventsMatch (s : Silmaril.X86.State) (i : Insn) : Bool :=
  match i.events with
  | some es => i.byteEvents s == some es
  | none => true

/-- Every instruction records its events (no `none`). -/
def Test.hasEvents (t : Test) : Bool :=
  t.threads.all fun th => th.insns.all fun i => i.events.isSome

/-- Every recorded event list is the events of the bytes, each thread in its initial state. -/
def Test.eventsMatch (t : Test) : Bool :=
  t.threads.all fun th => th.insns.all (Insn.eventsMatch th.initState)

end Silmaril.X86.MemoryModel.Litmus

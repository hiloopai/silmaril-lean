module

public import Silmaril.X86.Ext.Store
public import Silmaril.X86.Ext.SymExec
public import Silmaril.Machine.X86.Ext.Lemmas.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-!
# Semantic block lifting: rung 2½ for code our compiler did not emit

`Lift.checkBlock` (rung 2½ of `docs/Decompilation.md`) lifts a recovered block
by *recompilation*: it runs Silmaril's own instruction selection on a proposed
Lir block and compares bytes. That accepts exactly the code our backend emits,
so it cannot lift a block that clang or gcc produced. This module is the
semantic sibling. A proposal is a **block summary** — what every live-out
register holds, which stores happen and in what order, what the flags compare —
written as `Ex` expressions over the block's *entry* registers and *entry*
memory, so it is a straight-line SSA value graph with no machine state in it.
The checker decodes the bytes itself, symbolically executes them over `Ex`, and
accepts when the result is the proposal.

## Proposer and checker

The proposer is untrusted. `run` doubles as one (print `run code n SSt.init`
with `#eval` and paste it), but nothing depends on that: an external
decompiler, an agent or a hand-written spec in the same vocabulary is checked
the same way. `check` is total and decidable: it decodes with `Ext.decode`,
refuses anything outside its fragment, and compares the summaries with
`DecidableEq`. A rejection is `false`; `explain` is the diagnostic.

## What acceptance buys

`check_sound` is the translation-validation theorem. From any machine state
whose RIP is at the block and whose memory holds the block's bytes, `n`
retirements of the real machine (`Ext.Runs`, through fetch, decode and
`exec`) reach a state in which

* RIP is past the block,
* every live-out register holds the value its summary expression denotes,
* memory is the entry memory with the summary's stores applied in order, and
* the flags are those of the summary's last comparison, when it has one,

under three families of side conditions that the summary lists explicitly:
every load it performs is backed, every store it performs is writable, and no
store hits the code. Those are facts about the *entry* state only.

## Memory

Loads denote the *entry* memory (`Ex.ld`). That is sound because the checker
only accepts a load whose address is disjoint from every store earlier in the
block, either **syntactically** (`disjoint`: same symbolic base, constant
offsets whose distance, modulo 2^64, clears both widths) or by an **aliasing
assumption** the proposal declares (`Summary.assume`). An assumption is not
checked; it becomes a hypothesis of `check_sound` (`AssumeHolds`), stated at the
entry state, for the caller to discharge — typically from a calling
convention's region disjointness, since a frame slot and a caller's buffer have
different symbolic bases and no amount of offset arithmetic separates them. A
load that may alias an earlier store and is not covered is rejected rather
than guessed at. Store-to-load forwarding is a proposer improvement that would
not change what acceptance means.

## The fragment

32- and 64-bit register moves, loads and stores with a register or absent
base (no RIP-relative and no `fs:` operand, whose addresses are not functions
of the entry registers), the six ALU operations with register, memory,
immediate and accumulator operands, shifts and rotates by an immediate,
`inc`/`dec`, `not`/`neg`, `bswap`, `lea`, `mov r32, imm32` and `nop`. Control
transfers end a block and are not lifted here: the block's terminator is the
CFG rung's business, and the flag summary is what it needs to decide a
conditional branch. `push`/`pop`, RIP-relative operands, `call` and `ret` are
the obvious next additions.

## A worked instance

`Silmaril/Crypto/X86/Sha256O2/Lifted.lean` lifts both loop bodies of clang
`-O2` `sha256_compress` (24 and 47 instructions) and re-proves the hand-stepped
traces of `Sha256O2/Exec.lean` with identical statements, at about a third of
the size.
-/

@[expose] public section

namespace Silmaril.X86.Decompile.SemLift

open Silmaril.X86 (Reg Word State Byte AluOp Flags MState)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext

/-! ## Lifted values -/

/-- A 64-bit value of the lifted block, over the entry state. -/
inductive Ex where
  /-- The entry value of a register. -/
  | reg (r : Reg)
  /-- The little-endian `k`-byte load from the *entry* memory, zero-extended. -/
  | ld (a : Ex) (k : Nat)
  | const (x : Word)
  /-- Zero-extension of the low `sz.bits` bits: a 32-bit move. -/
  | ext (sz : Sz) (a : Ex)
  /-- An ALU result at operand size `sz`, zero-extended. -/
  | alu (sz : Sz) (op : AluOp) (a b : Ex)
  /-- A shift or rotate at operand size `sz` by an already-masked count. -/
  | shift (sz : Sz) (op : ShiftOp) (a : Ex) (c : Nat)
  /-- `not` or `neg` at operand size `sz`. -/
  | un (sz : Sz) (op : UnOp) (a : Ex)
  /-- `bswap` at operand size `sz`. -/
  | bswap (sz : Sz) (a : Ex)
  deriving DecidableEq, Repr

/-- Zero-extension of the low `sz.bits` bits. -/
def extW (sz : Sz) (x : Word) : Word := (x.setWidth sz.bits).setWidth 64

/-- An ALU result at size `sz`, as a register write leaves it. -/
def aluW (sz : Sz) (op : AluOp) (x y : Word) : Word :=
  (AluOp.resultN op (x.setWidth sz.bits) (y.setWidth sz.bits)).setWidth 64

/-- A shift or rotate at size `sz`, as a register write leaves it. -/
def shiftW (sz : Sz) (op : ShiftOp) (x : Word) (c : Nat) : Word :=
  (op.result (x.setWidth sz.bits) c).setWidth 64

/-- `not` or `neg` at size `sz`, as a register write leaves it. -/
def unW (sz : Sz) : UnOp → Word → Word
  | .not, x => (~~~(x.setWidth sz.bits)).setWidth 64
  | .neg, x => (0#sz.bits - x.setWidth sz.bits).setWidth 64

/-- `bswap` at size `sz`, as a register write leaves it. -/
def bswapW (sz : Sz) (x : Word) : Word := (byteSwap sz (x.setWidth sz.bits)).setWidth 64

/-- The value of a lifted expression in an entry state and entry memory. An
unbacked load denotes `0`; `check_sound` only speaks about runs in which every
load of the summary is backed. -/
def Ex.eval (s : State) (mem : Memory) : Ex → Word
  | reg r => s.read r
  | ld a k => (loadN mem (a.eval s mem) k).getD 0
  | const x => x
  | ext sz a => extW sz (a.eval s mem)
  | alu sz op a b => aluW sz op (a.eval s mem) (b.eval s mem)
  | shift sz op a c => shiftW sz op (a.eval s mem) c
  | un sz op a => unW sz op (a.eval s mem)
  | bswap sz a => bswapW sz (a.eval s mem)

/-! The equations of `Ex.eval`, one per constructor, so that a proof at the
lifted level can unfold the arithmetic while leaving loads as atoms. -/

theorem Ex.eval_reg (s : State) (mem : Memory) (r : Reg) : (Ex.reg r).eval s mem = s.read r := rfl
theorem Ex.eval_const (s : State) (mem : Memory) (x : Word) : (Ex.const x).eval s mem = x := rfl
theorem Ex.eval_ext (s : State) (mem : Memory) (sz : Sz) (a : Ex) :
    (Ex.ext sz a).eval s mem = extW sz (a.eval s mem) := rfl
theorem Ex.eval_alu (s : State) (mem : Memory) (sz : Sz) (op : AluOp) (a b : Ex) :
    (Ex.alu sz op a b).eval s mem = aluW sz op (a.eval s mem) (b.eval s mem) := rfl
theorem Ex.eval_shift (s : State) (mem : Memory) (sz : Sz) (op : ShiftOp) (a : Ex) (c : Nat) :
    (Ex.shift sz op a c).eval s mem = shiftW sz op (a.eval s mem) c := rfl
theorem Ex.eval_un (s : State) (mem : Memory) (sz : Sz) (op : UnOp) (a : Ex) :
    (Ex.un sz op a).eval s mem = unW sz op (a.eval s mem) := rfl
theorem Ex.eval_bswap (s : State) (mem : Memory) (sz : Sz) (a : Ex) :
    (Ex.bswap sz a).eval s mem = bswapW sz (a.eval s mem) := rfl

/-- What the flags hold at the end of the block. -/
inductive FlagSum where
  /-- Nothing is claimed. -/
  | unknown
  /-- The flags of `cmp a, b` at size `sz`. -/
  | cmp (sz : Sz) (a b : Ex)
  deriving DecidableEq, Repr

/-- The flag claim, read against a concrete flag register. -/
def FlagSum.Holds (s : State) (mem : Memory) (f : Flags) : FlagSum → Prop
  | unknown => True
  | cmp sz a b => f = subFlagsN ((a.eval s mem).setWidth sz.bits) ((b.eval s mem).setWidth sz.bits)

/-! ## Symbolic state -/

/-- The symbolic state after a prefix of the block: every register as an
expression over the entry state, the stores so far (address, width, value) in
program order, every load so far (address, width), the bytes consumed, and the
flag summary. -/
structure SSt where
  regs : Reg → Ex
  stores : List (Ex × Nat × Ex)
  reads : List (Ex × Nat)
  len : Nat
  flags : FlagSum

/-- The entry: every register is itself, nothing stored or read. -/
def SSt.init : SSt := ⟨Ex.reg, [], [], 0, .unknown⟩

namespace SSt

/-- Write a register. -/
def set (σ : SSt) (r : Reg) (e : Ex) : SSt :=
  { σ with regs := fun q => if q = r then e else σ.regs q }

/-- Record a load. -/
def read (σ : SSt) (a : Ex) (k : Nat) : SSt := { σ with reads := σ.reads ++ [(a, k)] }

/-- Record a store. -/
def store (σ : SSt) (a : Ex) (k : Nat) (v : Ex) : SSt := { σ with stores := σ.stores ++ [(a, k, v)] }

/-- An ALU instruction with register destination `dst` and second operand `y`:
`cmp` sets the flag summary, every other operation writes `dst` and forgets
the flags. -/
def aluTo (σ : SSt) (sz : Sz) (op : AluOp) (dst : Reg) (y : Ex) : SSt :=
  if op = .cmp then { σ with flags := .cmp sz (σ.regs dst) y }
  else { σ.set dst (.alu sz op (σ.regs dst) y) with flags := .unknown }

end SSt

/-! ## Addresses and disjointness -/

/-- The effective address of a memory operand, as an expression, when it is a
function of the registers: a register base or none, an optional scaled index
and a displacement. RIP-relative and `fs:` operands are outside the fragment. -/
def addrEx (σ : SSt) (m : Mem) : Option Ex :=
  let idx : Ex := match m.index with
    | some i => .shift .q .shl (σ.regs i.reg) i.scale.toNat
    | none => .const 0
  match m.base with
  | .reg r => some (.alu .q .add (.alu .q .add (σ.regs r) idx) (.const (m.disp.signExtend 64)))
  | .none => some (.alu .q .add (.alu .q .add (.const 0) idx) (.const (m.disp.signExtend 64)))
  | .rip | .fs => none

/-- Split a constant offset off an address. -/
def split : Ex → Ex × Word
  | .alu .q .add a (.const c) => (a, c)
  | e => (e, 0)

/-- `[a, a + k)` and `[b, b + j)` are disjoint in every state: same symbolic
base, and the constant offsets are far enough apart in both directions,
modulo 2^64. -/
def disjoint (a : Ex) (k : Nat) (b : Ex) (j : Nat) : Bool :=
  (split a).1 == (split b).1 &&
    decide (k ≤ ((split b).2 - (split a).2).toNat) &&
    decide (j ≤ ((split a).2 - (split b).2).toNat)

/-- Aliasing assumptions a proposal may declare: `(a, k, b, j)` claims that
`[a, a + k)` and `[b, b + j)` are disjoint at the entry. The checker cannot
decide such a claim when the two addresses have different symbolic bases —
the frame and a caller's buffer, say — so it becomes a hypothesis of
`check_sound`, to be discharged from the calling convention's region
disjointness. -/
abbrev Assume := List (Ex × Nat × Ex × Nat)

/-- A load may read the entry memory when it is disjoint from every store so
far: syntactically, or by a declared assumption. -/
def SSt.loadOk (asm : Assume) (σ : SSt) (a : Ex) (k : Nat) : Bool :=
  σ.stores.all fun p => disjoint a k p.1 p.2.1 || asm.contains (a, k, p.1, p.2.1)

/-! ## One instruction -/

/-- Symbolically execute one instruction of the fragment; `none` outside it.
Control transfers and `ret` are outside it, so an accepted instruction always
falls through. -/
def symStep (asm : Assume) (σ : SSt) : Ext.Instr → Option SSt
  | .mov sz (.reg dst) src => some (σ.set dst (.ext sz (σ.regs src)))
  | .mov sz (.mem m) src =>
    (addrEx σ m).map fun a => σ.store a sz.bytes (.ext sz (σ.regs src))
  | .load sz dst m =>
    (addrEx σ m).bind fun a =>
      if σ.loadOk asm a sz.bytes then some ((σ.read a sz.bytes).set dst (.ext sz (.ld a sz.bytes)))
      else none
  | .alu sz op (.reg dst) src => some (σ.aluTo sz op dst (σ.regs src))
  | .aluR sz op dst (.reg src) => some (σ.aluTo sz op dst (σ.regs src))
  | .aluR sz op dst (.mem m) =>
    (addrEx σ m).bind fun a =>
      if σ.loadOk asm a sz.bytes then some ((σ.read a sz.bytes).aluTo sz op dst (.ld a sz.bytes))
      else none
  | .aluI sz op (.reg dst) imm =>
    some (σ.aluTo sz op dst (.const ((imm.signExtend sz.bits).setWidth 64)))
  | .aluI8 sz op (.reg dst) imm =>
    some (σ.aluTo sz op dst (.const ((imm.signExtend sz.bits).setWidth 64)))
  | .aluA sz op imm => some (σ.aluTo sz op .rax (.const ((imm.signExtend sz.bits).setWidth 64)))
  | .shift sz op (.reg dst) (.imm n) =>
    some { σ.set dst (.shift sz op (σ.regs dst) (n.toNat % sz.bits)) with flags := .unknown }
  | .incdec sz dec (.reg dst) =>
    some { σ.set dst (.alu sz (if dec then .sub else .add) (σ.regs dst) (.const 1)) with
      flags := .unknown }
  | .lea .q dst m => (addrEx σ m).map fun a => σ.set dst a
  | .movI32 dst imm => some (σ.set dst (.const (imm.setWidth 64)))
  | .unary sz op (.reg dst) => some { σ.set dst (.un sz op (σ.regs dst)) with flags := .unknown }
  | .bswap sz dst => some (σ.set dst (.bswap sz (σ.regs dst)))
  | .nop _ => some σ
  | _ => none

/-! ## A block -/

/-- Decode and symbolically execute `n` instructions of `code`, from the byte
offset `σ.len`. Each instruction must decode from exactly its own slice and
lie inside `code`. -/
def run (asm : Assume) (code : List Byte) : Nat → SSt → Option SSt
  | 0, σ => some σ
  | n + 1, σ =>
    match Ext.decode ((code.drop σ.len).take 15) with
    | none => none
    | some (i, l) =>
      if Ext.decode ((code.drop σ.len).take l) = some (i, l) ∧ σ.len + l ≤ code.length then
        (symStep asm σ i).bind fun σ' => run asm code n { σ' with len := σ.len + l }
      else none

/-- A proposed block summary: the live-out registers and what they hold, the
stores and loads in program order, the length in bytes and the flag claim. -/
structure Summary where
  outs : List (Reg × Ex)
  stores : List (Ex × Nat × Ex)
  reads : List (Ex × Nat)
  len : Nat
  flags : FlagSum
  /-- Declared aliasing assumptions; empty when every load is syntactically
  disjoint from the stores before it. -/
  assume : Assume := []
  deriving Repr

/-- Does the symbolic state agree with the proposal? -/
def Summary.matches (spec : Summary) (σ : SSt) : Bool :=
  spec.outs.all (fun p => σ.regs p.1 == p.2) && σ.stores == spec.stores &&
    σ.reads == spec.reads && σ.len == spec.len && σ.flags == spec.flags

/-- **The checker.** Decode and symbolically execute `n` instructions of `code`
and compare with the proposal. -/
def check (code : List Byte) (n : Nat) (spec : Summary) : Bool :=
  match run spec.assume code n SSt.init with
  | some σ => spec.matches σ
  | none => false

/-- The untrusted proposer: what the checker computes, as a summary with the
given live-out registers. -/
def propose (code : List Byte) (n : Nat) (outs : List Reg) (asm : Assume := []) :
    Option Summary :=
  (run asm code n SSt.init).map fun σ =>
    ⟨outs.map fun r => (r, σ.regs r), σ.stores, σ.reads, σ.len, σ.flags, asm⟩

/-! ## Soundness: expressions -/

/-- The memory after the summary's stores, applied in order, each address and
value evaluated in the entry state. -/
def applyStores (s0 : State) (mem0 : Memory) : Memory → List (Ex × Nat × Ex) → Option Memory
  | mem, [] => some mem
  | mem, (a, k, v) :: rest =>
    (storeN mem (a.eval s0 mem0) k (v.eval s0 mem0)).bind fun m => applyStores s0 mem0 m rest

theorem applyStores_append (s0 : State) (mem0 : Memory) :
    ∀ (mem : Memory) (l : List (Ex × Nat × Ex)) (a : Ex) (k : Nat) (v : Ex),
      applyStores s0 mem0 mem (l ++ [(a, k, v)]) =
        (applyStores s0 mem0 mem l).bind fun m => storeN m (a.eval s0 mem0) k (v.eval s0 mem0)
  | mem, [], a, k, v => by
    simp only [List.nil_append, applyStores, Option.bind_some]
    cases storeN mem (a.eval s0 mem0) k (v.eval s0 mem0) <;> simp
  | mem, (b, j, w) :: rest, a, k, v => by
    simp only [List.cons_append, applyStores]
    cases storeN mem (b.eval s0 mem0) j (w.eval s0 mem0) with
    | none => rfl
    | some m => exact applyStores_append s0 mem0 m rest a k v

/-- Stores change no mapping, so permissions survive them. -/
theorem applyStores_permitted {s0 : State} {mem0 : Memory} :
    ∀ {mem mem' : Memory} {l : List (Ex × Nat × Ex)}, applyStores s0 mem0 mem l = some mem' →
      ∀ {access : Silmaril.Process.Access} {start count : Nat},
        mem.Permitted access start count → mem'.Permitted access start count
  | mem, mem', [], h, _, _, _, p => by
    simp only [applyStores, Option.some.injEq] at h
    exact h ▸ p
  | mem, mem', (a, k, v) :: rest, h, _, _, _, p => by
    simp only [applyStores] at h
    cases hs : storeN mem (a.eval s0 mem0) k (v.eval s0 mem0) with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs, Option.bind_some] at h
      exact applyStores_permitted h ((Stored.of_storeN hs).permitted p)

/-- A load disjoint from every store reads what the entry memory held. -/
theorem applyStores_loadN {s0 : State} {mem0 : Memory} {addr : Word} {k : Nat} :
    ∀ {mem mem' : Memory} {l : List (Ex × Nat × Ex)}, applyStores s0 mem0 mem l = some mem' →
      (∀ p ∈ l, addr.toNat + k ≤ (p.1.eval s0 mem0).toNat ∨
        (p.1.eval s0 mem0).toNat + p.2.1 ≤ addr.toNat) →
      loadN mem' addr k = loadN mem addr k
  | mem, mem', [], h, _ => by
    simp only [applyStores, Option.some.injEq] at h
    rw [h]
  | mem, mem', (a, j, v) :: rest, h, hd => by
    simp only [applyStores] at h
    cases hs : storeN mem (a.eval s0 mem0) j (v.eval s0 mem0) with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs, Option.bind_some] at h
      rw [applyStores_loadN h (fun p hp => hd p (List.mem_cons_of_mem _ hp))]
      exact loadN_storeN_disjoint hs (hd _ List.mem_cons_self)

/-- The code stays loaded across stores that miss it. -/
theorem applyStores_loaded {s0 : State} {mem0 : Memory} {base : Word} {code : List Byte} :
    ∀ {mem mem' : Memory} {l : List (Ex × Nat × Ex)}, applyStores s0 mem0 mem l = some mem' →
      (∀ p ∈ l, base.toNat + code.length ≤ (p.1.eval s0 mem0).toNat ∨
        (p.1.eval s0 mem0).toNat + p.2.1 ≤ base.toNat) →
      Loaded mem base code → Loaded mem' base code
  | mem, mem', [], h, _, hl => by
    simp only [applyStores, Option.some.injEq] at h
    exact h ▸ hl
  | mem, mem', (a, j, v) :: rest, h, hd, hl => by
    simp only [applyStores] at h
    cases hs : storeN mem (a.eval s0 mem0) j (v.eval s0 mem0) with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs, Option.bind_some] at h
      refine applyStores_loaded h (fun p hp => hd p (List.mem_cons_of_mem _ hp)) ?_
      refine Loaded.of_stored hl (Stored.of_storeN hs) ?_
      simpa using hd _ List.mem_cons_self

theorem split_eval (s : State) (mem : Memory) (e : Ex) :
    (split e).1.eval s mem + (split e).2 = e.eval s mem := by
  unfold split
  split
  · simp [Ex.eval, aluW, AluOp.resultN]
    rfl
  · simp

theorem disjoint_sound {a b : Ex} {k j : Nat} (h : disjoint a k b j = true) (s : State)
    (mem : Memory) :
    (a.eval s mem).toNat + k ≤ (b.eval s mem).toNat ∨
      (b.eval s mem).toNat + j ≤ (a.eval s mem).toNat := by
  simp only [disjoint, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hb, hk⟩, hj⟩ := h
  rw [← split_eval s mem a, ← split_eval s mem b, hb]
  generalize (split b).1.eval s mem = x at *
  generalize (split a).2 = c at *
  generalize (split b).2 = d at *
  have hdiff : (x + d) - (x + c) = d - c := by
    bv_omega
  have hdiff' : (x + c) - (x + d) = c - d := by
    bv_omega
  by_cases hle : (x + c).toNat ≤ (x + d).toNat
  · left
    have := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)
    rw [hdiff] at this
    omega
  · right
    have := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show (x + d).toNat ≤ (x + c).toNat by omega))
    rw [hdiff'] at this
    omega

/-! ## Soundness: one instruction -/

/-- The simulation relation: the concrete registers are the symbolic ones
evaluated at the entry, the concrete memory is the entry memory with the
symbolic stores applied, and the flag claim holds. -/
structure Rel (s0 : State) (mem0 : Memory) (σ : SSt) (s : State) (mem : Memory) : Prop where
  regs : ∀ r, s.read r = (σ.regs r).eval s0 mem0
  mem : applyStores s0 mem0 mem0 σ.stores = some mem
  flags : σ.flags.Holds s0 mem0 s.flags

theorem Rel.init (s : State) (mem : Memory) : Rel s mem SSt.init s mem where
  regs _ := rfl
  mem := rfl
  flags := trivial

variable {s0 : State} {mem0 : Memory}

theorem regs_set {σ : SSt} {s : State} (h : ∀ r, s.read r = (σ.regs r).eval s0 mem0)
    {dst : Reg} {v : Word} {e : Ex} (hv : v = e.eval s0 mem0) :
    ∀ r, (s.write dst v).read r = ((σ.set dst e).regs r).eval s0 mem0 := by
  intro r
  by_cases hr : r = dst
  · subst hr; simp [SSt.set, hv]
  · simp [SSt.set, hr, h r]

theorem addrEx_eval {σ : SSt} {m : Mem} {a : Ex} (ha : addrEx σ m = some a) {s : State}
    (h : ∀ r, s.read r = (σ.regs r).eval s0 mem0) (next : Word) :
    m.addr s next = a.eval s0 mem0 := by
  obtain ⟨base, index, disp, _⟩ := m
  cases base <;> simp only [addrEx, Option.some.injEq, reduceCtorEq] at ha <;> subst ha <;>
    cases index <;>
    simp [Mem.addr, Ex.eval, aluW, shiftW, AluOp.resultN, ShiftOp.result, Index.value, h] <;>
    first | rfl |
      (erw [BitVec.add_zero]; try rfl) | (erw [BitVec.zero_add]; try rfl)

theorem setWidth_signExtend_setWidth (sz : Sz) {w : Nat} (imm : BitVec w) :
    (((imm.signExtend sz.bits).setWidth 64).setWidth sz.bits) = imm.signExtend sz.bits := by
  cases sz <;> simp

theorem aluTo_rel_cmp {σ : SSt} {s : State} {mem : Memory} (hr : Rel s0 mem0 σ s mem)
    {sz : Sz} {dst : Reg} {y : Ex} {yv : BitVec sz.bits}
    (hy : yv = (y.eval s0 mem0).setWidth sz.bits) (x : Word) :
    Rel s0 mem0 (σ.aluTo sz .cmp dst y)
      { s with flags := subFlagsN (sz.read s dst) yv, rip := x } mem where
  regs r := hr.regs r
  mem := hr.mem
  flags := by
    simp only [SSt.aluTo, ite_true, FlagSum.Holds, Sz.read, hy, hr.regs dst]

theorem aluTo_rel_op {σ : SSt} {s : State} {mem : Memory} (hr : Rel s0 mem0 σ s mem)
    {sz : Sz} {op : AluOp} (hop : op ≠ .cmp) {dst : Reg} {y : Ex} {yv : BitVec sz.bits}
    (hy : yv = (y.eval s0 mem0).setWidth sz.bits) (f : Flags) (x : Word) :
    Rel s0 mem0 (σ.aluTo sz op dst y)
      { sz.write s dst (AluOp.resultN op (sz.read s dst) yv) with flags := f, rip := x } mem where
  regs r := by
    simp only [SSt.aluTo, hop, ite_false]
    exact regs_set hr.regs (by simp [Ex.eval, aluW, Sz.read, hy, hr.regs dst]) r
  mem := by simp only [SSt.aluTo, hop, ite_false]; exact hr.mem
  flags := by simp only [SSt.aluTo, hop, ite_false]; trivial

/-- The declared aliasing assumptions hold at the entry. -/
def AssumeHolds (s0 : State) (mem0 : Memory) (asm : Assume) : Prop :=
  ∀ q ∈ asm, (q.1.eval s0 mem0).toNat + q.2.1 ≤ (q.2.2.1.eval s0 mem0).toNat ∨
    (q.2.2.1.eval s0 mem0).toNat + q.2.2.2 ≤ (q.1.eval s0 mem0).toNat

/-- A load of the fragment reads the entry memory, and succeeds. -/
theorem load_ok {asm : Assume} (hasm : AssumeHolds s0 mem0 asm) {σ : SSt} {s : State}
    {mem : Memory} (hr : Rel s0 mem0 σ s mem) {a : Ex}
    {k : Nat} (hok : σ.loadOk asm a k = true)
    (hread : (loadN mem0 (a.eval s0 mem0) k).isSome) :
    loadN mem (a.eval s0 mem0) k = some ((loadN mem0 (a.eval s0 mem0) k).getD 0) := by
  rw [applyStores_loadN hr.mem]
  · cases h : loadN mem0 (a.eval s0 mem0) k
    · rw [h] at hread; cases hread
    · rfl
  · intro p hp
    have := List.all_eq_true.mp hok p hp
    simp only [Bool.or_eq_true, List.contains_iff_mem] at this
    rcases this with h | h
    · exact disjoint_sound h s0 mem0
    · exact hasm _ h

/-- What one accepted instruction must do: from any related state whose new
loads are backed and new stores writable, retire, advance RIP by its length and
re-establish the relation. -/
def StepOk (s0 : State) (mem0 : Memory) (σ σ' : SSt) (i : Ext.Instr) : Prop :=
  ∀ {s : State} {mem : Memory}, Rel s0 mem0 σ s mem →
    (∀ p ∈ σ'.reads, (loadN mem0 (p.1.eval s0 mem0) p.2).isSome) →
    (∀ p ∈ σ'.stores, mem0.Permitted .write (p.1.eval s0 mem0).toNat p.2.1) →
    ∃ t mem', exec i s mem = .ok t mem' ∧ t.rip = s.rip + BitVec.ofNat 64 i.length ∧
      Rel s0 mem0 σ' t mem'

variable {σ σ' : SSt} {asm : Assume}

theorem step_mov_reg {sz : Sz} {dst src : Reg} (h : symStep asm σ (.mov sz (.reg dst) src) = some σ') :
    StepOk s0 mem0 σ σ' (.mov sz (.reg dst) src) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  refine ⟨_, _, exec_mov_reg s mem sz dst src, rfl, ?_, hr.mem, hr.flags⟩
  exact regs_set hr.regs (by simp [Ex.eval, extW, Sz.read, hr.regs src])

theorem step_mov_mem {sz : Sz} {m : Mem} {src : Reg}
    (h : symStep asm σ (.mov sz (.mem m) src) = some σ') :
    StepOk s0 mem0 σ σ' (.mov sz (.mem m) src) := by
  intro s mem hr _ hwrites
  simp only [symStep, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  have hw := hwrites (a, sz.bytes, .ext sz (σ.regs src)) (by simp [SSt.store])
  have hw' := applyStores_permitted hr.mem hw
  obtain ⟨after, hst, -⟩ := storeN_isSome (v := (sz.read s src).setWidth 64) hw'
  refine ⟨{ s with rip := s.rip + BitVec.ofNat 64 (Instr.mov sz (.mem m) src).length }, after,
    ?_, rfl, hr.regs, ?_, hr.flags⟩
  · rw [exec_store, addrEx_eval ha hr.regs, hst]
  · simp only [SSt.store]
    rw [applyStores_append, hr.mem, Option.bind_some, ← hst]
    simp [Ex.eval, extW, Sz.read, hr.regs src]

theorem step_load (hasm : AssumeHolds s0 mem0 asm) {sz : Sz} {dst : Reg} {m : Mem}
    (h : symStep asm σ (.load sz dst m) = some σ') :
    StepOk s0 mem0 σ σ' (.load sz dst m) := by
  intro s mem hr hreads _
  simp only [symStep, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  split at h
  · rename_i hok
    simp only [Option.some.injEq] at h; subst h
    have hread := hreads (a, sz.bytes) (by simp [SSt.set, SSt.read])
    refine ⟨{ Sz.write sz s dst (((loadN mem0 (a.eval s0 mem0) sz.bytes).getD 0).setWidth sz.bits)
      with rip := s.rip + BitVec.ofNat 64 (Instr.load sz dst m).length }, mem, ?_, rfl, ?_, hr.mem,
      hr.flags⟩
    · rw [exec_load, addrEx_eval ha hr.regs, load_ok hasm hr hok hread]
    · exact regs_set (σ := σ.read a sz.bytes) hr.regs (by simp [Ex.eval, extW])
  · cases h

theorem step_alu {sz : Sz} {op : AluOp} {dst src : Reg}
    (h : symStep asm σ (.alu sz op (.reg dst) src) = some σ') :
    StepOk s0 mem0 σ σ' (.alu sz op (.reg dst) src) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  by_cases hop : op = .cmp
  · subst hop
    exact ⟨_, _, exec_cmp_reg s mem sz dst src, rfl,
      aluTo_rel_cmp hr (by simp [Sz.read, hr.regs src]) _⟩
  · exact ⟨_, _, exec_alu_reg s mem sz op dst src hop, rfl,
      aluTo_rel_op hr hop (by simp [Sz.read, hr.regs src]) _ _⟩

theorem step_aluR_reg {sz : Sz} {op : AluOp} {dst src : Reg}
    (h : symStep asm σ (.aluR sz op dst (.reg src)) = some σ') :
    StepOk s0 mem0 σ σ' (.aluR sz op dst (.reg src)) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  by_cases hop : op = .cmp
  · subst hop
    exact ⟨_, _, exec_cmpR_reg s mem sz dst src, rfl,
      aluTo_rel_cmp hr (by simp [Sz.read, hr.regs src]) _⟩
  · exact ⟨_, _, exec_aluR_reg s mem sz op dst src hop, rfl,
      aluTo_rel_op hr hop (by simp [Sz.read, hr.regs src]) _ _⟩

theorem step_aluR_mem (hasm : AssumeHolds s0 mem0 asm) {sz : Sz} {op : AluOp} {dst : Reg} {m : Mem}
    (h : symStep asm σ (.aluR sz op dst (.mem m)) = some σ') :
    StepOk s0 mem0 σ σ' (.aluR sz op dst (.mem m)) := by
  intro s mem hr hreads _
  simp only [symStep, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  split at h
  · rename_i hok
    simp only [Option.some.injEq] at h; subst h
    have hread := hreads (a, sz.bytes) (by
      unfold SSt.aluTo; split <;> simp [SSt.set, SSt.read])
    have hl := load_ok hasm hr hok hread
    have hr' : Rel s0 mem0 (σ.read a sz.bytes) s mem := ⟨hr.regs, hr.mem, hr.flags⟩
    by_cases hop : op = .cmp
    · subst hop
      refine ⟨_, _, ?_, ?_, aluTo_rel_cmp hr' (y := .ld a sz.bytes)
        (yv := ((Ex.ld a sz.bytes).eval s0 mem0).setWidth sz.bits) rfl
        (s.rip + BitVec.ofNat 64 (Instr.aluR sz .cmp dst (.mem m)).length)⟩
      · rw [exec_cmpR_mem, addrEx_eval ha hr.regs, hl]
        rfl
      · rfl
    · refine ⟨_, _, ?_, ?_, aluTo_rel_op hr' hop (y := .ld a sz.bytes)
        (yv := ((Ex.ld a sz.bytes).eval s0 mem0).setWidth sz.bits) rfl
        (AluOp.flagsN op (sz.read s dst) (((Ex.ld a sz.bytes).eval s0 mem0).setWidth sz.bits))
        (s.rip + BitVec.ofNat 64 (Instr.aluR sz op dst (.mem m)).length)⟩
      · simp only [exec, retire, aluStepR, readRM, addrEx_eval ha hr.regs, hl, hop, ite_false,
          Option.map_some]
        rfl
      · rfl
  · cases h

theorem step_aluI {sz : Sz} {op : AluOp} {dst : Reg} {imm : BitVec 32}
    (h : symStep asm σ (.aluI sz op (.reg dst) imm) = some σ') :
    StepOk s0 mem0 σ σ' (.aluI sz op (.reg dst) imm) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  by_cases hop : op = .cmp
  · subst hop
    exact ⟨_, _, exec_cmpI_reg s mem sz dst imm, rfl,
      aluTo_rel_cmp hr (by simp [Ex.eval, setWidth_signExtend_setWidth]) _⟩
  · exact ⟨_, _, exec_aluI_reg s mem sz op dst imm hop, rfl,
      aluTo_rel_op hr hop (by simp [Ex.eval, setWidth_signExtend_setWidth]) _ _⟩

theorem step_aluI8 {sz : Sz} {op : AluOp} {dst : Reg} {imm : BitVec 8}
    (h : symStep asm σ (.aluI8 sz op (.reg dst) imm) = some σ') :
    StepOk s0 mem0 σ σ' (.aluI8 sz op (.reg dst) imm) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  by_cases hop : op = .cmp
  · subst hop
    exact ⟨_, _, exec_cmpI8_reg s mem sz dst imm, rfl,
      aluTo_rel_cmp hr (by simp [Ex.eval, setWidth_signExtend_setWidth]) _⟩
  · exact ⟨_, _, exec_aluI8_reg s mem sz op dst imm hop, rfl,
      aluTo_rel_op hr hop (by simp [Ex.eval, setWidth_signExtend_setWidth]) _ _⟩

theorem step_aluA {sz : Sz} {op : AluOp} {imm : BitVec 32}
    (h : symStep asm σ (.aluA sz op imm) = some σ') :
    StepOk s0 mem0 σ σ' (.aluA sz op imm) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  by_cases hop : op = .cmp
  · subst hop
    exact ⟨_, _, exec_cmpA s mem sz imm, rfl,
      aluTo_rel_cmp hr (by simp [Ex.eval, setWidth_signExtend_setWidth]) _⟩
  · exact ⟨_, _, exec_aluA_nonCmp s mem sz op imm hop, rfl,
      aluTo_rel_op hr hop (by simp [Ex.eval, setWidth_signExtend_setWidth]) _ _⟩

theorem step_shift {sz : Sz} {op : ShiftOp} {dst : Reg} {n : BitVec 8}
    (h : symStep asm σ (.shift sz op (.reg dst) (.imm n)) = some σ') :
    StepOk s0 mem0 σ σ' (.shift sz op (.reg dst) (.imm n)) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  refine ⟨_, _, exec_shift_reg s mem sz op dst (.imm n), rfl, ?_, hr.mem, trivial⟩
  exact regs_set hr.regs (by simp [Ex.eval, shiftW, Sz.read, Count.raw, hr.regs dst])

theorem step_incdec {sz : Sz} {dec : Bool} {dst : Reg}
    (h : symStep asm σ (.incdec sz dec (.reg dst)) = some σ') :
    StepOk s0 mem0 σ σ' (.incdec sz dec (.reg dst)) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  refine ⟨_, _, exec_incdec_reg s mem sz dec dst, rfl, ?_, hr.mem, trivial⟩
  refine regs_set hr.regs ?_
  cases dec <;> cases sz <;> simp [Ex.eval, aluW, AluOp.resultN, Sz.read, hr.regs dst]

theorem step_lea {dst : Reg} {m : Mem} (h : symStep asm σ (.lea .q dst m) = some σ') :
    StepOk s0 mem0 σ σ' (.lea .q dst m) := by
  intro s mem hr _ _
  simp only [symStep, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨_, _, exec_lea s mem dst m, rfl, ?_, hr.mem, hr.flags⟩
  exact regs_set hr.regs (addrEx_eval ha hr.regs _)

theorem step_movI32 {dst : Reg} {imm : BitVec 32} (h : symStep asm σ (.movI32 dst imm) = some σ') :
    StepOk s0 mem0 σ σ' (.movI32 dst imm) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  exact ⟨_, _, exec_movI32 s mem dst imm, rfl, regs_set hr.regs rfl, hr.mem, hr.flags⟩

theorem step_unary {sz : Sz} {op : UnOp} {dst : Reg}
    (h : symStep asm σ (.unary sz op (.reg dst)) = some σ') :
    StepOk s0 mem0 σ σ' (.unary sz op (.reg dst)) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  cases op
  · refine ⟨_, _, exec_neg_reg s mem sz dst, rfl, ?_, hr.mem, trivial⟩
    exact regs_set hr.regs (by simp [Ex.eval, unW, Sz.read, hr.regs dst])
  · refine ⟨_, _, exec_not_reg s mem sz dst, rfl, ?_, hr.mem, trivial⟩
    exact regs_set hr.regs (by simp [Ex.eval, unW, Sz.read, hr.regs dst])

theorem step_bswap {sz : Sz} {dst : Reg} (h : symStep asm σ (.bswap sz dst) = some σ') :
    StepOk s0 mem0 σ σ' (.bswap sz dst) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  refine ⟨_, _, exec_bswap s mem sz dst, rfl, ?_, hr.mem, hr.flags⟩
  exact regs_set hr.regs (by simp [Ex.eval, bswapW, Sz.read, hr.regs dst])

theorem step_nop {len : Fin 15} (h : symStep asm σ (.nop len) = some σ') :
    StepOk s0 mem0 σ σ' (.nop len) := by
  intro s mem hr _ _
  simp only [symStep, Option.some.injEq] at h; subst h
  exact ⟨_, _, exec_nop s mem len, rfl, hr.regs, hr.mem, hr.flags⟩

/-- **One instruction**, dispatched over the fragment. -/
theorem symStep_sound (hasm : AssumeHolds s0 mem0 asm) {i : Ext.Instr}
    (h : symStep asm σ i = some σ') : StepOk s0 mem0 σ σ' i := by
  cases i
  case mov sz dst src =>
    cases dst
    · exact step_mov_reg h
    · exact step_mov_mem h
  case load sz dst m => exact step_load hasm h
  case alu sz op dst src =>
    cases dst
    · exact step_alu h
    · simp [symStep] at h
  case aluR sz op dst src =>
    cases src
    · exact step_aluR_reg h
    · exact step_aluR_mem hasm h
  case aluI sz op dst imm =>
    cases dst
    · exact step_aluI h
    · simp [symStep] at h
  case aluI8 sz op dst imm =>
    cases dst
    · exact step_aluI8 h
    · simp [symStep] at h
  case aluA sz op imm => exact step_aluA h
  case shift sz op dst count =>
    cases dst
    · cases count
      · simp [symStep] at h
      · simp [symStep] at h
      · exact step_shift h
    · simp [symStep] at h
  case incdec sz dec dst =>
    cases dst
    · exact step_incdec h
    · simp [symStep] at h
  case lea sz dst m =>
    cases sz
    · simp [symStep] at h
    · exact step_lea h
  case movI32 dst imm => exact step_movI32 h
  case unary sz op dst =>
    cases dst
    · exact step_unary h
    · simp [symStep] at h
  case bswap sz dst => exact step_bswap h
  case nop len => exact step_nop h
  all_goals simp [symStep] at h

/-! ## Soundness: a block -/

/-- The loads and stores of `σ` are among those of `σ'`. -/
def SSt.Le (σ σ' : SSt) : Prop :=
  (∀ p ∈ σ.reads, p ∈ σ'.reads) ∧ (∀ p ∈ σ.stores, p ∈ σ'.stores)

theorem SSt.Le.refl (σ : SSt) : σ.Le σ := ⟨fun _ h => h, fun _ h => h⟩

theorem SSt.Le.trans {σ₁ σ₂ σ₃ : SSt} (a : σ₁.Le σ₂) (b : σ₂.Le σ₃) : σ₁.Le σ₃ :=
  ⟨fun p h => b.1 p (a.1 p h), fun p h => b.2 p (a.2 p h)⟩

@[simp] theorem SSt.set_reads (σ : SSt) (r : Reg) (e : Ex) : (σ.set r e).reads = σ.reads := rfl
@[simp] theorem SSt.set_stores (σ : SSt) (r : Reg) (e : Ex) : (σ.set r e).stores = σ.stores := rfl
@[simp] theorem SSt.read_reads (σ : SSt) (a : Ex) (k : Nat) :
    (σ.read a k).reads = σ.reads ++ [(a, k)] := rfl
@[simp] theorem SSt.read_stores (σ : SSt) (a : Ex) (k : Nat) : (σ.read a k).stores = σ.stores := rfl
@[simp] theorem SSt.store_reads (σ : SSt) (a : Ex) (k : Nat) (v : Ex) :
    (σ.store a k v).reads = σ.reads := rfl
@[simp] theorem SSt.store_stores (σ : SSt) (a : Ex) (k : Nat) (v : Ex) :
    (σ.store a k v).stores = σ.stores ++ [(a, k, v)] := rfl
@[simp] theorem SSt.aluTo_reads (σ : SSt) (sz : Sz) (op : AluOp) (dst : Reg) (y : Ex) :
    (σ.aluTo sz op dst y).reads = σ.reads := by unfold SSt.aluTo; split <;> rfl
@[simp] theorem SSt.aluTo_stores (σ : SSt) (sz : Sz) (op : AluOp) (dst : Reg) (y : Ex) :
    (σ.aluTo sz op dst y).stores = σ.stores := by unfold SSt.aluTo; split <;> rfl

theorem SSt.le_of {σ σ' : SSt} (hr : ∀ p ∈ σ.reads, p ∈ σ'.reads)
    (hs : ∀ p ∈ σ.stores, p ∈ σ'.stores) : σ.Le σ' := ⟨hr, hs⟩

theorem symStep_le {i : Ext.Instr} (h : symStep asm σ i = some σ') : σ.Le σ' := by
  cases i
  case mov sz dst src => cases dst
                         · (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
                         · (simp only [symStep, Option.map_eq_some_iff] at h; obtain ⟨a, _, rfl⟩ := h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
  case load sz dst m => (simp only [symStep, Option.bind_eq_some_iff] at h; obtain ⟨a, _, h⟩ := h; split at h <;> [(simp only [Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all)); cases h])
  case alu sz op dst src => cases dst
                            · (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
                            · simp [symStep] at h
  case aluR sz op dst src => cases src
                             · (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
                             · (simp only [symStep, Option.bind_eq_some_iff] at h; obtain ⟨a, _, h⟩ := h; split at h <;> [(simp only [Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all)); cases h])
  case aluI sz op dst imm => cases dst
                             · (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
                             · simp [symStep] at h
  case aluI8 sz op dst imm => cases dst
                              · (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
                              · simp [symStep] at h
  case shift sz op dst count =>
    cases dst
    · cases count
      · simp [symStep] at h
      · simp [symStep] at h
      · (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
    · simp [symStep] at h
  case incdec sz dec dst => cases dst
                            · (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
                            · simp [symStep] at h
  case lea sz dst m => cases sz
                       · simp [symStep] at h
                       · (simp only [symStep, Option.map_eq_some_iff] at h; obtain ⟨a, _, rfl⟩ := h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
  case movI32 dst imm => (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
  case unary sz op dst => cases dst
                          · (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
                          · simp [symStep] at h
  case bswap sz dst => (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
  case aluA sz op imm => (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
  case nop len => (simp only [symStep, Option.some.injEq] at h; subst h; exact SSt.le_of (fun p hp => by simp_all) (fun p hp => by simp_all))
  all_goals simp [symStep] at h

theorem SSt.Le.of_len {σ σf : SSt} {l : Nat} (h : SSt.Le { σ with len := l } σf) : σ.Le σf := h

theorem run_le (code : List Byte) : ∀ (n : Nat) (σ σf : SSt), run asm code n σ = some σf → σ.Le σf
  | 0, σ, σf, h => by
    simp only [run, Option.some.injEq] at h; subst h; exact SSt.Le.refl σ
  | n + 1, σ, σf, h => by
    simp only [run] at h
    split at h
    · cases h
    · split at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨σ', h1, h2⟩ := h
        exact (symStep_le h1).trans (SSt.Le.of_len (run_le code n _ σf h2))
      · cases h

/-- **The block.** If the checker's symbolic run accepts `n` instructions of a
loaded `code` from the state `σ`, then from any machine state related to `σ`
at RIP `base + σ.len`, `n` retirements reach a state related to the final
symbolic state, at RIP `base + σf.len`. -/
theorem run_sound (hasm : AssumeHolds s0 mem0 asm) {code : List Byte} {base exit : Word}
    (hlen : base.toNat + code.length ≤ 2 ^ 64) :
    ∀ (n : Nat) (σ σf : SSt) (m : MState), run asm code n σ = some σf →
      Rel s0 mem0 σ m.core m.memory → m.core.rip = base + BitVec.ofNat 64 σ.len →
      Loaded mem0 base code →
      (∀ p ∈ σf.reads, (loadN mem0 (p.1.eval s0 mem0) p.2).isSome) →
      (∀ p ∈ σf.stores, mem0.Permitted .write (p.1.eval s0 mem0).toNat p.2.1) →
      (∀ p ∈ σf.stores, base.toNat + code.length ≤ (p.1.eval s0 mem0).toNat ∨
        (p.1.eval s0 mem0).toNat + p.2.1 ≤ base.toNat) →
      ∃ m', Runs exit n m m' ∧ Rel s0 mem0 σf m'.core m'.memory ∧
        m'.core.rip = base + BitVec.ofNat 64 σf.len
  | 0, σ, σf, m, h, hr, hrip, _, _, _, _ => by
    simp only [run, Option.some.injEq] at h; subst h
    exact ⟨m, Runs.nil m, hr, hrip⟩
  | n + 1, σ, σf, m, h, hr, hrip, hl, hreads, hwrites, hcode => by
    simp only [run] at h
    split at h
    · cases h
    · rename_i i l hdec15
      split at h
      · rename_i hcond
        obtain ⟨hdec, hfits⟩ := hcond
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨σ', h1, h2⟩ := h
        have hle' : σ'.Le σf := SSt.Le.of_len (run_le code n _ σf h2)
        have hloaded : Loaded m.memory base code :=
          applyStores_loaded hr.mem (fun p hp => hcode p (hle'.2 p ((symStep_le h1).2 p hp))) hl
        obtain ⟨t, mem', hexec, htrip, hr'⟩ := symStep_sound hasm h1 hr
          (fun p hp => hreads p (hle'.1 p hp)) (fun p hp => hwrites p (hle'.2 p hp))
        have hnotret : i ≠ .ret := by
          rintro rfl; simp [symStep] at h1
        have hstep := stepOpt_of_loaded (exit := exit) hloaded hrip hfits hdec hnotret hexec
        have hil : i.length = l := (decode_length hdec).1.symm
        obtain ⟨mf, hrun, hrf, hripf⟩ := run_sound hasm hlen n { σ' with len := σ.len + l } σf ⟨t, mem'⟩ h2
          ⟨hr'.regs, hr'.mem, hr'.flags⟩
          (by
            show t.rip = _
            rw [htrip, hrip, hil, BitVec.ofNat_add, BitVec.add_assoc])
          hl hreads hwrites hcode
        exact ⟨mf, Runs.cons hstep hrun, hrf, hripf⟩
      · cases h

/-- **The translation-validation theorem.** An accepted summary describes the
machine. From any state whose RIP is `base` and whose memory holds `code`
there, `n` retirements reach a state whose RIP is past the block, whose
live-out registers hold the summary's expressions evaluated at the entry,
whose memory is the entry memory with the summary's stores applied in order,
and whose flags satisfy the summary's flag claim — provided the summary's
loads are backed, its stores writable, and its stores clear of the code. -/
theorem check_sound {code : List Byte} {n : Nat} {spec : Summary} (hc : check code n spec = true)
    {base exit : Word} (hlen : base.toNat + code.length ≤ 2 ^ 64) (m : MState)
    (hl : Loaded m.memory base code) (hrip : m.core.rip = base)
    (hreads : ∀ p ∈ spec.reads, (loadN m.memory (p.1.eval m.core m.memory) p.2).isSome)
    (hwrites : ∀ p ∈ spec.stores,
      m.memory.Permitted .write (p.1.eval m.core m.memory).toNat p.2.1)
    (hcode : ∀ p ∈ spec.stores, base.toNat + code.length ≤ (p.1.eval m.core m.memory).toNat ∨
      (p.1.eval m.core m.memory).toNat + p.2.1 ≤ base.toNat)
    (hasm : AssumeHolds m.core m.memory spec.assume) :
    ∃ m', Runs exit n m m' ∧
      m'.core.rip = base + BitVec.ofNat 64 spec.len ∧
      (∀ p ∈ spec.outs, m'.core.read p.1 = p.2.eval m.core m.memory) ∧
      applyStores m.core m.memory m.memory spec.stores = some m'.memory ∧
      spec.flags.Holds m.core m.memory m'.core.flags := by
  unfold check at hc
  split at hc
  · rename_i σ hrun
    simp only [Summary.matches, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨houts, hst⟩, hrd⟩, hln⟩, hfl⟩ := hc
    simp only [← hst, ← hrd, ← hln, ← hfl] at hreads hwrites hcode ⊢
    obtain ⟨m', hrun', hr', hrip'⟩ := run_sound (s0 := m.core) (mem0 := m.memory) (exit := exit)
      hasm hlen n SSt.init σ m hrun (Rel.init m.core m.memory) (by rw [hrip]; simp [SSt.init]) hl
      hreads hwrites hcode
    refine ⟨m', hrun', hrip', fun p hp => ?_, hr'.mem, hr'.flags⟩
    rw [hr'.regs p.1, houts p hp]
  · cases hc

end Silmaril.X86.Decompile.SemLift

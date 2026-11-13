module

public import Silmaril.X86.Decompile.Cfg
public import Silmaril.Machine.X86.Lir.Correct.Defs
public import Silmaril.Machine.CBackend.Lift.Abstraction.Defs
public import Silmaril.Machine.CBackend.RTL.ToLir.Defs
/-!
# Rung 2½: lifting a recovered basic block to a Lir block

`Decompile.checkCfg` says where the basic blocks of a function are and which
block reaches which. It says nothing about what a block *computes*, because
nothing in rungs 1 and 2 has a notion of a program variable. This file is the
step that introduces one: an agent proposes the **Lir block** a recovered run of
x86 instructions came from, and `checkBlock` verifies the proposal.

## The idea: translation validation by recompilation

The proposal is untrusted. The check is not an analysis of the recovered bytes
at all — it is a *recompilation*:

> the agent says "these instructions are what the backend emits for this Lir
> block, with these registers"; the checker runs the backend's own emitter on
> the proposed block and compares the result with the recovered instructions,
> instruction for instruction.

This is the same move as `Machine.Lift.checkAbstraction` (rung 3), which
recompiles a proposed RTL program and compares `Lir.Prog`s, and it is the single
most reusable idea in the toolkit. It is cheap — a `DecidableEq` comparison on
`List Decoded` — total, and decidable, and it buys the whole of the backend's
correctness theory: once the recovered instructions *are* `X86.Backend.blockCode`
for a Lir block, every theorem of `X86/Lir/{Ops,Step,Moves,Seq,Sim,Correct}.lean`
applies to them unchanged.

## What a proposal is

`Lift.BlockSpec` is the context the emitter needs, which is more than one block:
the backend's instruction selection is per-block, but *addresses* are not. A
`jmp` to a label resolves to a displacement that depends on where every other
block of the program sits, so the proposal carries the whole Lir program, the
register assignment, the code base, and the function and label of the block in
question. `BlockSpec.emit` is then the decoded listing the backend produces for
that one block, at the address `X86.Backend.layout` gives it.

Nothing about the proposal is checked except by re-emission: `checkBlock`
recomputes `progErrors`, `layout` and `blockCode` from the proposal alone and
compares.

## What acceptance means

`checkBlock c blk spec = .ok ()` says, for the recovered block `blk` of the
checked control-flow graph `c`:

* `blk` really is a block of `c` (`checkBlock_mem`) — without this the vacuous
  `CheckedCfg.body` of an unknown block would match an empty emission;
* the proposal compiles (`checkBlock_errors`), so `Env.Ok` is within reach;
* `blk` starts where the layout puts the proposed block (`checkBlock_addr`);
* **the recovered instructions from there are exactly the emitted ones**
  (`checkBlock_run`), hence the recovered *bytes* are exactly the compiled bytes
  (`checkBlock_bytes`);
* and the recovered block itself is a prefix of them (`checkBlock_prefix`).

## A Lir block is not always one recovered block

The comparison is against `recoveredRun`, the recovered instructions of the
function from `blk.start` onwards, and not against `CheckedCfg.body blk`, which
would be the obvious choice and is wrong. One Lir block does not always compile
to one recovered block.

`X86.Backend.termChunk` compiles a Lir `branch` to `test`, `jcc` to one label,
`jmp` to the other. `Jcc` does not retire, so rung 2 must end the recovered
block at it, and the trailing `jmp` becomes a recovered block of its own — the
glue block that `Silmaril/X86/Decompile/RoundTrip.lean` already names and
splices out. A Lir block ending in a `branch` therefore emits code spanning two
recovered blocks, and a checker that compared with `CheckedCfg.body blk` would
reject every branch in every program.

So `checkBlock` compares against the run of recovered instructions the emission
actually occupies, and separately checks that the recovered block is a prefix of
it. `checkBlock_prefix` is then the honest statement of the relationship: the
recovered block is where the Lir block starts, and what follows it inside the
emission is the backend's own glue.

## What the soundness theorem can say

The backend's simulation lemmas (`X86/Lir/Step.lean`) are stated against
`Env.Body`, the relation between a running Lir state and a machine state whose
RIP is the address of the Lir program point. They are per-Lir-step:
`sim_op`, `sim_jump`, `sim_branch`, `sim_trap`, and `sim_callSite`/`sim_ret` in
`Call.lean`/`Return.lean`. There is **no whole-block lemma** — no "run the body
of this block and arrive at the terminator" — so the honest statement is at the
level of one Lir step, and that is what `checkBlock_sound` states, via
`Env.simulation`, which packages all six cases.

What the lift *adds* to those lemmas is the identification of the machine's
instruction stream with the recovered one:

* `checkBlock_rip` — at the entry of the block the machine's RIP is `blk.start`,
  the address of the first recovered instruction;
* `checkBlock_isStart` — at *every* Lir program point of the block the machine's
  RIP is the address of one of the recovered instructions of the run.

Together with `checkBlock_bytes` these say the machine run the simulation
describes is a run through the recovered listing, not merely through some code
that happens to agree with it.

## The composition

`checkFunc` runs `checkBlock` on every block of a proposed Lir function, in
label order. `checkFunc_behaviour` composes it with rung 3
(`Machine.Lift.checkAbstraction`) and with the backend's `compile_correct`:
from an accepted lift of every block, an accepted abstraction of the lifted Lir
program, and a successful compilation, the behaviours of the *recovered bytes*
are the behaviours of the proposed RTL program. That is a statement about a
lifted program's behaviour rather than its shape, which is what rungs 1 and 2
could not give.

`toLir_lowerBehaves` supplies the `LowerBehaves` instance that rung 3 needed and
could not name when it was written: `RTL.toLir` is now in the tree.

## Proof versus test

Everything here is a kernel proof. `checkBlock` is a decidable function and the
tactic `lift_block` (`Silmaril/X86/Decompile/LiftTactic.lean`) closes its goals
by `rfl` or `decide`; there is no compiled evaluation and no `sorry`.
-/

@[expose] public section

namespace Silmaril.X86.Decompile.Lift

open Silmaril.X86 (Byte Word Reg MState State)
open Silmaril.X86.Backend (AInstr Assign Env Error Image Layout Space RStep blockChunks blockCode
  blockChunks_instr blockChunks_length blockChunks_term chunkOff compile emptyBlock emptyFunc
  encodeAt epilogue instrChunk lenOf layout nslots pointAddr progErrors retLoads selOp termChunk)
open Silmaril.Machine
open Silmaril.Machine.Lift (AbstractionSpec LowerBehaves Lowering behaviorToLir checkAbstraction)
open Silmaril.Process (Memory)
open Relation

/-! ## The backend's emission as an addressed listing

`X86.Backend.encodeAt` turns a list of `AInstr`s placed at an address into
bytes. `emitAt` is the same walk, stopping one level earlier: it resolves each
abstract instruction's jump or call target against the layout and records the
address and encoded length, which is exactly the shape `Region.decode?`
produces. The two agree (`emitAt_encode`), so comparing listings and comparing
bytes are the same comparison. -/

/-- The decoded listing the backend produces for abstract instructions placed
at `addr`: each one resolved against the layout at its own address, with that
address and its encoded length. -/
def emitAt (L : Layout) : Nat → List AInstr → List Decoded
  | _, [] => []
  | a, i :: is => ⟨a, i.resolve L a, i.len⟩ :: emitAt L (a + i.len) is

/-- Emission distributes over concatenation, with the tail placed after the
head. -/
theorem emitAt_append (L : Layout) (a : Nat) (xs ys : List AInstr) :
    emitAt L a (xs ++ ys) = emitAt L a xs ++ emitAt L (a + lenOf xs) ys := by
  induction xs generalizing a with
  | nil => simp [emitAt]
  | cons i is ih => simp [emitAt, ih, Nat.add_assoc]

/-- One decoded instruction per abstract instruction. -/
@[simp] theorem emitAt_length (L : Layout) (a : Nat) (is : List AInstr) :
    (emitAt L a is).length = is.length := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih => simp [emitAt, ih]

/-- **Emitting and then encoding is encoding.** The bytes of the emitted
listing are the bytes `encodeAt` produces, so a listing comparison is a byte
comparison. -/
theorem emitAt_encode (L : Layout) (a : Nat) (is : List AInstr) :
    (emitAt L a is).flatMap (fun d => Ext.encode d.instr) = encodeAt L a is := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih => simp [emitAt, encodeAt, ih]

/-- Every emitted instruction's recorded size is its encoded length, as
`Region.decode?` also guarantees. -/
theorem emitAt_size (L : Layout) (a : Nat) (is : List AInstr) :
    ∀ d ∈ emitAt L a is, (Ext.encode d.instr).length = d.size := by
  induction is generalizing a with
  | nil => simp [emitAt]
  | cons i is ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Silmaril.X86.Backend.encode_resolve_length L a i
    · exact ih _ d hd

/-- A non-empty emission begins at the address it was placed at. -/
theorem emitAt_isStart (L : Layout) (a : Nat) {is : List AInstr} (h : is ≠ []) :
    IsStart (emitAt L a is) a := by
  obtain ⟨i, is, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [IsStart, starts, emitAt]

/-- An emission's addresses are preserved by a prefix: anything the tail starts
is started by the whole. -/
theorem isStart_emitAt_append (L : Layout) (a : Nat) (xs ys : List AInstr) {addr : Nat}
    (h : IsStart (emitAt L (a + lenOf xs) ys) addr) : IsStart (emitAt L a (xs ++ ys)) addr := by
  rw [emitAt_append]
  simpa [IsStart, starts] using Or.inr h

/-! ## Proposals -/

/-- A proposed lifting of one recovered basic block: the Lir block it came from
and the context the backend's emitter needs to place it.

The emitter needs more than the block: a `jmp` to a label is encoded as a
displacement, so the address of *every* block of the program takes part. The
proposal therefore carries the whole Lir program and the code base, and names
the block by its function and label. `func` and `label` are `Nat` rather than
`Lir.FuncId` and `Lir.Label` because `omega` does not see through those
abbreviations. -/
structure BlockSpec (P : Type) where
  /-- The Lir program the block is proposed to belong to. -/
  prog : Lir.Prog P
  /-- The assignment of Lir registers to x86-64 registers. -/
  assign : Assign P
  /-- The address the program's code is proposed to start at. -/
  codeBase : Nat
  /-- The index of the function the block belongs to. -/
  func : Nat
  /-- The label of the block within that function. -/
  label : Nat

namespace BlockSpec

variable {P : Type} (spec : BlockSpec P)

/-- The layout the backend would place the proposed program with. -/
def layout : Layout := Silmaril.X86.Backend.layout spec.assign spec.prog spec.codeBase

/-- The address the layout gives the proposed block. -/
def addr : Nat := spec.layout.block spec.func spec.label

/-- The proposed function. -/
def func? : Option (Lir.Func P) := spec.prog.func? spec.func

/-- The number of stack slots the proposed function uses, as the backend counts
them. -/
def slotCount : Nat := nslots (spec.func?.getD emptyFunc)

/-- The proposed block. -/
def block? : Option (Lir.Block P) := spec.prog.block? spec.func spec.label

/-- The abstract instructions the backend emits for the proposed block, or `[]`
when the proposal names no block. -/
def code : List AInstr :=
  match spec.block? with
  | none => []
  | some b => blockCode spec.assign spec.func spec.slotCount b

/-- **The listing the backend emits for the proposed block**, at the address
the layout gives it. This is what `checkBlock` compares the recovered
instructions against. -/
def emit : List Decoded := emitAt spec.layout spec.addr spec.code

end BlockSpec

/-- A proposed lifting of a whole recovered function: the Lir function, and the
recovered block each of its Lir blocks was lifted from, in label order. -/
structure FuncSpec (P : Type) where
  /-- The Lir program the function is proposed to belong to. -/
  prog : Lir.Prog P
  /-- The assignment of Lir registers to x86-64 registers. -/
  assign : Assign P
  /-- The address the program's code is proposed to start at. -/
  codeBase : Nat
  /-- The index of the proposed function. -/
  func : Nat
  /-- The recovered block of Lir label `l`, at index `l`. -/
  blocks : List Decompile.BlockSpec

/-- The block proposal for one label of a function proposal. -/
def FuncSpec.blockSpec {P : Type} (spec : FuncSpec P) (label : Nat) : BlockSpec P :=
  ⟨spec.prog, spec.assign, spec.codeBase, spec.func, label⟩

/-! ## The recovered run a lifted block occupies -/

/-- The recovered instructions of the checked function from `start` onwards, at
most `n` of them. The accepted body is in increasing address order
(`checkCfg_blocks_ordered`), so this is the run of `n` instructions beginning at
`start`.

This, and not `CheckedCfg.body`, is what a lifted Lir block is compared
against: a Lir `branch` emits `test`, `jcc`, `jmp`, and rung 2 necessarily ends
the recovered block at the non-retiring `jcc`, so the trailing `jmp` lies in the
next recovered block. -/
def recoveredRun (c : CheckedCfg) (start n : Nat) : List Decoded :=
  ((c.accepted.body c.spec.func).filter fun d => decide (start ≤ d.addr)).take n

/-! ## Rejections -/

/-- Why a proposed lifting was rejected. Every constructor names the block,
address or instruction at fault; `docs/agents/decompile-lift-blocks.md`
tabulates what each one means and what to do about it. -/
inductive BlockReject where
  /-- The recovered block is not a block of the checked control-flow graph, so
  there is nothing to compare the emission against. -/
  | notARecoveredBlock (block : Decompile.BlockSpec)
  /-- The proposed Lir program is not compiled by the backend at all; these are
  the reasons. -/
  | notCompiled (errors : List Error)
  /-- The proposal names no function at this index. -/
  | noSuchFunction (func : Nat)
  /-- The proposed function has no block with this label. -/
  | noSuchBlock (func label : Nat)
  /-- The recovered block starts at `recovered`, but the layout puts the
  proposed block at `emitted`. -/
  | addressMismatch (recovered emitted : Nat)
  /-- The recovered run from the block's start is shorter than the emission:
  the function has only `recovered` instructions left where `emitted` are
  needed. -/
  | lengthMismatch (recovered emitted : Nat)
  /-- The recovered block is not a prefix of the emission, so the proposed Lir
  block is not the block that starts here. -/
  | notAPrefix (block : Decompile.BlockSpec)
  /-- The instructions differ at this index of the block. -/
  | instrMismatch (index : Nat) (recovered emitted : Decoded)
  /-- The function proposal lists `proposed` recovered blocks for a Lir
  function of `recovered` blocks. -/
  | blockCount (proposed recovered : Nat)
  /-- The block of this label was rejected, for this reason. -/
  | atLabel (label : Nat) (reject : BlockReject)
  deriving DecidableEq, Repr

/-! ## The checker -/

/-- The first index at which two listings differ, as a rejection. Used only
after the lengths have been found equal, which is why running off the end of
either list is reported as agreement. -/
def firstMismatch : Nat → List Decoded → List Decoded → Option BlockReject
  | _, [], _ => none
  | _, _, [] => none
  | k, r :: rs, e :: es =>
    if r = e then firstMismatch (k + 1) rs es else some (.instrMismatch k r e)

/-- Two listings of the same length with no first mismatch are equal. -/
theorem firstMismatch_eq : ∀ {k : Nat} {rs es : List Decoded}, rs.length = es.length →
    firstMismatch k rs es = none → rs = es
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, hl, _ => by simp at hl
  | _, _ :: _, [], hl, _ => by simp at hl
  | k, r :: rs, e :: es, hl, h => by
    rw [firstMismatch] at h
    split at h
    · rename_i he
      rw [he, firstMismatch_eq (k := k + 1) (by simpa using hl) h]
    · cases h

/-- **Accept when re-emitting the proposed Lir block reproduces the recovered
instructions exactly.** The comparison is `DecidableEq` on `List Decoded`, so
the checker is total and decidable and the kernel can run it. -/
def checkBlock {P : Type} (c : CheckedCfg) (blk : Decompile.BlockSpec) (spec : BlockSpec P) :
    Except BlockReject Unit :=
  if blk ∉ c.spec.blocks then .error (.notARecoveredBlock blk)
  else
    match progErrors spec.assign spec.prog with
    | e :: es => .error (.notCompiled (e :: es))
    | [] =>
      match spec.block? with
      | none => .error (.noSuchBlock spec.func spec.label)
      | some _ =>
        if blk.start ≠ spec.addr then .error (.addressMismatch blk.start spec.addr)
        else
          let run := recoveredRun c blk.start spec.emit.length
          if run.length ≠ spec.emit.length then
            .error (.lengthMismatch run.length spec.emit.length)
          else if ¬ (c.body blk).isPrefixOf spec.emit then .error (.notAPrefix blk)
          else
            match firstMismatch 0 run spec.emit with
            | some rej => .error rej
            | none => .ok ()

/-- Check the blocks of a function proposal from label `l` onwards. -/
def checkFrom {P : Type} (c : CheckedCfg) (spec : FuncSpec P) :
    Nat → List Decompile.BlockSpec → Except BlockReject Unit
  | _, [] => .ok ()
  | l, blk :: rest =>
    match checkBlock c blk (spec.blockSpec l) with
    | .error rej => .error (.atLabel l rej)
    | .ok () => checkFrom c spec (l + 1) rest

/-- **Accept when every block of the proposed Lir function re-emits to the
recovered block it was lifted from**, label by label. -/
def checkFunc {P : Type} (c : CheckedCfg) (spec : FuncSpec P) : Except BlockReject Unit :=
  match spec.prog.func? spec.func with
  | none => .error (.noSuchFunction spec.func)
  | some fn =>
    if spec.blocks.length ≠ fn.blocks.length then
      .error (.blockCount spec.blocks.length fn.blocks.length)
    else checkFrom c spec 0 spec.blocks

/-! ## Inverting the checker -/

section Invert

variable {P : Type} {c : CheckedCfg} {blk : Decompile.BlockSpec} {spec : BlockSpec P}

/-- **Everything acceptance establishes**, in one statement, taken apart below.
The checker is written as nested `match`es for exactly this reason: each test
can be inverted one at a time. -/
theorem checkBlock_inv (h : checkBlock c blk spec = .ok ()) :
    blk ∈ c.spec.blocks ∧ progErrors spec.assign spec.prog = [] ∧
      (∃ b, spec.block? = some b) ∧ blk.start = spec.addr ∧
      recoveredRun c blk.start spec.emit.length = spec.emit ∧
      c.body blk <+: spec.emit := by
  rw [checkBlock] at h
  split at h
  · cases h
  · rename_i hmem
    rw [Decidable.not_not] at hmem
    split at h
    · cases h
    · rename_i herr
      split at h
      · cases h
      · rename_i b hb
        split at h
        · cases h
        · rename_i haddr
          rw [ne_eq, Decidable.not_not] at haddr
          simp only at h
          split at h
          · cases h
          · rename_i hlen
            rw [ne_eq, Decidable.not_not] at hlen
            split at h
            · cases h
            · rename_i hpre
              rw [Decidable.not_not] at hpre
              split at h
              · cases h
              · rename_i hmm
                exact ⟨hmem, herr, ⟨b, hb⟩, haddr, firstMismatch_eq hlen hmm,
                  List.isPrefixOf_iff_prefix.mp hpre⟩

/-- An accepted block is a block of the checked control-flow graph. -/
theorem checkBlock_mem (h : checkBlock c blk spec = .ok ()) : blk ∈ c.spec.blocks :=
  (checkBlock_inv h).1

/-- An accepted proposal is compiled by the backend without errors. -/
theorem checkBlock_errors (h : checkBlock c blk spec = .ok ()) :
    progErrors spec.assign spec.prog = [] :=
  (checkBlock_inv h).2.1

/-- An accepted proposal names a block. -/
theorem checkBlock_block (h : checkBlock c blk spec = .ok ()) : ∃ b, spec.block? = some b :=
  (checkBlock_inv h).2.2.1

/-- An accepted block starts where the layout puts the proposed Lir block. -/
theorem checkBlock_addr (h : checkBlock c blk spec = .ok ()) : blk.start = spec.addr :=
  (checkBlock_inv h).2.2.2.1

/-- **The recovered instructions from the block's start are exactly what the
backend emits** for the proposed Lir block. This is the whole content of
acceptance. -/
theorem checkBlock_run (h : checkBlock c blk spec = .ok ()) :
    recoveredRun c blk.start spec.emit.length = spec.emit :=
  (checkBlock_inv h).2.2.2.2.1

/-- **The recovered block is where the lifted block starts.** Its instructions
are a prefix of the emission; anything the emission has beyond them is the
backend's own glue, which rung 2 split into a block of its own because it
follows a non-retiring `jcc`. -/
theorem checkBlock_prefix (h : checkBlock c blk spec = .ok ()) : c.body blk <+: spec.emit :=
  (checkBlock_inv h).2.2.2.2.2

/-- **The recovered bytes are the compiled bytes.** The encodings of the
recovered instructions the lifted block occupies are exactly what
`X86.Backend.encodeAt` writes for the proposed Lir block at its layout
address. -/
theorem checkBlock_bytes (h : checkBlock c blk spec = .ok ()) :
    (recoveredRun c blk.start spec.emit.length).flatMap (fun d => Ext.encode d.instr) =
      encodeAt spec.layout spec.addr spec.code := by
  rw [checkBlock_run h, BlockSpec.emit, emitAt_encode]

end Invert

section InvertFunc

variable {P : Type} {c : CheckedCfg} {spec : FuncSpec P}

/-- Accepting a run of blocks accepts each of them, at its own label. -/
theorem checkFrom_block : ∀ {l : Nat} {bs : List Decompile.BlockSpec},
    checkFrom c spec l bs = .ok () →
    ∀ {i : Nat} (hi : i < bs.length), checkBlock c bs[i] (spec.blockSpec (l + i)) = .ok ()
  | _, [], _, _, hi => absurd hi (by simp)
  | l, blk :: rest, h, i, hi => by
    rw [checkFrom] at h
    split at h
    · cases h
    · rename_i hb
      cases i with
      | zero => simpa using hb
      | succ i =>
        have hrec := checkFrom_block h (i := i) (by simpa using hi)
        have he : l + (i + 1) = l + 1 + i := by omega
        rw [he]
        simpa using hrec

/-- An accepted function proposal names a function. -/
theorem checkFunc_func (h : checkFunc c spec = .ok ()) :
    ∃ fn, spec.prog.func? spec.func = some fn := by
  rw [checkFunc] at h
  split at h
  · cases h
  · exact ⟨_, by assumption⟩

/-- An accepted function proposal lists one recovered block per Lir block. -/
theorem checkFunc_length (h : checkFunc c spec = .ok ()) {fn : Lir.Func P}
    (hf : spec.prog.func? spec.func = some fn) : spec.blocks.length = fn.blocks.length := by
  simp only [checkFunc, hf] at h
  split at h
  · cases h
  · rename_i hc; rwa [ne_eq, Decidable.not_not] at hc

/-- **Every block of an accepted function proposal is an accepted block.** -/
theorem checkFunc_block (h : checkFunc c spec = .ok ()) {l : Nat} (hl : l < spec.blocks.length) :
    checkBlock c spec.blocks[l] (spec.blockSpec l) = .ok () := by
  rw [checkFunc] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simpa using checkFrom_block h hl

/-- **Every recovered block of an accepted function proposal begins the
backend's emission for the Lir block of its label.** -/
theorem checkFunc_prefix (h : checkFunc c spec = .ok ()) {l : Nat} (hl : l < spec.blocks.length) :
    c.body spec.blocks[l] <+: (spec.blockSpec l).emit :=
  checkBlock_prefix (checkFunc_block h hl)

/-- **The recovered instructions from each block's start are the backend's
emission for the Lir block of its label.** -/
theorem checkFunc_run (h : checkFunc c spec = .ok ()) {l : Nat} (hl : l < spec.blocks.length) :
    recoveredRun c spec.blocks[l].start (spec.blockSpec l).emit.length =
      (spec.blockSpec l).emit :=
  checkBlock_run (checkFunc_block h hl)

end InvertFunc

/-! ## Soundness

An accepted lift says the recovered instructions *are* the backend's output for
the proposed Lir block. The backend's own correctness theory then applies to
them, and the statements below are that theory re-exported in terms of the
recovered block. -/

section Sound

-- Several statements below are about the proposal alone and do not use the
-- `DecidableEq P` the `Env` relations need, as in `X86/Lir/Step.lean`.
set_option linter.unusedSectionVars false

variable {P : Type} [DecidableEq P]

/-- The environment of a run of the proposed program: the proposal's assignment
and Lir program, with the memory layout, designated return address, entry stack
pointer and callee-saved values of the run. -/
def BlockSpec.env (spec : BlockSpec P) (S : Space) (exit : Word) (E0 : Nat)
    (saved : Reg → Word) : Env P := ⟨spec.assign, spec.prog, S, exit, E0, saved⟩

variable {spec : BlockSpec P} {S : Space} {exit : Word} {E0 : Nat} {saved : Reg → Word}

/-- The environment of a proposal placed where the proposal says lays the code
out exactly as the proposal does. -/
theorem BlockSpec.env_layout (hcb : S.codeBase = spec.codeBase) :
    (spec.env S exit E0 saved).L = spec.layout := by
  simp [Env.L, BlockSpec.env, BlockSpec.layout, hcb]

/-- The function and block a proposal names, when it names a block. -/
theorem BlockSpec.block?_eq {b : Lir.Block P} (hb : spec.block? = some b) :
    ∃ fn, spec.prog.func? spec.func = some fn ∧ fn.blocks[spec.label]? = some b := by
  simpa [BlockSpec.block?, Lir.Prog.block?, Option.bind_eq_some_iff] using hb

/-- The address of the Lir program point at index `k` of the proposed block:
the block's address plus the length of the code of the earlier Lir
instructions. -/
theorem BlockSpec.env_pointAddr (hcb : S.codeBase = spec.codeBase) {b : Lir.Block P}
    (hb : spec.block? = some b) (k : Nat) :
    (spec.env S exit E0 saved).pa ⟨spec.func, spec.label, k⟩ =
      spec.addr + chunkOff spec.assign spec.func spec.slotCount b k := by
  obtain ⟨fn, hfn, hbl⟩ := BlockSpec.block?_eq hb
  simp only [Env.pa, BlockSpec.env, pointAddr, BlockSpec.addr, BlockSpec.layout,
    Silmaril.X86.Backend.layout, BlockSpec.slotCount, BlockSpec.func?, hfn, hbl, hcb,
    Option.getD_some]

/-! ### Every emitted chunk is non-empty

`checkBlock_isStart` needs to know that the code of each Lir instruction of a
block really does occupy some bytes, so that the address of the next program
point is the address of a *later* instruction rather than the same one. -/

/-- An environment built only to reach the `E.A`-indexed lemmas of
`X86/Lir/Step.lean` for a bare assignment. -/
private def dummyEnv (A : Assign P) : Env P := ⟨A, ⟨[]⟩, ⟨0, 0, 0, 0, 0⟩, 0, 0, fun _ => 0⟩

/-- Every Lir operation selects at least one machine instruction. -/
theorem selOp_ne_nil (A : Assign P) (o : Lir.Op P) :
    Silmaril.X86.Backend.selOp A o ≠ [] :=
  Env.selOp_ne_nil (dummyEnv A) o

/-- **Every chunk of a block's code is non-empty**: each Lir instruction and
the terminator select at least one machine instruction. -/
theorem chunk_ne_nil (A : Assign P) (f ns : Nat) (b : Lir.Block P) {k : Nat}
    (hk : k < (blockChunks A f ns b).length) : (blockChunks A f ns b)[k] ≠ [] := by
  rw [blockChunks_length] at hk
  rcases Nat.lt_or_ge k b.instrs.length with hlt | hge
  · rw [blockChunks_instr A f ns b hlt]
    cases hi : b.instrs[k] with
    | op o => simpa [instrChunk] using selOp_ne_nil A o
    | call g args results => simp [instrChunk]
    | fop => simp [instrChunk]
  · obtain rfl : k = b.instrs.length := by omega
    rw [blockChunks_term]
    cases b.term <;> simp [termChunk, epilogue]

variable {c : CheckedCfg} {blk : Decompile.BlockSpec}

/-- **At the entry of an accepted block the machine is at its first recovered
instruction.** This is what the lift adds to the backend's simulation lemmas:
the machine run they describe starts at the address rung 2 recovered, so it is
a run of the recovered code. -/
theorem checkBlock_rip (hchk : checkBlock c blk spec = .ok ())
    (hcb : S.codeBase = spec.codeBase) {s : Lir.State P} {t : MState} {B : Nat}
    (hm : (spec.env S exit E0 saved).Body s t B)
    (hpt : s.point = ⟨spec.func, spec.label, 0⟩) :
    t.core.rip = BitVec.ofNat 64 blk.start := by
  obtain ⟨b, hb⟩ := checkBlock_block hchk
  rw [hm.rip, hpt, BlockSpec.env_pointAddr hcb hb, ← checkBlock_addr hchk]
  simp [chunkOff]

/-- **Every Lir program point of an accepted block is the address of a
recovered instruction.** The machine run that the simulation lemmas describe
therefore walks the recovered listing, instruction by instruction, and not
merely some code that agrees with it.

This is the lemma the next rung needs and the one it is easiest to assume
without noticing: without it, "the lifted program's steps are the recovered
instructions' steps" is a hope rather than a theorem. -/
theorem checkBlock_isStart (hchk : checkBlock c blk spec = .ok ())
    (hcb : S.codeBase = spec.codeBase) {b : Lir.Block P} (hb : spec.block? = some b)
    {k : Nat} (hk : k ≤ b.instrs.length) :
    IsStart (recoveredRun c blk.start spec.emit.length)
      ((spec.env S exit E0 saved).pa ⟨spec.func, spec.label, k⟩) := by
  have hklt : k < (blockChunks spec.assign spec.func spec.slotCount b).length := by
    rw [blockChunks_length]; omega
  rw [checkBlock_run hchk, BlockSpec.env_pointAddr hcb hb]
  simp only [BlockSpec.emit, BlockSpec.code, hb]
  have hsplit : blockCode spec.assign spec.func spec.slotCount b =
      ((blockChunks spec.assign spec.func spec.slotCount b).take k).flatten ++
        ((blockChunks spec.assign spec.func spec.slotCount b).drop k).flatten := by
    rw [blockCode, ← List.flatten_append, List.take_append_drop]
  have hne : ((blockChunks spec.assign spec.func spec.slotCount b).drop k).flatten ≠ [] := by
    have hc := chunk_ne_nil spec.assign spec.func spec.slotCount b hklt
    rw [List.drop_eq_getElem_cons hklt, List.flatten_cons]
    simp only [ne_eq, List.append_eq_nil_iff, not_and]
    exact fun h => absurd h hc
  rw [hsplit]
  exact isStart_emitAt_append _ _ _ _ (emitAt_isStart _ _ hne)

/-- **An accepted block lift is sound.**

The first conjunct is what the lift contributes, and it is the point of this
rung: the machine is at the recovered block's first instruction, so what the
second conjunct describes is an execution of the *recovered* code and not of
some code that merely agrees with it. `checkBlock_bytes` and
`checkBlock_isStart` carry that through the rest of the block.

The second conjunct is the backend's own theory, re-exported: the recovered
instructions are exactly what the backend emits for the proposed Lir block, so
executing them from a machine state matching a Lir state reaches a state
matching the Lir successor state.

**The statement is per Lir step because the backend's lemmas are.** `sim_op`,
`sim_jump`, `sim_branch`, `sim_trap`, `sim_callSite`, `sim_ret` and `sim_halt`
are each about one Lir transition and `Env.simulation` is their packaging;
there is no "run this block body to its terminator" lemma in `X86/Lir/` to
lift. A whole-block statement waits on a whole-block lemma there, which is the
backend's work and not this rung's. -/
theorem checkBlock_sound (hchk : checkBlock c blk spec = .ok ())
    (hcb : S.codeBase = spec.codeBase) (hok : (spec.env S exit E0 saved).Ok)
    {s : Lir.State P} {t : MState} {B : Nat}
    (hm : (spec.env S exit E0 saved).Body s t B)
    (hpt : s.point = ⟨spec.func, spec.label, 0⟩) :
    t.core.rip = BitVec.ofNat 64 blk.start ∧
      ∀ s', Lir.Step spec.prog s s' →
        ∃ t', TransGen (spec.env S exit E0 saved).TStep t t' ∧
          (spec.env S exit E0 saved).Match s' t' := by
  refine ⟨checkBlock_rip hchk hcb hm hpt, fun s' hstep => ?_⟩
  obtain ⟨t', hmatch, hprog⟩ :=
    (Env.simulation _ hok).toForward.running s t s' (.inl ⟨B, hm⟩) hstep
  rcases hprog with hg | ⟨-, hlt⟩
  · exact ⟨t', hg, hmatch⟩
  · exact absurd hlt (Nat.lt_irrefl 0)

end Sound

/-! ## The lowering rung 3 needed

`Machine.Lift.Abstraction` takes its lowering as a parameter, because
`RTL.toLir` was on a sibling branch when it was written. It is in the tree now,
and this is the instance. -/

/-- The two transports of a behaviour from RTL to Lir — rung 3's and
`RTL.ToLir`'s — are the same function. -/
theorem behaviorToLir_eq (b : RTL.Behavior) : behaviorToLir b = RTL.toLirBehavior b := by
  cases b <;> rfl

/-- **`RTL.toLir` preserves behaviour**, in the form rung 3 asks for.

`Machine/Lift/Abstraction.lean` takes its lowering as a parameter and says that
`RTL.toLir` "together with its preservation theorem is the intended instance;
nothing is instantiated here", because `RTL.toLir` was on a sibling branch when
that file was written. It is in the tree now, so rung 3 is a theorem about the
compiler rather than about a stub. -/
theorem toLir_lowerBehaves : LowerBehaves RTL.toLir := by
  intro p f args mem s b hs hb hns
  obtain ⟨t, ht, hbt⟩ := RTL.toLir_start_behaves hs hb hns
  exact ⟨t, ht, by rwa [behaviorToLir_eq]⟩

/-! ## The composition -/

section Compose

variable {P : Type} [DecidableEq P]

/-- **A lifted function's behaviour, not merely its shape.** From

* an accepted lift of every recovered block of a function (`checkFunc`), so the
  recovered bytes *are* the compilation of the proposed Lir function;
* an accepted abstraction of the proposed Lir program (rung 3,
  `Machine.Lift.checkAbstraction`), so the proposed RTL program and the Lir
  program have the same behaviours;
* a successful compilation of the proposed Lir program at the proposed code
  base, with the layout conditions of `compile_correct`;

the behaviours of the proposed RTL program are the behaviours of the machine
loaded with the compiled image — whose bytes at each recovered block are, by the
first conjunct, exactly the recovered bytes.

This is the statement rungs 1 and 2 could not make: it is about what the
recovered code *does*, not about where it is. -/
theorem checkFunc_behaviour {c : CheckedCfg} {spec : FuncSpec P}
    (hlift : checkFunc c spec = .ok ())
    {lower : Lowering} (hlow : LowerBehaves lower) {abs : AbstractionSpec P}
    (habs : checkAbstraction lower spec.prog abs = .ok ())
    {S : Space} {img : Image} (hc : compile spec.assign spec.prog S.codeBase = .ok img)
    (hvalid : S.Valid img.code.length) (exit : Word) (E0 : Nat) (saved : Reg → Word)
    (hhi : E0 + 8 ≤ S.stackHi) (hlo : S.stackLo ≤ E0) (halign : E0 % 16 = 8)
    (hexit : exit.toNat < S.codeBase ∨ S.codeBase + img.code.length ≤ exit.toNat)
    {lm : Lir.Memory} (hsize : lm.size = S.memSize)
    {f : RTL.FuncId} {args : List Word} {rs : RTL.State Nat}
    (hs : abs.source.start f args lm = some rs)
    (hsafe : ¬ RTL.Behaves abs.source rs .stuck) (init : State) :
    let E : Env P := ⟨spec.assign, spec.prog, S, exit, E0, saved⟩
    (∀ l (hl : l < spec.blocks.length),
      recoveredRun c spec.blocks[l].start (spec.blockSpec l).emit.length =
        (spec.blockSpec l).emit) ∧
    E.code = img.code ∧
    ∃ t₀, spec.prog.start f args lm = some t₀ ∧
      (∀ b : RTL.Behavior, RTL.Behaves abs.source rs b ↔
        Lir.Behaves spec.prog t₀ (behaviorToLir b)) ∧
      (∀ vs m, RTL.Behaves abs.source rs (.returned vs m) →
        ∃ t', ReflTransGen (RStep exit) (E.load lm f args init) t' ∧ E.Returned vs m t') ∧
      (∀ m, RTL.Behaves abs.source rs (.trapped m) →
        ∃ t', ReflTransGen (RStep exit) (E.load lm f args init) t' ∧ E.Trapped m t') := by
  intro E
  obtain ⟨t₀, ht₀, hiff⟩ := Silmaril.Machine.Lift.checkAbstraction_sound hlow habs hs hsafe
  obtain ⟨-, hcode, hret, htrap, -⟩ :=
    Silmaril.X86.Backend.compile_correct spec.assign spec.prog S hc hvalid exit E0 saved hhi hlo
      halign hexit hsize ht₀ init
  exact ⟨fun l hl => checkFunc_run hlift hl, hcode, t₀, ht₀, hiff,
    fun vs m hb => hret vs m ((hiff _).mp hb), fun m hb => htrap m ((hiff _).mp hb)⟩

end Compose

end Silmaril.X86.Decompile.Lift

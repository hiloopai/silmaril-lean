module

public import Silmaril.Machine.CBackend.RTL.ToLirExamples.Defs
public import Silmaril.X86.Decompile.CfgPropose
public import Silmaril.X86.Decompile.Propose.Defs
public import Silmaril.X86.Decompile.Tactic.Defs
public import Silmaril.X86.Decompile.LiftTactic.Defs
public import Silmaril.Machine.CBackend.Lift.Tactic.Defs
public meta import Silmaril.X86.Decompile.LiftTactic.Defs
public meta import Silmaril.Machine.CBackend.Lift.Tactic.Defs
public meta import Silmaril.Machine.CBackend.RTL.ToLirExamples.Defs
public meta import Silmaril.X86.Decompile.CfgPropose
public meta import Silmaril.X86.Decompile.Propose.Defs
/-!
# The round trip: decompiling our own compiler's output

`Silmaril/Machine/RTL/ToLirExamples.lean` carries `RTL.Examples.factorial` down
the ladder — one Lir block per RTL node (`toLir`), spilled onto the nine
allocatable registers, compiled by `X86.Backend.compile` into a 139-byte image
at `0x401000`. This file takes those 139 bytes and carries them back *up* the
decompilation ladder of `Silmaril/X86/Decompile/`, with no information passed
between the two directions except the bytes and the address they sit at.

That is the point of the exercise. `X86.Backend.compile` writes the bytes and
`Decompile.Region.decode?` reads them, and the two were written independently:
the backend emits through `Ext.encode`, the decompiler walks through
`Ext.decode`, and nothing but the byte string connects them. Every number below
is therefore a statement about the pair, not about either one alone.

## The rungs, on this image

1. `factorialRegion` — the image's bytes at the backend's `codeBase`.
   `factorial_code_is_compiled` proves the byte list really is what
   `X86.Backend.compile` returns, so the literal is not an independent claim.
2. `factorial_decodes` — all 139 bytes decode, as 35 instructions, with no
   byte skipped and no instruction spelled differently from the way
   `Ext.encode` spells it (`Region.decode?_covers`).
3. `factorial_check_eq` — the one-function partition is accepted, with all 35
   instructions in the function's body, and `factorial_assumes_nothing` records
   that acceptance assumes nothing at all about the link.
4. `factorial_checkCfg_eq` — the control-flow graph `CfgPropose` recovers,
   10 blocks and 10 edges, is accepted by `checkCfg`.
5. `factorial_lift` — each of the six recovered blocks that is an RTL node
   re-emits, under `X86.Backend.blockCode`, to exactly the instructions that
   were recovered from it (`Decompile.Lift.checkFunc`).
6. `factorial_abstraction` — the lifted Lir function abstracts to the RTL
   factorial, with the real `RTL.toLir` as the lowering
   (`Machine.Lift.checkAbstraction`).

`factorial_round_trip` relates the recovered *graph* to the RTL function it came
from; `factorial_lifted_behaviour` relates the recovered *bytes* to what the RTL
function computes.

## No calls, so no relocations

`RTL.Examples.factorial` calls nothing, and the backend emits a `call` only for
`Lir.Instr.call`. The compiled image therefore contains no `call` instruction:
`factorial_no_calls` checks that, and `factorial_assumes_nothing` is the
consequence — `Partition.relocs` and `Partition.externals` are both empty, and
`Accepted.assumedExternal` is empty, so the accepted decomposition is
unconditional. The call-resolution machinery of rung 1 (`relocTarget`,
`check_relocated_internal_is_entry`) is exercised instead by the ingested
`sha256.o` in `Silmaril/X86/Decompile/Examples.lean`, which has seven relocated
call sites and three external ones. There is nothing to resolve here, and
inventing a relocation to exercise the path would weaken the statement rather
than strengthen it.

## What the round-trip theorem says

`factorial_round_trip` is a **structural** statement, and only that. It says
that the blocks and edges the decompiler recovers from the bytes are the blocks
and edges the compiler laid down:

* the recovered function's extent is exactly the extent `X86.Backend.layout`
  assigns to the Lir function (`factorial_extent_is_layout`);
* every recovered block at or above the address of the Lir entry block, with
  the compiler's glue blocks spliced out, starts at `layout.block 0 n` for the
  RTL node `n` it came from, and these exhaust the six RTL nodes;
* the recovered edges, read at that level, are exactly the successor relation
  of the RTL function — `RTL.Func.succ` — transported through `layout.block`.

## What `factorial_round_trip` does not say, and what now does

`factorial_round_trip` says **nothing about semantics**. It does not say that
the recovered graph, lifted to a program, computes the factorial, nor anything
about registers, stack slots or the values in them. Rungs 1 and 2 are about
*where the code is* and *where control goes*, and a statement of semantic
equivalence is not available from them, because neither rung has a notion of a
program variable at all.

The step that introduces one is now here. `Decompile.Lift.checkBlock`
(`Silmaril/X86/Decompile/Lift.lean`) accepts a proposed Lir block when
re-emitting it with the backend's own instruction selection reproduces the
recovered instructions exactly, and `factorial_lift` is that check passing on
all six blocks of this image. From there the existing rungs compose:
`factorial_abstraction` is rung 3 on the lifted Lir function — with the real
`RTL.toLir`, not a stub — and `factorial_lifted_behaviour` is the composition,
every hypothesis discharged: **every returning or trapping behaviour of the RTL
factorial is a behaviour of the machine executing these 139 bytes**, up to the
stack-limit stop.

So this file now shows two things rather than one. The toolkit accepts our
compiler's output and recovers the structure the compiler laid down
(`factorial_round_trip`); and the recovered code, lifted, computes what the
source program computes (`factorial_lifted_behaviour`).

## What is still missing

Three things, and it is worth being exact about them.

* **The statement is one-directional.** `factorial_lifted_behaviour` carries RTL
  behaviours to machine executions. The converse — that the machine exhibits no
  behaviour the RTL program does not — is what
  `RTL.ImplementsX86.implements_sysv64` is for, and closing the loop as an
  equivalence is a composition this file does not perform.
* **There is no whole-block simulation lemma.** `Lift.checkBlock_sound` is per
  Lir step, because `X86/Lir/Step.lean` is: `sim_op`, `sim_jump`, `sim_branch`
  and the rest are each about one transition. A "run this block body to its
  terminator" statement waits on a lemma in the backend, not in the lift.
* **There is no block proposer.** The six Lir blocks above were written by hand.
  Nothing in `Silmaril/X86/Decompile/` guesses a Lir block from x86 bytes; the
  checker is the judge and the proposer is the agent's job, which is the
  arrangement the whole toolkit is built on.

## Proof versus test

Every theorem in this file is a kernel proof. There is no compiled evaluation and
no `sorry`: at 139 bytes and 35 instructions the whole pipeline — `compile`,
`decode?`, `check`, `CfgPropose.ofFunction`, `checkCfg`, `Lift.checkFunc`,
`checkAbstraction` and the comparison against `X86.Backend.layout` — reduces in
the kernel, by `decide` or by the `split_functions`, `recover_cfg`,
`lift_block` and `abstract_stack` tactics, which are the same thing with
`maxRecDepth` raised.

The two exceptions are marked as such. `Propose.ofStripped` sorts its seed
addresses with `List.mergeSort`, which is defined by well-founded recursion and
does not reduce in the kernel, so what the symbol-table-free proposer guesses
for this image is recorded with `#guard` — compiled evaluation at build time,
which adds no axioms but is a test rather than a proof. Nothing downstream
depends on those two lines.
-/

@[expose] public section

namespace Silmaril.X86.Decompile.RoundTrip

open Silmaril.X86 (Byte)
open Silmaril.X86.Backend (Layout compile encodeAt layout progCode)
open Silmaril.Machine.RTL.X86.Examples (E0 assign9 factMem factorialX space startState)
open Silmaril.Machine.Lift (AbstractionSpec TableAlloc checkAbstraction)
open scoped Silmaril.X86.Decompile.Lift
open scoped Silmaril.Machine.Lift

open Silmaril.Process (Memory)

set_option maxRecDepth 100000

/-! ## The compiled image, as a region -/

/-- The 139 bytes `X86.Backend.compile` emits for the spilled, lowered
`RTL.Examples.factorial`. Written as a literal so that the decompilation below
reduces over a byte list rather than over the whole backend;
`factorial_code_is_compiled` is the proof that the literal is the image. -/
def factorialCode : List Byte := List.map (BitVec.ofNat 8) [
  0x49, 0x89, 0xE3, 0x4D, 0x29, 0xF3, 0x49, 0x81, 0xFB, 0x80, 0x00, 0x00, 0x00, 0x0F, 0x83,
  0x02, 0x00, 0x00, 0x00, 0x0F, 0x0B, 0x55, 0x53, 0x41, 0x54, 0x41, 0x55, 0x48, 0x81, 0xEC,
  0x58, 0x00, 0x00, 0x00, 0x48, 0x89, 0x7C, 0x24, 0x08, 0x48, 0x8B, 0x74, 0x24, 0x08, 0xE9,
  0x00, 0x00, 0x00, 0x00, 0x48, 0xBF, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xE9,
  0x00, 0x00, 0x00, 0x00, 0x49, 0xB8, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xE9,
  0x00, 0x00, 0x00, 0x00, 0x48, 0x85, 0xF6, 0x0F, 0x85, 0x05, 0x00, 0x00, 0x00, 0xE9, 0x1D,
  0x00, 0x00, 0x00, 0x49, 0x89, 0xFB, 0x4C, 0x0F, 0xAF, 0xDE, 0x4C, 0x89, 0xDF, 0xE9, 0x00,
  0x00, 0x00, 0x00, 0x49, 0x89, 0xF3, 0x4D, 0x29, 0xC3, 0x4C, 0x89, 0xDE, 0xE9, 0xD5, 0xFF,
  0xFF, 0xFF, 0x48, 0x89, 0xF8, 0x48, 0x81, 0xC4, 0x58, 0x00, 0x00, 0x00, 0x41, 0x5D, 0x41,
  0x5C, 0x5B, 0x5D, 0xC3]

/-- The layout `X86.Backend.compile` placed the image with: where each Lir
function starts, and where each of its blocks starts. -/
def factorialLayout : Layout := layout assign9 factorialX space.codeBase

/-- **The literal really is the compiled image.** `compile` succeeds on the
spilled factorial at the backend's `codeBase`, and the bytes it returns are
`factorialCode`. Checked by the kernel. -/
theorem factorial_code_is_compiled :
    ∃ img, compile assign9 factorialX space.codeBase = .ok img ∧
      img.code = factorialCode ∧ img.layout = factorialLayout :=
  ⟨_, rfl, by decide, rfl⟩

/-- The image as an addressed region: the compiled bytes at the backend's
`codeBase`, which is `0x401000`. -/
def factorialRegion : Region := { base := space.codeBase, bytes := factorialCode }

/-- The region's base is the address the layout gives the one Lir function.
Checked by the kernel. -/
theorem factorial_base_eq : factorialRegion.base = factorialLayout.func 0 := by decide

/-- A memory holding the image, readable and executable, so that the
hypotheses of `check_sound_step` and `checkCfg_exit` are satisfiable here too.
-/
def factorialMemory : Memory := factorialRegion.load

/-- The memory really does hold the region. -/
theorem factorial_loaded : factorialRegion.LoadedIn factorialMemory :=
  factorialRegion.loadedIn_load (by decide)

/-! ## Rung 0: the image decodes

`Region.decode?` walks the bytes through `Ext.decode`, which re-encodes what it
reads and demands the result be a prefix of the input. A successful walk is
therefore not merely a reading of the bytes but the statement that the bytes
*are* the canonical encodings of the listed instructions
(`Region.decode?_covers`). -/

/-- **All 139 bytes decode, as 35 instructions.** Checked by the kernel. -/
theorem factorial_decodes :
    (factorialRegion.decode? 200).map List.length = some 35 := by split_functions

/-- The image is 139 bytes long. Checked by the kernel. -/
theorem factorial_length : factorialRegion.bytes.length = 139 := by decide

/-- The decoded listing, as a term. -/
def factorialListing : List Decoded := (factorialRegion.decode? 200).getD []

/-- The listing is the one `decode?` produced. Checked by the kernel. -/
theorem factorial_listing_eq : factorialRegion.decode? 200 = some factorialListing := by
  split_functions

/-- **The bytes are exactly the canonical encodings of the 35 listed
instructions**, so no byte was skipped and nothing was spelled differently from
the way the backend's `Ext.encode` spells it. -/
theorem factorial_listing_covers :
    (factorialListing.map fun d => Ext.encode d.instr).flatten = factorialRegion.bytes :=
  Region.decode?_covers factorial_listing_eq

/-- **The image contains no `call`.** `RTL.Examples.factorial` calls nothing,
and the backend emits a `call` only for `Lir.Instr.call`, so there is no call
site for a relocation to describe and nothing for the partition to resolve.
Checked by the kernel. -/
theorem factorial_no_calls :
    factorialListing.all (fun d => match d.instr with | .call _ => false | _ => true) = true := by
  split_functions

/-! ## Rung 1: the function boundary

One RTL function compiles to one Lir function, and `X86.Backend.layout` gives
each Lir function a contiguous extent starting at `funcOff`. With one function
in the program that extent is the whole image. -/

/-- The one function of the image: the whole region, entered at its first
byte. -/
def factorialFunction : FunctionSpec :=
  { name := "factorial", entry := 0x401000, size := 139 }

/-- The one-function partition, with no padding, no relocation and no declared
external. -/
def factorialPartition : Partition :=
  { funcs := [factorialFunction], padding := [], relocs := [], externals := [] }

/-- **The recovered extent is the one the compiler laid down.** The function's
entry is the address `X86.Backend.layout` assigns to Lir function `0`, and its
extent ends where the compiled image ends. Checked by the kernel. -/
theorem factorial_extent_is_layout :
    factorialFunction.entry = factorialLayout.func 0 ∧
      factorialFunction.entry + factorialFunction.size =
        factorialLayout.func 0 + factorialCode.length := by decide

/-- **The partition is accepted**, with all 35 instructions in the one
function's body. Checked by the kernel. -/
theorem factorial_accepted :
    (check factorialRegion factorialPartition 200).map
        (fun acc => acc.bodies.map fun b => (b.1.name, b.2.length)) =
      .ok [("factorial", 35)] := by split_functions

/-- The accepted decomposition as a term, so that the soundness theorems of
rung 1 can be applied to it. -/
def factorialAccepted : Accepted :=
  (check factorialRegion factorialPartition 200).toOption.getD
    { region := factorialRegion, partition := factorialPartition, bodies := [],
      relocatedCalls := [], assumedExternal := [] }

/-- The checker accepts, with that term as the result. Checked by the kernel. -/
theorem factorial_check_eq :
    check factorialRegion factorialPartition 200 = .ok factorialAccepted := by split_functions

/-- **Acceptance assumes nothing about the link.** There is no relocated call
site and no external symbol, so the decomposition is unconditional: the
disjuncts of `check_sound_step` that name a relocated call site are empty here.
Checked by the kernel. -/
theorem factorial_assumes_nothing :
    factorialAccepted.relocatedCalls = [] ∧ factorialAccepted.assumedExternal = [] := by
  split_functions

/-! Without a symbol table the stripped proposer guesses the same single
function, and the checker accepts that too. The proposer is untrusted; the
content of the two lines is that `check` is the judge.

These are the only two `#guard`s in the file: `Propose.ofStripped` sorts its
seeds with `List.mergeSort`, which is defined by well-founded recursion and
does not reduce in the kernel, so the proposal itself cannot be computed by
`decide`. They are tests, not proofs. -/

#guard (Propose.ofStripped factorialRegion 200).funcs.map (fun f => (f.entry, f.size)) ==
  [(0x401000, 139)]
#guard (check factorialRegion (Propose.ofStripped factorialRegion 200) 200).toOption.isSome

/-! ## Rung 2: the control-flow graph -/

/-- The control-flow graph `CfgPropose` recovers for the function. Untrusted
data: `checkCfg` is the judge. -/
def factorialCfg : CfgSpec := CfgPropose.ofFunction factorialAccepted factorialFunction

/-- **The recovered graph: ten blocks and ten edges.** Blocks are
`(start, terminator)` pairs of instruction addresses and edges are pairs of
block start addresses; both are written here as offsets from `0x401000` added
to the base, so that the correspondence with the layout below is readable.
Checked by the kernel. -/
theorem factorial_cfg_shape :
    (factorialCfg.blocks.map fun b => (b.start - 0x401000, b.terminator - 0x401000),
      factorialCfg.edges.map fun e => (e.1 - 0x401000, e.2 - 0x401000)) =
      ([(0, 13), (19, 19), (21, 44), (49, 59), (64, 74), (79, 82), (88, 88), (93, 103),
        (108, 117), (122, 138)],
       [(0, 21), (0, 19), (21, 49), (49, 64), (64, 79), (79, 93), (79, 88), (88, 122),
        (93, 108), (108, 79)]) := by recover_cfg

/-- The checked graph as a term, so that the soundness theorems of rung 2 can
be applied to it. -/
def factorialCheckedCfg : CheckedCfg :=
  (checkCfg factorialAccepted factorialCfg).toOption.getD
    { accepted := factorialAccepted, spec := factorialCfg, bodies := [] }

/-- **The proposal is accepted.** Checked by the kernel. -/
theorem factorial_checkCfg_eq :
    checkCfg factorialAccepted factorialCfg = .ok factorialCheckedCfg := by recover_cfg

/-- The 35 instructions are split 4, 1, 8, 2, 2, 2, 1, 4, 4, 7 over the ten
blocks, and the parts sum to the whole. Checked by the kernel. -/
theorem factorial_cfg_bodies :
    (factorialCheckedCfg.bodies.map fun entry => (entry.1.start - 0x401000, entry.2.length),
      (factorialCheckedCfg.bodies.map fun entry => entry.2.length).sum) =
      ([(0, 4), (19, 1), (21, 8), (49, 2), (64, 2), (79, 2), (88, 1), (93, 4), (108, 4),
        (122, 7)], 35) := by recover_cfg

/-! ## Reading the recovered graph at the level of the compiler's blocks

Ten recovered blocks against six RTL nodes. The four extra blocks are not noise
and are not an artefact of the recovery: each one is code the backend emits
that corresponds to no RTL node at all.

* Offsets 0, 19 and 21 are the **prologue**. `X86.Backend.prologue` emits a
  stack-limit check (`cmp`/`jae`), the `ud2` the check jumps over, the
  callee-saved pushes and the frame adjustment, the staging of the incoming
  argument registers, and finally a `jmp` to the entry block. All of it lies
  below the address the layout gives the entry block, and none of it is in the
  image of `layout.block`.
* Offset 88 is **glue**. `X86.Backend.termChunk` compiles a Lir `branch` to
  `test`, `jcc` to one label and `jmp` to the other. Since `jcc` does not
  retire, the `jmp` begins a block of its own: a block whose only instruction
  is an unconditional jump, standing for the untaken arm of the branch.

`lirLevelBlocks` and `lirLevelEdges` read the recovered graph with both kinds
of block removed — the prologue by address, the glue by splicing every edge
into a glue block through to that block's own successor. Both are plain
computable functions of the recovered graph, with no reference to the compiler,
so the theorem below compares two independently produced objects. -/

/-- A recovered block is **glue** when its body is the single unconditional
jump the backend emits for the untaken arm of a `branch`: one instruction, and
that instruction a `jmp`. -/
def IsGlue (c : CheckedCfg) (b : BlockSpec) : Bool :=
  b.start == b.terminator &&
    (match (at? (c.accepted.body c.spec.func) b.start).map Decoded.instr with
     | some (.jmp _) => true
     | _ => false)

/-- The unique outgoing edge target of the block starting at `addr`, when it
has exactly one. -/
def soleTarget (c : CheckedCfg) (addr : Nat) : Option Nat :=
  match c.spec.edges.filter fun e => e.1 == addr with
  | [e] => some e.2
  | _ => none

/-- Follow a block start through a glue block to the block it jumps to; any
other address is left alone. -/
def forward (c : CheckedCfg) (addr : Nat) : Nat :=
  match c.spec.blocks.find? fun b => b.start == addr with
  | some b => if IsGlue c b then (soleTarget c addr).getD addr else addr
  | none => addr

/-- The block starting at `addr` is glue. -/
def IsGlueStart (c : CheckedCfg) (addr : Nat) : Bool :=
  c.spec.blocks.any fun b => b.start == addr && IsGlue c b

/-- The recovered blocks read at the level of the compiler's Lir blocks: the
start addresses of the blocks at or above `entry` that are not glue, in
increasing address order. -/
def lirLevelBlocks (c : CheckedCfg) (entry : Nat) : List Nat :=
  (c.spec.blocks.filter fun b => decide (entry ≤ b.start) && !IsGlue c b).map BlockSpec.start

/-- The recovered edges read at the level of the compiler's Lir blocks: drop
every edge whose source is below `entry` or is a glue block, and redirect every
remaining edge that lands on a glue block to that block's own successor. -/
def lirLevelEdges (c : CheckedCfg) (entry : Nat) : List (Nat × Nat) :=
  (c.spec.edges.filter fun e => decide (entry ≤ e.1) && !IsGlueStart c e.1).map
    fun e => (e.1, forward c e.2)

/-! ## The RTL side

The successor relation of an RTL function, read straight off `RTL.Func.succ`,
which is the relation `toLir` turns into Lir terminators. -/

/-- The edges of an RTL function: every node paired with each of its
successors, in node order. -/
def rtlEdges {R : Type} (p : Silmaril.Machine.RTL.Prog R) (f : Silmaril.Machine.RTL.FuncId) :
    List (Nat × Nat) :=
  match p.func? f with
  | none => []
  | some fn =>
    (List.range fn.code.length).flatMap fun n =>
      (Silmaril.Machine.RTL.Func.succ fn n).map fun m => (n, m)

/-- The address `X86.Backend.layout` assigns to the Lir block of RTL node `n`.
`toLir` makes node `n` into the block labelled `n`, and `Lir.Alloc.spill` maps
blocks one for one, so this is the address of the code of node `n`. -/
def nodeAddr (n : Nat) : Nat := factorialLayout.block 0 n

/-- The RTL factorial has six nodes. Checked by the kernel. -/
theorem factorial_node_count :
    (Silmaril.Machine.RTL.Examples.factorial.func? 0).map (fun fn => fn.code.length) = some 6 := by
  decide

/-- The lowered and spilled program has one function of six blocks, one per RTL
node. Checked by the kernel. -/
theorem factorial_block_count :
    (factorialX.func? 0).map (fun fn => fn.blocks.length) = some 6 := by decide

/-- The six RTL edges: node 0 to 1, 1 to 2, the loop test at 2 to the body at 3
and the return at 5, the body at 3 to 4, and 4 back to the test at 2. Checked
by the kernel. -/
theorem factorial_rtl_edges :
    rtlEdges Silmaril.Machine.RTL.Examples.factorial 0 =
      [(0, 1), (1, 2), (2, 3), (2, 5), (3, 4), (4, 2)] := by decide

/-- Where the layout put each of the six nodes: offsets 49, 64, 79, 93, 108 and
122 from the code base. Checked by the kernel. -/
theorem factorial_node_addrs :
    (List.range 6).map nodeAddr =
      [0x401031, 0x401040, 0x40104F, 0x40105D, 0x40106C, 0x40107A] := by decide

/-- The address of node `0`, the entry block, which is where the prologue ends.
Checked by the kernel. -/
theorem factorial_node0 : nodeAddr 0 = 0x401031 := by decide

/-- The address of node `1`. Checked by the kernel. -/
theorem factorial_node1 : nodeAddr 1 = 0x401040 := by decide

/-- The address of node `2`, the loop test. Checked by the kernel. -/
theorem factorial_node2 : nodeAddr 2 = 0x40104F := by decide

/-- The address of node `3`, the multiply. Checked by the kernel. -/
theorem factorial_node3 : nodeAddr 3 = 0x40105D := by decide

/-- The address of node `4`, the decrement. Checked by the kernel. -/
theorem factorial_node4 : nodeAddr 4 = 0x40106C := by decide

/-- The address of node `5`, the return. Checked by the kernel. -/
theorem factorial_node5 : nodeAddr 5 = 0x40107A := by decide

/-! ## The round-trip theorem -/

/-- **The round trip.** The control-flow graph recovered from the compiled
bytes, read at the level of the compiler's Lir blocks, *is* the control-flow
graph of the RTL function, transported through `X86.Backend.layout`:

* the recovered blocks at or above the entry block, with the backend's glue
  blocks spliced out, start at exactly the addresses `layout.block 0 n` for the
  six RTL nodes `n`, in node order;
* the recovered edges, read at the same level, are exactly the successor
  relation `RTL.Func.succ` of the RTL function, with both ends transported
  through `layout.block 0`.

Nothing on the left-hand side mentions the compiler and nothing on the right
mentions the bytes: the only thing the two sides share is the 139-byte image
and the address it sits at. Checked by the kernel.

**This is a structural statement.** It says the decompiler recovers the shape
the compiler laid down. It does *not* say that a program lifted from the
recovered graph computes what the RTL program computes — see the module
docstring for what would be needed, and which rung supplies it. -/
theorem factorial_round_trip :
    lirLevelBlocks factorialCheckedCfg (nodeAddr 0) = (List.range 6).map nodeAddr ∧
      lirLevelEdges factorialCheckedCfg (nodeAddr 0) =
        (rtlEdges Silmaril.Machine.RTL.Examples.factorial 0).map
          fun e => (nodeAddr e.1, nodeAddr e.2) := by
  rw [factorial_node_addrs, factorial_rtl_edges, factorial_node0]
  simp only [List.map_cons, List.map_nil, factorial_node0, factorial_node1, factorial_node2,
    factorial_node3, factorial_node4, factorial_node5]
  recover_cfg

/-- The ten recovered blocks less the six that are RTL nodes: the three
prologue blocks and the one glue block, named by their offsets from the code
base. The round-trip theorem says what the six are; this says what the other
four are, so that the accounting is complete. Checked by the kernel. -/
theorem factorial_non_node_blocks :
    (factorialCfg.blocks.filter fun b =>
        decide (b.start < nodeAddr 0) || IsGlue factorialCheckedCfg b).map
      (fun b => b.start - 0x401000) = [0, 19, 21, 88] := by
  rw [factorial_node0]
  recover_cfg

/-! ## Rung 2½: lifting the recovered blocks to Lir blocks

The round-trip theorem above is structural. This section is what makes the
image's bytes a *program*: for each of the six recovered blocks that is an RTL
node, the Lir block it came from is proposed, and `Lift.checkBlock` re-emits
that block with the backend's own instruction selection and compares the result
with the recovered instructions.

Nothing about the proposal is trusted. `Lift.checkFunc` recomputes
`progErrors`, `layout` and `blockCode` from the proposal alone; the only thing
the two sides share is, as everywhere in this file, the 139-byte image and the
address it sits at. -/

/-- The proposed lifting of the recovered function: the compiled Lir program,
the register assignment, and the recovered block each Lir block was lifted
from, in label order. The six blocks are the six RTL nodes of
`factorial_node_addrs`; the prologue and the glue block are not Lir blocks and
appear nowhere here. -/
def factorialLift : Lift.FuncSpec (Fin 9) where
  prog := factorialX
  assign := assign9
  codeBase := space.codeBase
  func := 0
  blocks :=
    [⟨0x401031, 0x40103B⟩, ⟨0x401040, 0x40104A⟩, ⟨0x40104F, 0x401052⟩,
     ⟨0x40105D, 0x401067⟩, ⟨0x40106C, 0x401075⟩, ⟨0x40107A, 0x40108A⟩]

/-- **Every recovered block re-emits to itself.** Running the backend's
instruction selection on each proposed Lir block, at the address the layout
gives it, reproduces the recovered instructions exactly. Checked by the
kernel. -/
theorem factorial_lift : Lift.checkFunc factorialCheckedCfg factorialLift = .ok () := by
  lift_block

/-- **One Lir block is not one recovered block.** The loop test is Lir block
`2`; the backend compiles its `branch` to `test`, `jcc`, `jmp`, but `jcc` does
not retire, so rung 2 had to end the recovered block at it and the trailing
`jmp` became the glue block at offset 88. The emission is therefore three
instructions where the recovered block has two, and the recovered block is a
*prefix* of the emission — which is what `Lift.checkBlock_prefix` states and
why the checker compares against `Lift.recoveredRun` rather than against
`CheckedCfg.body`. Checked by the kernel. -/
theorem factorial_branch_block_spans_glue :
    (factorialLift.blockSpec 2).emit.length = 3 ∧
      (factorialCheckedCfg.body ⟨0x40104F, 0x401052⟩).length = 2 := by
  lift_block

/-- The six lifted blocks emit 2, 2, 3, 4, 4 and 7 instructions: 22 in all,
against the 35 of the image. The other 13 are the prologue, which is not a Lir
block — `factorial_non_node_blocks` already accounted for it. Checked by the
kernel. -/
theorem factorial_lift_sizes :
    ((List.range 6).map fun l => (factorialLift.blockSpec l).emit.length) = [2, 2, 3, 4, 4, 7] := by
  lift_block

/-! ## Rung 3 on the lifted program, with the real lowering

`Machine/Lift/Abstraction.lean` takes its lowering as a parameter and its
examples use a stub, because `RTL.toLir` was on a sibling branch when they were
written. It is in the tree now, so the abstraction below is checked against the
*actual* compiler: `Lift.toLir_lowerBehaves` is the `LowerBehaves` instance. -/

/-- The allocation `Lir.Alloc.firstK 7` as a table: seven pseudo-registers in
the seven non-scratch allocatable registers, with `0` and `1` scratch. -/
def factorialAlloc : TableAlloc (Fin 9) := ⟨[.reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
  .reg 8], 0, 1⟩

/-- The proposed abstraction of the lifted Lir function: the RTL factorial, and
the allocation that puts its pseudo-registers back on the machine. -/
def factorialAbstraction : AbstractionSpec (Fin 9) :=
  ⟨Silmaril.Machine.RTL.Examples.factorial, factorialAlloc⟩

/-- **The lifted Lir program abstracts to the RTL factorial.** Lowering
`RTL.Examples.factorial` with the real `RTL.toLir` and spilling it with the
proposed allocation reproduces `factorialX` exactly. Checked by the kernel. -/
theorem factorial_abstraction :
    checkAbstraction Silmaril.Machine.RTL.toLir factorialX factorialAbstraction = .ok () := by
  abstract_stack

/-! ## The composition: a statement about behaviour

`Lift.checkFunc_behaviour` composes the lift with rung 3 and with the backend's
`compile_correct`. Every hypothesis is discharged here, so the theorem below is
about this image and not about a hypothetical one. -/

/-- The compiled image as a term, so that `compile_correct`'s hypotheses can be
stated about it. -/
def factorialImage : Silmaril.X86.Backend.Image :=
  ⟨encodeAt factorialLayout space.codeBase (progCode assign9 factorialX), factorialLayout⟩

/-- The image is what `compile` returns. Checked by the kernel. -/
theorem factorial_compile_eq :
    compile assign9 factorialX space.codeBase = .ok factorialImage := rfl

/-- The layout conditions hold for the image's 139 bytes. -/
theorem factorial_space_valid : space.Valid factorialImage.code.length := by
  show space.Valid (encodeAt (layout assign9 factorialX space.codeBase) space.codeBase
    (progCode assign9 factorialX)).length
  rw [Silmaril.Machine.RTL.X86.Examples.factorialX_code_length]
  exact Silmaril.Machine.RTL.X86.Examples.space_valid

/-- **The RTL run of `factorial(n)` does not get stuck**, so the abstraction's
behavioural `iff` has something to say. The RTL program returns `n!`, and
`Behaves.unique` rules out any other behaviour. -/
theorem factorial_safe (n : Silmaril.X86.Word) :
    ¬ Silmaril.Machine.RTL.Behaves Silmaril.Machine.RTL.Examples.factorial (startState n)
      .stuck := by
  intro hstuck
  obtain ⟨s, hs, hb⟩ := Silmaril.Machine.RTL.Examples.factorial_returns n factMem
  rw [Silmaril.Machine.RTL.X86.Examples.start_eq n] at hs
  cases hs
  exact absurd (Silmaril.Machine.RTL.Behaves.unique hstuck hb) (by intro e; cases e)

/-- **The payoff: the recovered bytes compute the factorial.**

Every hypothesis of `Lift.checkFunc_behaviour` is discharged for this image, so
what comes out is a statement about *this* 139-byte region:

* each recovered block is exactly the backend's emission for the Lir block it
  was lifted to — the first conjunct, which is `factorial_lift` unpacked;
* the loaded machine's code is the image;
* and every returning or trapping behaviour of the **RTL** program
  `RTL.Examples.factorial` is a behaviour of the machine executing those bytes,
  up to the stack-limit stop that is the one difference between the finite
  machine stack and RTL's unbounded one.

Contrast `factorial_round_trip`, which says only that the recovered *shape* is
the compiled shape. This says what the bytes do. -/
theorem factorial_lifted_behaviour (n : Silmaril.X86.Word) (init : Silmaril.X86.State)
    (saved : Silmaril.X86.Reg → Silmaril.X86.Word) :
    let E : Silmaril.X86.Backend.Env (Fin 9) := ⟨assign9, factorialX, space, 0, E0, saved⟩
    (∀ l (hl : l < factorialLift.blocks.length),
      Lift.recoveredRun factorialCheckedCfg factorialLift.blocks[l].start
          (factorialLift.blockSpec l).emit.length = (factorialLift.blockSpec l).emit) ∧
    E.code = factorialImage.code ∧
    ∃ t₀, factorialX.start 0 [n] factMem = some t₀ ∧
      (∀ b : Silmaril.Machine.RTL.Behavior,
        Silmaril.Machine.RTL.Behaves Silmaril.Machine.RTL.Examples.factorial (startState n) b ↔
          Silmaril.Machine.Lir.Behaves factorialX t₀
            (Silmaril.Machine.Lift.behaviorToLir b)) ∧
      (∀ vs m, Silmaril.Machine.RTL.Behaves Silmaril.Machine.RTL.Examples.factorial
          (startState n) (.returned vs m) →
        ∃ t', Relation.ReflTransGen (Silmaril.X86.Backend.RStep 0) (E.load factMem 0 [n] init) t' ∧
          E.Returned vs m t') ∧
      (∀ m, Silmaril.Machine.RTL.Behaves Silmaril.Machine.RTL.Examples.factorial
          (startState n) (.trapped m) →
        ∃ t', Relation.ReflTransGen (Silmaril.X86.Backend.RStep 0) (E.load factMem 0 [n] init) t' ∧
          E.Trapped m t') :=
  Lift.checkFunc_behaviour factorial_lift Lift.toLir_lowerBehaves factorial_abstraction
    factorial_compile_eq factorial_space_valid 0 E0 saved (by decide) (by decide) (by decide)
    (.inl (by decide)) Silmaril.Machine.RTL.X86.Examples.factMem_size
    (Silmaril.Machine.RTL.X86.Examples.start_eq n) (factorial_safe n) init

/-- The glue block is the one at offset 88, and it forwards to the return
block, which is RTL node `5`. This is the splice the round-trip theorem
performs, written out. Checked by the kernel. -/
theorem factorial_glue :
    (factorialCfg.blocks.filter (IsGlue factorialCheckedCfg)).map BlockSpec.start =
        [0x401058] ∧
      forward factorialCheckedCfg 0x401058 = nodeAddr 5 := by
  rw [factorial_node5]
  recover_cfg

end Silmaril.X86.Decompile.RoundTrip

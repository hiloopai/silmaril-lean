module

public import Silmaril.X86.Decompile.CfgPropose
public import Silmaril.X86.Decompile.Propose.Defs
public import Silmaril.X86.Decompile.Tactic.Defs
public import Silmaril.Machine.CSupport.Crypto.X86.Objects.Sha256ClangO0.Defs
public meta import Silmaril.X86.Decompile.CfgPropose
public meta import Silmaril.X86.Decompile.Propose.Defs
public meta import Silmaril.Machine.CSupport.Crypto.X86.Objects.Sha256ClangO0.Defs
/-!
# Worked examples

Who checks what, in the style of `Crypto.X86.Objects.Sha256ClangO0Facts`.

## Checked by the Lean kernel (`decide`/`rfl`, via `split_functions`)

`MD5_memset`, the 64-byte, 20-instruction `clang -O0` fixture from
`tests/x86/md5_memset_clang_O0.hex`: that the one-function partition is
accepted, and that a partition claiming 60 bytes instead of 64 is rejected with
exactly `Reject.uncovered 60 64`. These are proofs.

Also a proof: that `check_sound_step` is not vacuous. It assumes
`Region.LoadedIn`, and a hypothesis nobody exhibits might be unsatisfiable, in
which case the theorem would say nothing at all — a failure mode `sil gate`
does not catch, because the hypothesis is not literally `False`.
`md5_memset_sound_step_instance` discharges every hypothesis at once on a
concrete state, and `md5_memset_hypotheses_inhabited` states the same thing as
the inhabitation of the hypothesis set. `Region.loadedIn_load` settles the
general question: every region ending below the address limit is held by some
memory.

Also proofs, for the control-flow rung: the four-block graph `CfgPropose`
recovers for `MD5_memset`, three rejections of deliberately broken proposals,
and `md5_memset_cfg_exit_instance`, which discharges every hypothesis of
`checkCfg_exit` on the same `jmp` at offset 57 — the block terminator that
closes the loop.

## Checked by compiled evaluation (`#guard`)

What `Propose.ofStripped` guesses for `MD5_memset` without a symbol table, and

The whole 3253-byte `.text` of the ingested `clang -O0` `sha256.o` — 794
instructions in eight functions and six runs of alignment padding — proposed
from its symbol table by `Propose.ofSymbols` and then checked, together with
the three external calls acceptance records as assumptions. Kernel reduction of
`Ext.decode` over three thousand bytes is too slow, so this runs at build time
as compiled code. It adds no axioms, and it is a test, not a proof.
-/

@[expose] public section

namespace Silmaril.X86.Decompile.Examples

open Silmaril.X86.Decompile
open Silmaril.X86 (Byte Word State MState)
open Silmaril.Process (Memory)

set_option maxRecDepth 100000

/-! ## `MD5_memset`, checked by the kernel -/

/-- The 64 bytes of `MD5_memset` from the `clang -O0` `md5.o` of `xcompile` (`.text+0x1200`,
size `0x40`), the fixture `tests/x86/md5_memset_clang_O0.hex` records. -/
def md5MemsetBytes : List Byte := List.map (BitVec.ofNat 8) [
  0x55, 0x48, 0x89, 0xE5, 0x48, 0x89, 0x7D, 0xF8, 0x89, 0x75, 0xF4, 0x89, 0x55, 0xF0, 0xC7,
  0x45, 0xEC, 0x00, 0x00, 0x00, 0x00, 0x8B, 0x45, 0xEC, 0x3B, 0x45, 0xF0, 0x0F, 0x83, 0x1D,
  0x00, 0x00, 0x00, 0x8B, 0x45, 0xF4, 0x88, 0xC2, 0x48, 0x8B, 0x45, 0xF8, 0x8B, 0x4D, 0xEC,
  0x88, 0x14, 0x08, 0x8B, 0x45, 0xEC, 0x83, 0xC0, 0x01, 0x89, 0x45, 0xEC, 0xE9, 0xD7, 0xFF,
  0xFF, 0xFF, 0x5D, 0xC3]

/-- The function as a region, addressed from zero. -/
def md5MemsetRegion : Region := { base := 0, bytes := md5MemsetBytes }

/-- The obvious proposal: one function covering the whole region. -/
def md5MemsetPartition : Partition :=
  { funcs := [{ name := "MD5_memset", entry := 0, size := 64 }],
    padding := [], relocs := [], externals := [] }

/-- The region decodes to twenty instructions. -/
theorem md5_memset_decodes :
    (md5MemsetRegion.decode? 128).map List.length = some 20 := by split_functions

/-- **The proposal is accepted**, with all twenty instructions in the one
function's body. Checked by the kernel. -/
theorem md5_memset_accepted :
    (check md5MemsetRegion md5MemsetPartition 128).map
        (fun acc => acc.bodies.map fun b => (b.1.name, b.2.length)) =
      .ok [("MD5_memset", 20)] := by split_functions

/-- The accepted decomposition assumes nothing about the link: `MD5_memset`
calls nothing. -/
theorem md5_memset_no_assumptions :
    (check md5MemsetRegion md5MemsetPartition 128).map Accepted.assumedExternal = .ok [] := by
  split_functions

/-- A proposal claiming 60 bytes instead of 64. -/
def md5MemsetShort : Partition :=
  { md5MemsetPartition with funcs := [{ name := "MD5_memset", entry := 0, size := 60 }] }

/-- **The wrong size is rejected**, with the uncovered range named. Checked by
the kernel. -/
theorem md5_memset_short_rejected :
    check md5MemsetRegion md5MemsetShort 128 = .error (.uncovered 60 64) := by split_functions

/-! ## A memory holding the function, and a non-vacuous instance

`check_sound_step` assumes `Region.LoadedIn`, and a hypothesis nobody exhibits
is a hypothesis that might be unsatisfiable, in which case the theorem would say
nothing. `Region.loadedIn_load` settles that in general; what follows pins it
down here and then discharges *every* hypothesis of `check_sound_step` at once,
on a concrete state, so that a reader can see the theorem has content.

The state chosen is the one at offset 57, the unconditional `jmp` back to the
loop head at 21. It is the cheapest honest choice: `jmp` reads no memory and no
flag, so the machine really does retire from it with nothing mapped but the
code itself, and the successor is a decoded instruction of the same function —
the first disjunct of `check_sound_step`. -/

/-- A memory holding `MD5_memset` at address 0, readable and executable. -/
def md5MemsetMemory : Memory := md5MemsetRegion.load

/-- The memory really does hold the region, so `check_sound_step`'s `hload` is
satisfiable. -/
theorem md5_memset_loaded : md5MemsetRegion.LoadedIn md5MemsetMemory :=
  md5MemsetRegion.loadedIn_load (by decide)

/-- The one function of the proposal. -/
def md5MemsetFunction : FunctionSpec := { name := "MD5_memset", entry := 0, size := 64 }

/-- The accepted decomposition as a term, so that `check_sound_step` can be
applied to it. Writing the twenty decoded instructions out as a literal would
say no more. -/
def md5MemsetAccepted : Accepted :=
  (check md5MemsetRegion md5MemsetPartition 128).toOption.getD
    { region := md5MemsetRegion, partition := md5MemsetPartition, bodies := [],
      relocatedCalls := [], assumedExternal := [] }

/-- The checker accepts, with that term as the result. Checked by the kernel. -/
theorem md5_memset_check_eq :
    check md5MemsetRegion md5MemsetPartition 128 = .ok md5MemsetAccepted := by
  split_functions

/-- Offset 57 is a decoded instruction of the function. Checked by the kernel. -/
theorem md5_memset_at_57 : md5MemsetAccepted.AtInstruction md5MemsetFunction 57 := by
  split_functions

/-- The unconditional jump at offset 57 fetches from the loaded memory. -/
theorem md5_memset_fetch_jmp :
    Ext.fetch md5MemsetMemory 57 = .decoded (.jmp 0xFFFFFFD7#32) 5 := by
  refine Ext.fetch_eq_decoded_iff.mpr ⟨(md5MemsetBytes.drop 57).take 5, ?_, by decide⟩
  simpa [md5MemsetRegion] using md5_memset_loaded 57 5 (by decide)

/-- The successor RIP of the jump at offset 57, in the form `Ext.exec`
produces it. -/
def md5MemsetJumpRip (core : State) : Word :=
  core.rip + BitVec.ofNat 64 (Ext.Instr.jmp 0xFFFFFFD7#32).length +
    (0xFFFFFFD7#32 : BitVec 32).signExtend 64

/-- From that jump, in that memory, the machine really retires, and lands on
the loop head at offset 21. -/
theorem md5_memset_step (exit : Word) (core : State) (hrip : core.rip = 57#64) :
    ∃ next, Ext.stepOpt exit ⟨core, md5MemsetMemory⟩ = some next ∧
      next.core.rip.toNat = 21 := by
  have hstep : Ext.step exit (⟨core, md5MemsetMemory⟩ : MState) =
      .retired ⟨{ core with rip := md5MemsetJumpRip core }, md5MemsetMemory⟩ := by
    simp only [Ext.step, hrip]
    rw [show (57#64 : Word).toNat = 57 from rfl, md5_memset_fetch_jmp]
    dsimp only
    rw [exec_jmp]
    simp [md5MemsetJumpRip, hrip]
  refine ⟨_, Ext.stepOpt_eq_some_iff.mpr hstep, ?_⟩
  simp only [md5MemsetJumpRip, hrip]
  decide

/-- **`check_sound_step` is not vacuous.** Every hypothesis is discharged: the
acceptance of `md5_memset_check_eq`, the memory of `md5_memset_loaded`, and a
concrete state at offset 57 from which the machine really does retire. The
conclusion holds with its first disjunct — control stays inside the function. -/
theorem md5_memset_sound_step_instance (exit : Word) (core : State)
    (hrip : core.rip = 57#64) :
    ∃ next, Ext.stepOpt exit ⟨core, md5MemsetMemory⟩ = some next ∧
      (md5MemsetAccepted.AtInstruction md5MemsetFunction next.core.rip.toNat ∨
        (∃ g ∈ md5MemsetPartition.funcs, next.core.rip.toNat = g.entry) ∨
        md5MemsetAccepted.IsRet md5MemsetFunction core.rip.toNat ∨
        md5MemsetAccepted.IsRelocatedCall core.rip.toNat) := by
  obtain ⟨next, hstep, -⟩ := md5_memset_step exit core hrip
  refine ⟨next, hstep, check_sound_step md5_memset_check_eq (f := md5MemsetFunction) (by decide)
    md5_memset_loaded (m := ⟨core, md5MemsetMemory⟩) ?_ hstep⟩
  show md5MemsetAccepted.AtInstruction md5MemsetFunction core.rip.toNat
  rw [hrip]
  exact md5_memset_at_57

/-- A concrete machine state at offset 57: every register zero, every flag
unknown, in the memory that holds the function. -/
def md5MemsetState : MState :=
  ⟨⟨fun _ => 0, 57, ⟨none, none, none, none, none, none⟩, 0⟩, md5MemsetMemory⟩

/-- The same fact stated as the inhabitation of `check_sound_step`'s hypothesis
set, which is the form the vacuity question is asked in. -/
theorem md5_memset_hypotheses_inhabited :
    ∃ (acc : Accepted) (f : FunctionSpec) (exit : Word) (m next : MState),
      check md5MemsetRegion md5MemsetPartition 128 = .ok acc ∧
        f ∈ md5MemsetPartition.funcs ∧ md5MemsetRegion.LoadedIn m.memory ∧
        acc.AtInstruction f m.core.rip.toNat ∧ Ext.stepOpt exit m = some next := by
  obtain ⟨next, hstep, -⟩ := md5_memset_step 0 md5MemsetState.core rfl
  exact ⟨md5MemsetAccepted, md5MemsetFunction, 0, md5MemsetState, next, md5_memset_check_eq,
    by decide, md5_memset_loaded, md5_memset_at_57, hstep⟩

/-! ## The same function with no symbol table

`Propose.ofStripped` is untrusted, like the rest of `Propose`. The point of
these two lines is not that the heuristic is right — it is that `check` is the
judge of whether it is. -/

-- With no symbol table, the heuristic seeds one function at the region base
-- and runs it to the end, and the checker accepts that.
#guard (Propose.ofStripped md5MemsetRegion 128).funcs.map (fun f => (f.name, f.entry, f.size)) ==
  [("fn_0", 0, 64)]
#guard (check md5MemsetRegion (Propose.ofStripped md5MemsetRegion 128) 128).toOption.isSome

/-! ## The ingested `sha256.o`, checked by evaluation -/

/-- The whole `.text` of the ingested object, as a region addressed from zero
(section offsets). -/
def sha256TextRegion : Region :=
  { base := 0,
    bytes := ((Silmaril.Crypto.X86.Objects.Sha256ClangO0.object.sections[1]?).map
      fun part => part.data.toList).getD [] }

/-- The partition `Propose.ofSymbols` builds from the object's symbol table. -/
def sha256TextPartition : Partition :=
  (Propose.ofSymbols Silmaril.Crypto.X86.Objects.Sha256ClangO0.object ".text").getD
    { funcs := [], padding := [], relocs := [], externals := [] }

-- The section is the expected size, and the model consumes all of it.
#guard sha256TextRegion.bytes.length == 3253
#guard (sha256TextRegion.decode? 5000).map List.length == some 794

-- Eight defined functions, as the symbol table names them, and the six runs of
-- inter-function alignment padding between them: 44 bytes in all.
#guard sha256TextPartition.funcs.map (fun f => (f.name, f.entry, f.size)) ==
  [("xc_sha256", 0, 43), ("sha256_compress", 48, 1214), ("sha_256_init", 1264, 153),
   ("sha_256_write", 1424, 341), ("consume_chunk", 1776, 836), ("sha_256_close", 2624, 505),
   ("calc_sha_256", 3136, 80), ("right_rot", 3216, 37)]
#guard sha256TextPartition.padding ==
  [(43, 48), (1262, 1264), (1417, 1424), (1765, 1776), (2612, 2624), (3129, 3136)]

-- The proposal is accepted, and every function gets a body. This is a test,
-- not a proof: `#guard` runs compiled code.
--
-- `sha256_compress` gets 270 instructions over its 1214 bytes, which is what
-- `tests/x86/MANIFEST` records for the same symbol, reached there by
-- `scripts/x86-crosscheck.py` against `llvm-mc` rather than by this checker.
#guard (check sha256TextRegion sha256TextPartition 5000).map
    (fun acc => acc.bodies.map fun b => (b.1.name, b.2.length)) ==
  .ok [("xc_sha256", 13), ("sha256_compress", 270), ("sha_256_init", 33),
       ("sha_256_write", 82), ("consume_chunk", 219), ("sha_256_close", 138),
       ("calc_sha_256", 18), ("right_rot", 15)]

-- What acceptance assumes about the link: three calls reach undefined symbols.
-- The other four relocated call sites resolve inside the section, and
-- `check_relocated_internal_is_entry` says they land on function entries.
#guard (check sha256TextRegion sha256TextPartition 5000).map Accepted.assumedExternal ==
  .ok [(1618, "memcpy"), (2723, "memset"), (2787, "memset")]
#guard (check sha256TextRegion sha256TextPartition 5000).map
    (fun acc => acc.relocatedCalls.length) == .ok 7


/-! ## The control-flow graph of `MD5_memset`, checked by the kernel

`MD5_memset` is not straight-line: it is a counted loop, with a `jae` out of
the loop at offset 27 and an unconditional `jmp` back to the loop head at
offset 57. The leader algorithm therefore recovers four blocks and four edges,
and the kernel checks the whole of it — proposal and check together. -/

/-- The control-flow graph `CfgPropose` recovers for `MD5_memset`. Untrusted
data: `checkCfg` is the judge. -/
def md5MemsetCfg : CfgSpec := CfgPropose.ofFunction md5MemsetAccepted md5MemsetFunction

/-- **The recovered graph is the loop.** Four blocks — the prologue, the loop
test, the loop body and the epilogue — and four edges. Checked by the
kernel. -/
theorem md5_memset_cfg_shape :
    (md5MemsetCfg.blocks, md5MemsetCfg.edges) =
      ([{ start := 0, terminator := 14 }, { start := 21, terminator := 27 },
        { start := 33, terminator := 57 }, { start := 62, terminator := 63 }],
       [(0, 21), (21, 62), (21, 33), (33, 21)]) := by recover_cfg

/-- The checked graph as a term, so that `checkCfg_exit` can be applied to
it. -/
def md5MemsetCheckedCfg : CheckedCfg :=
  (checkCfg md5MemsetAccepted md5MemsetCfg).toOption.getD
    { accepted := md5MemsetAccepted, spec := md5MemsetCfg, bodies := [] }

/-- **The proposal is accepted.** Checked by the kernel. -/
theorem md5_memset_checkCfg_eq :
    checkCfg md5MemsetAccepted md5MemsetCfg = .ok md5MemsetCheckedCfg := by recover_cfg

/-- The twenty instructions are split six, three, nine and two. Checked by the
kernel. -/
theorem md5_memset_cfg_bodies :
    md5MemsetCheckedCfg.bodies.map (fun entry => (entry.1.start, entry.2.length)) =
      [(0, 6), (21, 3), (33, 9), (62, 2)] := by recover_cfg

/-! ### Three broken proposals, each rejected with its reason

Every rejection below is a proposal that differs from the accepted one in
exactly one way, so that the constructor named is the one the change earns. -/

/-- The accepted graph with the loop test's fall-through edge deleted. -/
def md5MemsetCfgMissing : CfgSpec :=
  { md5MemsetCfg with edges := [(0, 21), (21, 62), (33, 21)] }

/-- **A deleted edge is rejected**, naming the edge the decoded `jae` at offset
27 justifies and the proposal omits. Checked by the kernel. -/
theorem md5_memset_cfg_missing_edge :
    checkCfg md5MemsetAccepted md5MemsetCfgMissing = .error (.missingEdge 21 33) := by
  recover_cfg

/-- The accepted graph with an edge from the prologue to the epilogue, which no
instruction justifies: the prologue ends in a `mov`, whose only successor is
its fall-through. -/
def md5MemsetCfgInvented : CfgSpec :=
  { md5MemsetCfg with edges := md5MemsetCfg.edges ++ [(0, 62)] }

/-- **An invented edge is rejected**, even though its target really is a block
start. Checked by the kernel. -/
theorem md5_memset_cfg_unjustified_edge :
    checkCfg md5MemsetAccepted md5MemsetCfgInvented = .error (.unjustifiedEdge 0 62) := by
  recover_cfg

/-- The accepted graph with the loop test and the loop body merged into one
block, which puts the `jae` at offset 27 strictly inside a block. -/
def md5MemsetCfgMerged : CfgSpec :=
  { md5MemsetCfg with
    blocks := [{ start := 0, terminator := 14 }, { start := 21, terminator := 57 },
               { start := 62, terminator := 63 }],
    edges := [(0, 21), (21, 21)] }

/-- **A block with a branch inside it is rejected**, naming the block and the
address of the transfer. A block is straight-line code or it is not a block.
Checked by the kernel. -/
theorem md5_memset_cfg_interior_transfer :
    checkCfg md5MemsetAccepted md5MemsetCfgMerged =
      .error (.interiorTransfer { start := 21, terminator := 57 } 27) := by recover_cfg

/-! ### A non-vacuous instance of `checkCfg_exit`

`checkCfg_exit` assumes a loaded memory and a retirement, and a hypothesis
nobody exhibits might be unsatisfiable. The state is the same one
`md5_memset_sound_step_instance` uses: the unconditional `jmp` at offset 57,
which reads no memory and no flag, and which is the terminator of the loop
body. -/

/-- The block of the recovered graph that ends in the backward jump. -/
def md5MemsetLoopBlock : BlockSpec := { start := 33, terminator := 57 }

/-- The jump at offset 57, as the listing records it. -/
def md5MemsetJump : Decoded := { addr := 57, instr := .jmp 0xFFFFFFD7#32, size := 5 }

/-- The jump is the terminator of that block. Checked by the kernel. -/
theorem md5_memset_jump_in_block :
    md5MemsetJump ∈ md5MemsetCheckedCfg.body md5MemsetLoopBlock := by recover_cfg

/-- **`checkCfg_exit` is not vacuous.** Every hypothesis is discharged: the
acceptance of both rungs, the memory of `md5_memset_loaded`, and a concrete
state at offset 57 from which the machine really does retire. -/
theorem md5_memset_cfg_exit_instance (exit : Word) (core : State) (hrip : core.rip = 57#64) :
    ∃ next, Ext.stepOpt exit ⟨core, md5MemsetMemory⟩ = some next ∧
      ((∃ t, (md5MemsetLoopBlock.start, t) ∈ md5MemsetCfg.edges ∧
          next.core.rip.toNat = t ∧ ∃ b' ∈ md5MemsetCfg.blocks, b'.start = t) ∨
        (∃ g ∈ md5MemsetPartition.funcs, next.core.rip.toNat = g.entry) ∨
        md5MemsetAccepted.IsRelocatedCall md5MemsetJump.addr ∨
        md5MemsetJump.instr = .ret) := by
  obtain ⟨next, hstep, -⟩ := md5_memset_step exit core hrip
  refine ⟨next, hstep, checkCfg_exit md5_memset_check_eq md5_memset_checkCfg_eq
    (b := md5MemsetLoopBlock) (by decide) md5_memset_jump_in_block rfl md5_memset_loaded ?_ hstep⟩
  show core.rip.toNat = md5MemsetJump.addr
  rw [hrip]
  rfl

/-- The same fact stated as the inhabitation of `checkCfg_exit`'s hypothesis
set, which is the form the vacuity question is asked in. -/
theorem md5_memset_cfg_hypotheses_inhabited :
    ∃ (acc : Accepted) (c : CheckedCfg) (b : BlockSpec) (d : Decoded) (exit : Word)
      (m next : MState),
      check md5MemsetRegion md5MemsetPartition 128 = .ok acc ∧
        checkCfg acc md5MemsetCfg = .ok c ∧ b ∈ md5MemsetCfg.blocks ∧ d ∈ c.body b ∧
        d.addr = b.terminator ∧ md5MemsetRegion.LoadedIn m.memory ∧
        m.core.rip.toNat = d.addr ∧ Ext.stepOpt exit m = some next := by
  obtain ⟨next, hstep, -⟩ := md5_memset_step 0 ⟨fun _ => 0, 57, ⟨none, none, none, none, none,
    none⟩, 0⟩ rfl
  exact ⟨md5MemsetAccepted, md5MemsetCheckedCfg, md5MemsetLoopBlock, md5MemsetJump, 0,
    ⟨⟨fun _ => 0, 57, ⟨none, none, none, none, none, none⟩, 0⟩, md5MemsetMemory⟩, next,
    md5_memset_check_eq, md5_memset_checkCfg_eq, by decide, md5_memset_jump_in_block, rfl,
    md5_memset_loaded, rfl, hstep⟩

/-! ## The control-flow graphs of the ingested `sha256.o`, checked by evaluation

Each of the eight functions gets a graph, and `checkCfg` accepts all eight.
This runs at build time as compiled code: it adds no axioms, and it is a test,
not a proof. -/

-- Every function of the object, with the number of blocks and edges its graph
-- has, and the fact that the checker accepts it.
#guard (check sha256TextRegion sha256TextPartition 5000).map
    (fun acc => acc.partition.funcs.map fun f =>
      let spec := CfgPropose.ofFunction acc f
      (f.name, spec.blocks.length, spec.edges.length, (checkCfg acc spec).toOption.isSome)) ==
  .ok [("xc_sha256", 2, 1, true), ("sha256_compress", 10, 12, true),
       ("sha_256_init", 1, 0, true), ("sha_256_write", 16, 20, true),
       ("consume_chunk", 27, 31, true), ("sha_256_close", 13, 15, true),
       ("calc_sha_256", 4, 3, true), ("right_rot", 1, 0, true)]

-- `sha256_compress`, the 270-instruction compression function, in detail: ten
-- blocks and twelve edges over its three loops, as `(start, terminator)` pairs
-- and `(source, target)` pairs of block start addresses.
#guard (check sha256TextRegion sha256TextPartition 5000).toOption.map
    (fun acc =>
      let f := { name := "sha256_compress", entry := 48, size := 1214 : FunctionSpec }
      let spec := CfgPropose.ofFunction acc f
      ((spec.blocks.map fun b => (b.start, b.terminator)), spec.edges)) ==
  some ([(48, 67), (77, 84), (90, 223), (228, 228), (238, 245), (251, 574), (579, 682),
         (692, 699), (705, 1122), (1127, 1261)],
        [(48, 77), (77, 228), (77, 90), (90, 77), (228, 238), (238, 579), (238, 251),
         (251, 238), (579, 692), (692, 1127), (692, 705), (705, 692)])

-- Every instruction of `sha256_compress` lands in exactly one block: the ten
-- block bodies sum to the function's 270 instructions.
#guard (check sha256TextRegion sha256TextPartition 5000).toOption.map
    (fun acc =>
      let f := { name := "sha256_compress", entry := 48, size := 1214 : FunctionSpec }
      ((checkCfg acc (CfgPropose.ofFunction acc f)).toOption.map fun c =>
        ((c.bodies.map fun entry => entry.2.length).sum, c.bodies.length))) ==
  some (some (270, 10))

end Silmaril.X86.Decompile.Examples

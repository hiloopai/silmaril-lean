module

public import Silmaril.X86.Decompile.Cfg
public import Silmaril.X86.Decompile.Cert
/-!
# Preparsed x86 instruction and block representations

The instruction array is usable independently of a byte parser: `Program.step`
executes its instruction and stored length using the existing `Ext` machine and
memory. `WellFormed` checks representation invariants; `SourceCertificate` is a
separate, optional proof connecting the representation to exact canonical bytes.
A trusted-parser workflow may omit that certificate, with an explicitly larger
trust boundary. This first interface covers canonical `Ext` instructions; it
makes no claim about noncanonical spellings supported by `Ext.Wire`.

Blocks contain instructions and explicit successors. Calls and their eventual
return continuations are distinct: the continuation is an analysis edge, not the
RIP produced by executing CALL. Flattening equality validates the change of
representation and preserves lookup and execution. Structural acceptance alone
is not a functional correctness or termination theorem.
-/

@[expose] public section

namespace Silmaril.X86.Verify

open Decompile

/-- An instruction array with absolute addresses and original consumed lengths.
An ELF-relative listing can use base zero. -/
structure Program where
  base : Nat
  instructions : Array Decoded
  deriving DecidableEq, Repr

/-- Find an instruction without fetching or decoding memory. -/
def Program.lookup (program : Program) (address : Nat) : Option Decoded :=
  at? program.instructions.toList address

/-- The exclusive end of the represented byte span. For a well-formed listing
this follows from its retained instruction addresses and lengths. -/
def Program.endAddress (program : Program) : Nat :=
  (program.instructions.toList.getLast?.map fun instruction =>
    instruction.addr + instruction.size).getD program.base

/-- Representation invariants, independently checkable without source bytes. -/
def Program.WellFormed (program : Program) : Prop :=
  (∀ d ∈ program.instructions.toList, 0 < d.size ∧ d.size = d.instr.length) ∧
    (starts program.instructions.toList).Pairwise (· < ·) ∧
    List.IsChain (fun d e => e.addr = d.addr + d.size) program.instructions.toList ∧
    (∀ d ∈ program.instructions.toList.head?, d.addr = program.base)

instance (program : Program) : Decidable program.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Optional evidence tying a representation to complete canonical source bytes.
This is separate from `WellFormed` and is never required to run analyses. -/
def Program.SourceCertificate (program : Program) (region : Region) (fuel : Nat) : Prop :=
  region.base = program.base ∧ region.decode? fuel = some program.instructions.toList

instance (program : Program) (region : Region) (fuel : Nat) :
    Decidable (program.SourceCertificate region fuel) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Executable canonical parser; its result is ordinary data. -/
def parseProgram (region : Region) (fuel : Nat) : Option Program :=
  (region.decode? fuel).map fun instructions => ⟨region.base, instructions.toArray⟩

/-- A successful checked parser supplies its separate source certificate. -/
theorem parseProgram_source {region : Region} {fuel : Nat} {program : Program}
    (parsed : parseProgram region fuel = some program) :
    program.SourceCertificate region fuel := by
  unfold parseProgram at parsed
  cases decoded : region.decode? fuel with
  | none => simp [decoded] at parsed
  | some instructions =>
    simp only [decoded, Option.map_some, Option.some.injEq] at parsed
    subst program
    exact ⟨rfl, by simpa using decoded⟩

/-- Decoder checking implies the independent representation invariants. -/
theorem Program.SourceCertificate.wellFormed {program : Program} {region : Region} {fuel : Nat}
    (source : program.SourceCertificate region fuel) : program.WellFormed := by
  refine ⟨?_, Region.decode?_addr_pairwise source.2, Region.decode?_chain source.2, ?_⟩
  · intro d member
    exact ⟨Region.decode?_size_pos source.2 d member, Region.decode?_size source.2 d member⟩
  · intro d member
    exact (Region.decode?_head source.2 d member).trans source.1

/-- Execute the retained instruction with its retained length. No memory fetch,
byte decoder, new register file or new memory model is involved. -/
def Program.execute (instruction : Decoded) (exit : Word) (state : MState) : Ext.Outcome :=
  match Ext.execWithLength instruction.instr instruction.size state.core state.memory with
  | .ok core memory =>
    if instruction.instr = .ret ∧ core.rip = exit then .returned ⟨core, memory⟩
    else .retired ⟨core, memory⟩
  | .dataFault => .dataFault instruction.instr
  | .divideError => .divideFault
  | .undefinedCondition condition => .undefinedCondition condition
  | .trap => .trapped

/-- Representation-first execution. A RIP outside the listing is undecodable;
this does not assert anything about bytes outside the represented region. -/
def Program.step (program : Program) (exit : Word) (state : MState) : Ext.Outcome :=
  match program.lookup state.core.rip.toNat with
  | none => .undecodable
  | some instruction => Program.execute instruction exit state

/-- At a represented address, a checked source image makes representation-first
execution identical to fetching, decoding and executing the actual bytes. The
loaded-image premise is about the current memory; multi-step clients must
preserve it across writes. -/
theorem Program.step_eq_raw {program : Program} {region : Region} {fuel : Nat}
    (source : program.SourceCertificate region fuel) {exit : Word} {state : MState}
    (loaded : region.LoadedIn state.memory) {instruction : Decoded}
    (present : program.lookup state.core.rip.toNat = some instruction) :
    program.step exit state = Ext.step exit state := by
  obtain ⟨member, address⟩ := at?_eq_some present
  have fetched := Region.decode?_fetch source.2 loaded member
  rw [address] at fetched
  have size : instruction.size = instruction.instr.length :=
    Region.decode?_size source.2 instruction member
  simp only [Program.step, present, Program.execute, size,
    Ext.execWithLength_canonical, Ext.step, fetched]
  rfl

/-- Retirement-only execution on the preparsed representation. -/
def Program.stepOpt (program : Program) (exit : Word) (state : MState) : Option MState :=
  match program.step exit state with
  | .retired next => some next
  | _ => none

/-- A finite number of representation-level retirements. -/
def Program.Advances (program : Program) (exit : Word) (initial final : MState) : Prop :=
  Machine.Execution.Reaches (program.stepOpt exit) initial final

/-- Finite representation-level execution followed by a designated return. -/
def Program.Returns (program : Program) (exit : Word) (initial final : MState) : Prop :=
  ∃ n mid, Machine.Execution.run (program.stepOpt exit) n initial = some mid ∧
    program.step exit mid = .returned final

/-- The local obligation needed to lower one represented step to source bytes.
It must be preserved along the execution; structural CFG validation does not
establish this memory invariant or reachability property. -/
def Program.LoadedAt (program : Program) (region : Region) (state : MState) : Prop :=
  region.LoadedIn state.memory ∧
    ∃ instruction, program.lookup state.core.rip.toNat = some instruction

/-- Verify on instruction arrays, then lower an exact finite run to the raw
machine. `SafePrefixes` asks only for the loaded-image and represented-RIP
obligation at each executed prestate, including faulting prestates. -/
theorem Program.run_eq_raw {program : Program} {region : Region} {fuel : Nat}
    (source : program.SourceCertificate region fuel) (exit : Word) (n : Nat)
    (initial : MState)
    (safe : Machine.Execution.SafePrefixes (program.stepOpt exit)
      (program.LoadedAt region) n initial) :
    Machine.Execution.run (program.stepOpt exit) n initial =
      Machine.Execution.run (Ext.stepOpt exit) n initial := by
  induction n generalizing initial with
  | zero => rfl
  | succ n ih =>
    obtain ⟨loaded, instruction, present⟩ := safe 0 (by omega) initial rfl
    have step : program.stepOpt exit initial = Ext.stepOpt exit initial := by
      simp only [Program.stepOpt, Ext.stepOpt, Program.step_eq_raw source loaded present]
      rfl
    simp only [Machine.Execution.run_succ]
    rw [← step]
    cases retired : program.stepOpt exit initial with
    | none => rfl
    | some next =>
      simp only [Option.bind_some]
      apply ih next
      intro k bound mid executed
      apply safe (k + 1) (by omega) mid
      simpa only [Machine.Execution.run_succ, retired, Option.bind_some] using executed

/-- Lower a representation-level advance using a proved invariant on its
retirement-reachable states. -/
theorem Program.Advances.to_raw {program : Program} {region : Region} {fuel : Nat}
    (source : program.SourceCertificate region fuel) {exit : Word} {initial final : MState}
    (execution : program.Advances exit initial final)
    (preserved : ∀ n state, Machine.Execution.run (program.stepOpt exit) n initial = some state →
      program.LoadedAt region state) : Decompile.Advances exit initial final := by
  obtain ⟨n, executed⟩ := execution
  have safe : Machine.Execution.SafePrefixes (program.stepOpt exit)
      (program.LoadedAt region) n initial := by
    intro k _ state partialRun
    exact preserved k state partialRun
  exact ⟨n, (Program.run_eq_raw source exit n initial safe).symm.trans executed⟩

/-- A functional contract proved about the instruction array can be lowered to
`Ext.Returns` once source identity and image preservation are supplied. -/
theorem Program.Returns.to_raw {program : Program} {region : Region} {fuel : Nat}
    (source : program.SourceCertificate region fuel) {exit : Word} {initial final : MState}
    (execution : program.Returns exit initial final)
    (preserved : ∀ n state, Machine.Execution.run (program.stepOpt exit) n initial = some state →
      program.LoadedAt region state) : Ext.Returns exit initial final := by
  obtain ⟨n, mid, executed, returned⟩ := execution
  obtain ⟨loaded, instruction, present⟩ := preserved n mid executed
  have safe : Machine.Execution.SafePrefixes (program.stepOpt exit)
      (program.LoadedAt region) n initial := by
    intro k _ state partialRun
    exact preserved k state partialRun
  refine ⟨n, mid, (Program.run_eq_raw source exit n initial safe).symm.trans executed, ?_⟩
  exact (Program.step_eq_raw source loaded present).symm.trans returned

/-- Analysis edges. The return continuation of a direct call is recorded
separately from its immediate machine successor. -/
inductive Successor where
  | fallthrough (target : Nat)
  | jump (target : Nat)
  | branch (target : Nat)
  | call (target : Nat)
  | returnContinuation (target : Nat)
  | ret
  | halt
  deriving DecidableEq, Repr

/-- Use the existing decoded-edge arithmetic, including 64-bit wrapping. -/
def instructionSuccessors (instruction : Decoded) : List Successor :=
  instruction.edges.map fun edge =>
    match edge with
    | .fallthrough target =>
      match instruction.instr with
      | .call _ => .returnContinuation target
      | _ => .fallthrough target
    | .jump target => .jump target
    | .branch target => .branch target
    | .call target => .call target
    | .ret => .ret
    | .halt => .halt

/-- Intraprocedural analysis targets; calls themselves leave the current block. -/
def Successor.cfgTarget? : Successor → Option Nat
  | .fallthrough target | .jump target | .branch target | .returnContinuation target => some target
  | _ => none

/-- All statically named destinations, including direct call targets. -/
def Successor.target? : Successor → Option Nat
  | .fallthrough target | .jump target | .branch target | .call target |
      .returnContinuation target => some target
  | _ => none

def Successor.callTarget? : Successor → Option Nat
  | .call target => some target
  | _ => none

@[simp] theorem Successor.callTarget?_eq_some {successor : Successor} {target : Nat} :
    successor.callTarget? = some target ↔ successor = .call target := by
  cases successor <;> simp [Successor.callTarget?]

/-- Every direct call target in the instruction array, independent of parsing. -/
def Program.callTargets (program : Program) : List Nat :=
  program.instructions.toList.flatMap fun instruction =>
    (instructionSuccessors instruction).filterMap Successor.callTarget?

/-- The call analysis reports exactly the explicitly represented call edges. -/
theorem Program.mem_callTargets {program : Program} {target : Nat} :
    target ∈ program.callTargets ↔
      ∃ instruction ∈ program.instructions.toList,
        Successor.call target ∈ instructionSuccessors instruction := by
  simp [Program.callTargets, List.mem_flatMap, List.mem_filterMap]

/-- Intraprocedural instruction edges, with source addresses retained. -/
def Program.directEdges (program : Program) : List (Nat × Nat) :=
  program.instructions.toList.flatMap fun instruction =>
    (instructionSuccessors instruction).filterMap fun successor =>
      successor.cfgTarget?.map (instruction.addr, ·)

/-- Syntactic backward intraprocedural edges. This does not assert that the
edge is reachable or that it is taken on a particular execution. -/
def Program.backEdges (program : Program) : List (Nat × Nat) :=
  program.directEdges.filter fun edge => decide (edge.2 ≤ edge.1)

theorem Program.mem_backEdges_le {program : Program} {edge : Nat × Nat}
    (member : edge ∈ program.backEdges) : edge.2 ≤ edge.1 := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- An actual block body, rather than only a pair of address bounds. -/
structure BasicBlock where
  instructions : Array Decoded
  successors : List Successor
  deriving DecidableEq, Repr

/-- Nonempty straight-line interiors and the exact terminator successors.
Canonical sizes, address order and adjacency are checked on the flattened
program by `BlockProgram.Validates`. -/
def BasicBlock.WellFormed (block : BasicBlock) : Prop :=
  block.instructions.toList ≠ [] ∧
    (∀ instruction ∈ block.instructions.toList.dropLast, retiring instruction.instr = true) ∧
    block.successors =
      ((block.instructions.toList.getLast?).map instructionSuccessors).getD []

instance (block : BasicBlock) : Decidable block.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A block graph whose bodies retain all original instruction data. -/
structure BlockProgram where
  base : Nat
  blocks : Array BasicBlock
  deriving DecidableEq, Repr

/-- Flatten block bodies without changing instruction values, addresses or sizes. -/
def BlockProgram.toProgram (blocks : BlockProgram) : Program :=
  ⟨blocks.base, (blocks.blocks.toList.flatMap fun block => block.instructions.toList).toArray⟩

/-- Block entry addresses. Empty blocks are excluded separately by validation. -/
def BlockProgram.blockStarts (blocks : BlockProgram) : List Nat :=
  blocks.blocks.toList.filterMap fun block =>
    block.instructions.toList.head?.map Decoded.addr

/-- A destination inside the represented byte span must be a block entry;
this also rejects branches into an instruction's middle bytes. Destinations
outside the span remain explicit open edges, including external calls. -/
def BlockProgram.targetsAligned (blocks : BlockProgram) (program : Program) : Bool :=
  blocks.blocks.toList.all fun block =>
    block.successors.all fun successor =>
      match successor.target? with
      | none => true
      | some target =>
        if program.base ≤ target ∧ target < program.endAddress then
          blocks.blockStarts.contains target
        else true

/-- A decidable translation-validation boundary between array and block forms. -/
def BlockProgram.Validates (blocks : BlockProgram) (program : Program) : Prop :=
  blocks.toProgram = program ∧ program.WellFormed ∧
    (∀ block ∈ blocks.blocks.toList, block.WellFormed) ∧
    blocks.targetsAligned program = true

instance (blocks : BlockProgram) (program : Program) : Decidable (blocks.Validates program) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def checkBlocks (blocks : BlockProgram) (program : Program) : Bool :=
  decide (blocks.Validates program)

@[simp] theorem checkBlocks_eq_true {blocks : BlockProgram} {program : Program} :
    checkBlocks blocks program = true ↔ blocks.Validates program := by
  simp [checkBlocks]

/-- Checked block conversion preserves every lookup, even without source bytes. -/
theorem BlockProgram.lookup_eq {blocks : BlockProgram} {program : Program}
    (checked : blocks.Validates program) (address : Nat) :
    blocks.toProgram.lookup address = program.lookup address := by rw [checked.1]

/-- Checked block conversion preserves all representation-level execution. -/
theorem BlockProgram.step_eq {blocks : BlockProgram} {program : Program}
    (checked : blocks.Validates program) (exit : Word) (state : MState) :
    blocks.toProgram.step exit state = program.step exit state := by rw [checked.1]

/-- Existing CFG range proposals can be materialized into instruction bodies.
This constructor does not silently assert that `checkCfg` accepted the proposal;
`Validates` and the existing CFG checker remain explicit checks. -/
def blocksFromCfg (program : Program) (specification : CfgSpec) : BlockProgram :=
  ⟨program.base, specification.blocks.toArray.map fun range =>
    let body := blockBody program.instructions.toList range
    ⟨body.toArray, (body.getLast?.map instructionSuccessors).getD []⟩⟩

/-- Group at leaders and after transfers. This is a proposal generator; checking
its output uses `Validates`, independently of how the grouping was obtained. -/
def groupInstructions (leaders : List Nat) : List Decoded → List (List Decoded)
  | [] => []
  | instruction :: rest =>
    match groupInstructions leaders rest with
    | [] => [[instruction]]
    | block :: blocks =>
      if retiring instruction.instr && !(block.head?.any fun first => leaders.contains first.addr)
      then (instruction :: block) :: blocks
      else [instruction] :: block :: blocks

/-- Recover block proposals from already preparsed data, without invoking a
byte parser. Targets inside or outside the represented function remain explicit. -/
def recoverBlocks (program : Program) : BlockProgram :=
  let leaders := program.base :: program.instructions.toList.flatMap fun instruction =>
    (instructionSuccessors instruction).filterMap fun successor =>
      match successor with
      | .jump target | .branch target | .call target | .returnContinuation target => some target
      | _ => none
  let groups := groupInstructions leaders program.instructions.toList
  ⟨program.base, groups.toArray.map fun body =>
    ⟨body.toArray, (body.getLast?.map instructionSuccessors).getD []⟩⟩

/-- Parse and propose blocks. The source and structural certificates can be
checked separately, or omitted under an explicitly trusted parser boundary. -/
def parseBlocks (region : Region) (fuel : Nat) : Option BlockProgram :=
  (parseProgram region fuel).map recoverBlocks

end Silmaril.X86.Verify

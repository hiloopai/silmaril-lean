module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Address
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract

theorem resolve_ordinary (units : Array Mir.Unit) (placement : MirSem.Placement)
    (symbol : String) (offset : Nat) (ordinary : Ordinary symbol) :
    resolve units placement symbol offset =
      (MirSem.symValue units placement symbol).map (fun value => BitVec.ofNat 64 (value + offset)) := by
  simp only [resolve, ite_eq_right ordinary]

theorem resolve_reserved (units : Array Mir.Unit) (placement : MirSem.Placement) (offset : Nat) :
    resolve units placement reservedFrame offset = none := by
  simp [resolve]

theorem initial (units : Array Mir.Unit) (placement : MirSem.Placement) (frame : Lir.Frame Nat) :
    Invariant units placement {} frame (Leaf.initialMeaning frame (resolve units placement)) :=
  ⟨Leaf.initial_rooted frame _, Total.empty_total _, rfl⟩

/-- Reset the actual source DAG to the checker's empty root maps. -/
theorem seed_invariant (units : Array Mir.Unit) (placement : MirSem.Placement)
    (frame sourceFrame : Lir.Frame Nat) (sourceState : State) (meaning : Interpretation)
    (source : Roots.OpResult {} sourceState sourceFrame
      (Leaf.initialMeaning frame (resolve units placement)) meaning)
    (total : Total.TotalNodes sourceState.nodes meaning) :
    Invariant units placement { nodes := sourceState.nodes } frame meaning :=
  ⟨Leaf.seed_rooted frame sourceFrame _ sourceState meaning source, total, source.extension.address⟩

/-- Writing the returned root does not change the actual interned DAG. -/
theorem addr_nodes (state : State) (dest : Nat) (symbol : String) (offset : Nat) :
    ((evalInstr (.addr dest symbol offset)).run state).2.nodes =
      ((intern (.addr symbol offset)).run state).2.nodes := rfl

/-- Successful real address resolution constructs the source symbolic result
and preserves the address interpretation, without completing partial inputs. -/
theorem evalInstr_sound (units : Array Mir.Unit) (placement : MirSem.Placement)
    (state : State) (frame : Lir.Frame Nat) (meaning : Interpretation)
    (invariant : Invariant units placement state frame meaning)
    (dest : Nat) (symbol : String) (offset : Nat) (word : Lir.Word)
    (resolved : resolve units placement symbol offset = some word) :
    ∃ newMeaning, Roots.OpResult state ((evalInstr (.addr dest symbol offset)).run state).2
      (frame.set dest word) meaning newMeaning ∧
      Invariant units placement ((evalInstr (.addr dest symbol offset)).run state).2
        (frame.set dest word) newMeaning := by
  have defined : (Expr.addr symbol offset).eval meaning = some word := by
    simpa only [Expr.eval, invariant.address] using resolved
  obtain ⟨newMeaning, result, total⟩ := Total.intern_sound state frame meaning invariant.rooted invariant.total
    (.addr symbol offset) trivial word defined
  have rooted := Roots.writeReg_rooted _ frame newMeaning result.rooted dest _ word result.bounded result.selected
  exact ⟨newMeaning, ⟨rooted, result.extension, result.grows, result.effects⟩,
    rooted, total, result.extension.address.trans invariant.address⟩

/-- The actual retained-partial-leaf guard derives candidate address resolution
from old total nodes. No successful candidate execution or target read is a premise. -/
theorem candidate_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory) (meaning : Interpretation)
    (invariant : Invariant units placement state frame meaning)
    (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size)
    (dest : Nat) (symbol : String) (offset : Nat)
    (guarded : Candidate.Guarded sourceSize ((evalInstr (.addr dest symbol offset)).run state).2.nodes) :
    ∃ word newMeaning, resolve units placement symbol offset = some word ∧
      InstructionExec (calls units placement) (.addr dest symbol offset) frame memory (frame.set dest word) memory ∧
      Roots.OpResult state ((evalInstr (.addr dest symbol offset)).run state).2
        (frame.set dest word) meaning newMeaning ∧
      Invariant units placement ((evalInstr (.addr dest symbol offset)).run state).2
        (frame.set dest word) newMeaning := by
  rw [addr_nodes] at guarded
  obtain ⟨word, defined⟩ := Leaf.intern_partial_defined state meaning invariant.rooted.coherent invariant.total
    sourceSize old (.addr symbol offset) rfl guarded
  have resolved : resolve units placement symbol offset = some word := by
    simpa only [Expr.eval, invariant.address] using defined
  obtain ⟨newMeaning, result, after⟩ := evalInstr_sound units placement state frame meaning invariant dest symbol offset word resolved
  exact ⟨word, newMeaning, resolved, .addr resolved, result, after⟩

/-- The ordinary resolver matches the genuine Mir step, including missing symbols.
The ordinary hypothesis is essential: native reserved-frame semantics are separate. -/
theorem mir_step_addr (units : Array Mir.Unit) (placement : MirSem.Placement)
    (state : MirSem.State) (block : Mir.Block) (dest : Nat) (symbol : String) (offset : Nat)
    (ordinary : Ordinary symbol) (found : state.func.blocks[state.label]? = some block)
    (selected : block.instrs[state.index]? = some (.addr dest symbol offset)) :
    MirSem.step units placement state =
      match resolve units placement symbol offset with
      | none => .stuck
      | some word => .running { state with index := state.index + 1, frame := state.frame.set dest word } := by
  rw [resolve_ordinary units placement symbol offset ordinary]
  simp only [MirSem.step, found, selected]
  cases MirSem.symValue units placement symbol <;> rfl

theorem mir_step_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (state : MirSem.State) (block : Mir.Block) (dest : Nat) (symbol : String) (offset : Nat)
    (ordinary : Ordinary symbol) (found : state.func.blocks[state.label]? = some block)
    (selected : block.instrs[state.index]? = some (.addr dest symbol offset))
    (word : Lir.Word) (resolved : resolve units placement symbol offset = some word) :
    MirSem.step units placement state =
      .running { state with index := state.index + 1, frame := state.frame.set dest word } := by
  rw [mir_step_addr units placement state block dest symbol offset ordinary found selected, resolved]

theorem mir_step_missing (units : Array Mir.Unit) (placement : MirSem.Placement)
    (state : MirSem.State) (block : Mir.Block) (dest : Nat) (symbol : String) (offset : Nat)
    (ordinary : Ordinary symbol) (found : state.func.blocks[state.label]? = some block)
    (selected : block.instrs[state.index]? = some (.addr dest symbol offset))
    (missing : resolve units placement symbol offset = none) :
    MirSem.step units placement state = .stuck := by
  rw [mir_step_addr units placement state block dest symbol offset ordinary found selected, missing]

/-- A fresh register write preserves agreement on the actual original partial
register range and all slots. -/
theorem agrees_fresh {base : Nat} {source target : Lir.Frame Nat}
    (agrees : PureSoundness.FrameAgrees base source target) (fresh : Nat) (above : base ≤ fresh)
    (word : Lir.Word) : PureSoundness.FrameAgrees base source (target.set fresh word) := by
  refine ⟨agrees.slots, ?_⟩
  intro reg below
  have different : reg ≠ fresh := by omega
  simpa only [Lir.Frame.get_set, ite_eq_right different] using agrees.registers reg below

/-- The guarded fresh address and its real move commit execute from a distinct
partial target frame, preserving memory and agreement on the original range. -/
theorem candidate_commit_success (units : Array Mir.Unit) (placement : MirSem.Placement)
    (state : State) (source target : Lir.Frame Nat) (memory : Lir.Memory) (meaning : Interpretation)
    (invariant : Invariant units placement state target meaning)
    (sourceSize : Nat) (old : sourceSize ≤ state.nodes.size)
    (base dest fresh : Nat) (above : base ≤ fresh)
    (agrees : PureSoundness.FrameAgrees base source target) (symbol : String) (offset : Nat)
    (guarded : Candidate.Guarded sourceSize ((evalInstr (.addr fresh symbol offset)).run state).2.nodes) :
    ∃ word, resolve units placement symbol offset = some word ∧
      InstructionExec (calls units placement) (.addr dest symbol offset) source memory (source.set dest word) memory ∧
      InstructionsExec (calls units placement) [.addr fresh symbol offset, .op (.move dest fresh)]
        target memory ((target.set fresh word).set dest word) memory ∧
      PureSoundness.FrameAgrees base (source.set dest word) ((target.set fresh word).set dest word) := by
  obtain ⟨word, _, resolved, executed, _, _⟩ := candidate_success units placement state target memory meaning invariant
    sourceSize old fresh symbol offset guarded
  refine ⟨word, resolved, .addr resolved, .cons executed (.cons (.op ?_) .nil),
    Context.agrees_set (agrees_fresh agrees fresh above word) dest word⟩
  simp [Lir.Op.exec]

end Silmaril.Compiler.Native.Optimize.Validation.Address

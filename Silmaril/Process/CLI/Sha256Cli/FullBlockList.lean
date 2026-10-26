module

public import Silmaril.Process.CLI.Sha256Cli.FullBlockIteration
public import Silmaril.Process.Syscall.InputStreamParts

/-! # Finite lists of actual full-block reads

The existence theorem selects admitted 64-byte transfers from an immutable
matched stream. It composes actual read/CALL/body/RET/restart steps, preserving
natural descriptor cursors separately from the modular machine total. It does
not assert progress or cover all smaller transfers admitted by the syscall.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.FullBlockIteration

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

set_option maxRecDepth 100000

/-- Select one admitted full transfer from the supplied actual stream match. -/
theorem Ready.read_block {initial : Memory} {top : Nat} {c : Core} {s : Syscall.State}
    {total : Word} {state : Silmaril.Crypto.SHA256.State} {descriptor : Descriptor}
    (ready : Ready initial top c s total state) (block : List Byte) (full : block.length = 64)
    (opened : s.descriptors 0 = some descriptor) (readable : descriptor.readable = true)
    (matched : descriptor.input.Matches descriptor.cursor block) (flags : Word)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (next : Core) (memory : Memory),
      let after := { s.setDescriptor 0 { descriptor with cursor := descriptor.cursor + block.length }
        with memory := memory }
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [.read 0 block] ⟨next, after⟩ ∧
      Ready initial top next after (total + 64) (Driver.compressBlock state block) := by
  let copied : Memory := { s.memory with bytes := Memory.install s.memory.bytes 0x401620 block }
  let after : Syscall.State :=
    { s.setDescriptor 0 { descriptor with cursor := descriptor.cursor + block.length } with memory := copied }
  have permission : s.memory.Permitted .write 0x401620 block.length := by
    rw [full]
    exact ready.frame.bss_permitted .write rfl _ _ (by decide) (by decide)
  have write : s.memory.writeBytes 0x401620 block = some copied := ite_eq_left permission
  have effect : Syscall.Step s (.read 0 0x401620 64) (.read 0 block) (.returned (.ok 64)) after := by
    simpa only [full, after] using Syscall.Step.readSome ready.running opened readable matched
      (by omega) (by omega) (by rw [full]; decide) permission write
  obtain ⟨actual, next, memory, _, eventEq, run, fresh⟩ := ready.read_full flags effect geometry stack
  have actualEq : actual = block := by cases eventEq; rfl
  rw [actualEq] at fresh
  exact ⟨next, memory, run, fresh⟩

/-- Execute a supplied finite list of full blocks with the selected admitted
full-transfer schedule. No upper bound on the natural cursor is inferred from
the modular total, and no read availability/progress theorem is asserted. -/
theorem Ready.read_blocks {initial : Memory} {top : Nat} {c : Core} {s : Syscall.State}
    {total : Word} {state : Silmaril.Crypto.SHA256.State} {descriptor : Descriptor}
    (ready : Ready initial top c s total state) (blocks : List (List Byte))
    (full : ∀ block ∈ blocks, block.length = 64)
    (opened : s.descriptors 0 = some descriptor) (readable : descriptor.readable = true)
    (matched : descriptor.input.Matches descriptor.cursor blocks.flatten) (flags : Word)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (next : Core) (memory : Memory),
      let after := { s.setDescriptor 0 { descriptor with cursor := descriptor.cursor + blocks.flatten.length }
        with memory := memory }
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ (blocks.map (Event.read 0)) ⟨next, after⟩ ∧
      Ready initial top next after (total + BitVec.ofNat 64 blocks.flatten.length)
        (blocks.foldl Driver.compressBlock state) := by
  induction blocks generalizing c s total state descriptor with
  | nil =>
    have unchanged : s.setDescriptor 0 descriptor = s := by
      cases s
      simp only [State.setDescriptor, State.mk.injEq, true_and, and_true]
      exact Function.update_eq_self_iff.mpr opened.symm
    refine ⟨c, s.memory, ?_, ?_⟩
    · simpa only [List.flatten_nil, List.length_nil, Nat.add_zero, unchanged,
        List.map_nil] using (Machine.Trace.Runs.refl (state := (⟨c, s⟩ : Output.PS)))
    · simpa only [List.flatten_nil, List.length_nil, Nat.add_zero, unchanged,
        BitVec.add_zero, List.foldl_nil] using ready
  | cons block blocks ih =>
    have size := full block (by simp)
    have rest : ∀ b ∈ blocks, b.length = 64 := by intro b member; exact full b (by simp [member])
    obtain ⟨middle, firstMemory, firstRun, firstReady⟩ := ready.read_block block size opened readable
      (matched.left) flags geometry stack
    let advanced : Descriptor := { descriptor with cursor := descriptor.cursor + block.length }
    let firstState : Syscall.State := { s.setDescriptor 0 advanced with memory := firstMemory }
    have firstOpen : firstState.descriptors 0 = some advanced := by
      simp only [firstState, State.setDescriptor, Function.update_self]
    obtain ⟨next, memory, remaining, finalReady⟩ := ih firstReady rest firstOpen readable matched.right
    have totalEq : (total + 64) + BitVec.ofNat 64 blocks.flatten.length =
        total + BitVec.ofNat 64 (block.length + blocks.flatten.length) := by
      change (total + BitVec.ofNat 64 64) + BitVec.ofNat 64 blocks.flatten.length = _
      rw [size, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [totalEq] at finalReady
    refine ⟨next, memory, ?_, ?_⟩
    · simpa only [List.map_cons, List.singleton_append, firstState, advanced,
        State.setDescriptor, Function.update_idem, List.flatten_cons, List.length_append,
        Nat.add_assoc] using firstRun.append remaining
    · simpa only [firstState, advanced, State.setDescriptor, Function.update_idem,
        List.flatten_cons, List.length_append, Nat.add_assoc, List.foldl_cons] using finalReady

end Silmaril.Process.CLI.Sha256Cli.FullBlockIteration

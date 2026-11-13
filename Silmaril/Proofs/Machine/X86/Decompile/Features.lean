module

public import Silmaril.Machine.X86.Decompile.Features.Defs

/-! A checked ordinary-integer block runs on the actual fetched-byte Features
machine for any feature set and extension list. Exact loaded-byte decoding
selects the integer dispatcher first, and checker acceptance excludes every
feature-dependent bitcount instruction. This is not a full FFI contract. -/
@[expose] public section
namespace Silmaril.Machine.X86.Decompile.Features
open Silmaril Silmaril.X86
open Silmaril.X86.Decompile.SemLift
open Silmaril.Process (Memory)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The checker's actual supported instruction fragment is independent of
LZCNT/BMI1/POPCNT; those instructions have no successful symbolic step. -/
theorem symStep_baseRequirement {asm : Assume} {before after : SSt} {i : Ext.Instr}
    (checked : symStep asm before i = some after) :
    Silmaril.X86.Features.baseRequirement i = none := by
  cases i <;> first | rfl | simp [symStep] at checked

/-- Exact fetched and decoded integer bytes force the actual Features base
branch before any extension decoder can be consulted. -/
theorem retire_of_loaded {base exit : Word} {bytes : List Byte}
    {before after : X86.MState} {offset len : Nat} {i : Ext.Instr}
    (original : Silmaril.X86.Features.State)
    (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension)
    (loaded : Ext.Loaded before.memory base bytes)
    (pc : before.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : Ext.decode ((bytes.drop offset).take len) = some (i, len))
    (safe : Silmaril.X86.Features.baseRequirement i = none)
    (executed : Ext.stepOpt exit before = some after) :
    Silmaril.X86.Features.step featureSet extensions exit (lift original before) =
      .retired (lift original after) := by
  have fetched : Ext.fetch before.memory before.core.rip.toNat = .decoded i len := by
    apply Ext.fetch_eq_decoded_iff.mpr
    refine ⟨(bytes.drop offset).take len, ?_, decoded⟩
    rw [pc, loaded.toNat_add (by have := (Ext.decode_length decoded).2.1; omega)]
    exact loaded.fetchBytes_sub (Ext.decode_length decoded).2.1 fits
  have dispatched := Silmaril.X86.Features.step_of_base
    (m := lift original before) (F := featureSet) (exts := extensions) (exit := exit) fetched
  rw [dispatched]
  have retired : Ext.step exit before = .retired after := Ext.stepOpt_eq_some_iff.mp executed
  simp only [Silmaril.X86.Features.baseCheck, safe]
  change Silmaril.X86.Features.Outcome.ofBase (original.setCore before.core)
    (Ext.step exit before) = .retired (lift original after)
  rw [retired]
  rfl

private theorem run_succ_decompose {asm : Assume} {code : List Byte} {count : Nat}
    {before after : SSt}
    (checked : Silmaril.X86.Decompile.SemLift.run asm code (count + 1) before = some after) :
    ∃ instruction len next,
      Ext.decode ((code.drop before.len).take len) = some (instruction, len) ∧
      before.len + len ≤ code.length ∧ symStep asm before instruction = some next ∧
      Silmaril.X86.Decompile.SemLift.run asm code count { next with len := before.len + len } =
        some after := by
  simp only [Silmaril.X86.Decompile.SemLift.run] at checked
  split at checked
  · cases checked
  · rename_i instruction len decodedWindow
    split at checked
    · rename_i decoding
      obtain ⟨decoded, fits⟩ := decoding
      simp only [Option.bind_eq_some_iff] at checked
      obtain ⟨next, symbolicStep, rest⟩ := checked
      exact ⟨instruction, len, next, decoded, fits, symbolicStep, rest⟩
    · cases checked

/-- The actual checker run gives actual fetched-byte Features retirements,
retaining the original machine's extended fields. Loads must be backed, stores
writable and separate from code. Actual Loaded supplies image bounds; the
exact decoded spans remain explicit. -/
theorem run_sound {asm : Assume} {source : X86.State} {memory : Memory}
    (original : Silmaril.X86.Features.State)
    (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension)
    (assumptions : AssumeHolds source memory asm) {code : List Byte} {base exit : Word} :
    ∀ (count : Nat) (before after : SSt) (machine : X86.MState),
      Silmaril.X86.Decompile.SemLift.run asm code count before = some after →
      Rel source memory before machine.core machine.memory →
      machine.core.rip = base + BitVec.ofNat 64 before.len →
      Ext.Loaded memory base code →
      (∀ access ∈ after.reads, (Ext.loadN memory (access.1.eval source memory) access.2).isSome) →
      (∀ store ∈ after.stores,
        memory.Permitted .write (store.1.eval source memory).toNat store.2.1) →
      (∀ store ∈ after.stores, base.toNat + code.length ≤ (store.1.eval source memory).toNat ∨
        (store.1.eval source memory).toNat + store.2.1 ≤ base.toNat) →
      ∃ final, Silmaril.X86.Features.run featureSet extensions exit count
          (lift original machine) = some (lift original final) ∧
        Rel source memory after final.core final.memory ∧
        final.core.rip = base + BitVec.ofNat 64 after.len := by
  intro count before after machine checked related pc loaded reads writes separate
  induction count generalizing before machine with
  | zero =>
      have same : before = after := Option.some.inj checked
      cases same
      exact ⟨machine, rfl, related, pc⟩
  | succ count ih =>
      show ∃ final, Silmaril.X86.Features.run featureSet extensions exit (count + 1)
          (lift original machine) = some (lift original final) ∧
        Rel source memory after final.core final.memory ∧
        final.core.rip = base + BitVec.ofNat 64 after.len
      have decomposition : ∃ instruction len next,
          Ext.decode ((code.drop before.len).take len) = some (instruction, len) ∧
          before.len + len ≤ code.length ∧ symStep asm before instruction = some next ∧
          Silmaril.X86.Decompile.SemLift.run asm code count { next with len := before.len + len } =
            some after := run_succ_decompose checked
      obtain ⟨instruction, len, next, decoded, fits, symbolicStep, rest⟩ := decomposition
      have grows : next.Le after := SSt.Le.of_len (run_le code count _ after rest)
      have currentLoaded : Ext.Loaded machine.memory base code :=
        applyStores_loaded related.mem
          (fun store member => separate store (grows.2 store ((symStep_le symbolicStep).2 store member))) loaded
      obtain ⟨nextCore, nextMemory, executed, nextPc, nextRelated⟩ :=
        symStep_sound assumptions symbolicStep related
          (fun access member => reads access (grows.1 access member))
          (fun store member => writes store (grows.2 store member))
      have notRet : instruction ≠ .ret := by
        rintro rfl
        simp [symStep] at symbolicStep
      have integerStep : Ext.stepOpt exit machine = some ⟨nextCore, nextMemory⟩ :=
        Ext.stepOpt_of_loaded (exit := exit) currentLoaded pc fits decoded notRet executed
      have retired : Silmaril.X86.Features.step featureSet extensions exit (lift original machine) =
          .retired (lift original ⟨nextCore, nextMemory⟩) :=
        retire_of_loaded original featureSet extensions
          currentLoaded pc fits decoded (symStep_baseRequirement symbolicStep) integerStep
      have lengthEq : instruction.length = len := (Ext.decode_length decoded).1.symm
      obtain ⟨final, actualRun, finalRelated, finalPc⟩ :=
        ih { next with len := before.len + len } ⟨nextCore, nextMemory⟩ rest
        ⟨nextRelated.regs, nextRelated.mem, nextRelated.flags⟩
        (by
          show nextCore.rip = _
          rw [nextPc, pc, lengthEq, BitVec.ofNat_add, BitVec.add_assoc])
      refine ⟨final, ?_, finalRelated, finalPc⟩
      rw [Silmaril.X86.Features.run_succ,
        Silmaril.X86.Features.stepOpt_eq_some_iff.mpr retired]
      exact actualRun


/-- The real non-core Features fields are preserved by the explicit state
update. FS base belongs to the integer core and is not asserted here. -/
theorem lift_preserves_extended (original : Silmaril.X86.Features.State) (machine : X86.MState) :
    (lift original machine).state.zmm = original.zmm ∧
    (lift original machine).state.k = original.k ∧
    (lift original machine).state.mxcsr = original.mxcsr ∧
    (lift original machine).state.x87 = original.x87 := ⟨rfl, rfl, rfl, rfl⟩

/-- An accepted byte summary describes a real Features run from the same
loaded memory and RIP, with the actual summary's register/store/flag meanings. -/
theorem check_sound {code : List Byte} {count : Nat} {summary : Summary}
    (checked : check code count summary = true)
    (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension)
    {base exit : Word}
    (initial : Silmaril.X86.Features.MState)
    (loaded : Ext.Loaded initial.memory base code) (pc : initial.state.core.rip = base)
    (reads : ∀ access ∈ summary.reads,
      (Ext.loadN initial.memory (access.1.eval initial.state.core initial.memory) access.2).isSome)
    (writes : ∀ store ∈ summary.stores,
      initial.memory.Permitted .write (store.1.eval initial.state.core initial.memory).toNat store.2.1)
    (separate : ∀ store ∈ summary.stores,
      base.toNat + code.length ≤ (store.1.eval initial.state.core initial.memory).toNat ∨
        (store.1.eval initial.state.core initial.memory).toNat + store.2.1 ≤ base.toNat)
    (assumptions : AssumeHolds initial.state.core initial.memory summary.assume) :
    ∃ final : X86.MState,
      Silmaril.X86.Features.run featureSet extensions exit count initial =
        some (lift initial.state final) ∧
      final.core.rip = base + BitVec.ofNat 64 summary.len ∧
      (∀ output ∈ summary.outs,
        final.core.read output.1 = output.2.eval initial.state.core initial.memory) ∧
      applyStores initial.state.core initial.memory initial.memory summary.stores = some final.memory ∧
      summary.flags.Holds initial.state.core initial.memory final.core.flags := by
  unfold check at checked
  split at checked
  · rename_i symbolic checkedRun
    simp only [Summary.matches, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checked
    obtain ⟨⟨⟨⟨outputs, stores⟩, accesses⟩, length⟩, flags⟩ := checked
    simp only [← stores, ← accesses, ← length, ← flags] at reads writes separate ⊢
    obtain ⟨final, actualRun, related, finalPc⟩ := run_sound initial.state featureSet extensions
      assumptions count SSt.init symbolic initial.toBase checkedRun
      (Rel.init initial.state.core initial.memory) (by
        change initial.state.core.rip = base + BitVec.ofNat 64 SSt.init.len
        rw [pc]
        simp [SSt.init]) loaded
      reads writes separate
    refine ⟨final, actualRun, finalPc, fun output member => ?_, related.mem, related.flags⟩
    rw [related.regs output.1, outputs output member]
  · cases checked

end Silmaril.Machine.X86.Decompile.Features

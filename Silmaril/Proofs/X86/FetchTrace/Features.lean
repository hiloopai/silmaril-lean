module

public import Silmaril.X86.FetchTrace.Features.Defs
public import Silmaril.X86.FetchTrace.Thms
public import Silmaril.Machine.X86.Decompile.Features.Thms
@[expose] public section
namespace Silmaril.X86.FetchTrace.Features
open Silmaril Silmaril.X86
open Silmaril.Machine.X86.Decompile.Features (lift)

/-- Every fetched decoder equation, image invariant and ordinary-integer
feature dispatch is derived from the real decoded trace and independent image.
The result holds for arbitrary feature sets and extension dispatchers. -/
theorem execute {inside : Nat → Prop} {instructions : List Ext.Instr} {before after : X86.MState}
    (trace : Trace inside instructions before after) (admitted : Admitted instructions)
    (original : Silmaril.X86.Features.State) (featureSet : Silmaril.X86.Features.FeatureSet)
    (extensions : List Silmaril.X86.Features.Extension) (exit base : Word) (preceding suffix : List Byte)
    (loaded : Ext.Loaded before.memory base (preceding ++ code instructions ++ suffix))
    (pc : before.core.rip = base + BitVec.ofNat 64 preceding.length)
    (disjoint : Disjoint base (preceding ++ code instructions ++ suffix) inside) :
    Silmaril.X86.Features.run featureSet extensions exit instructions.length (lift original before) =
        some (lift original after) ∧
      Ext.Loaded after.memory base (preceding ++ code instructions ++ suffix) := by
  induction trace generalizing preceding with
  | nil state => exact ⟨rfl, loaded⟩
  | cons instruction rest before middle after notRet executed advance frame later ih =>
    show Silmaril.X86.Features.run featureSet extensions exit (instruction :: rest).length (lift original before) =
        some (lift original after) ∧
      Ext.Loaded after.memory base (preceding ++ code (instruction :: rest) ++ suffix)
    have image : preceding ++ code (instruction :: rest) ++ suffix =
        preceding ++ Ext.encode instruction ++ (code rest ++ suffix) := by
      simp only [code, List.flatMap_cons, List.append_assoc]
    have decoded : Ext.decode (((preceding ++ Ext.encode instruction ++ (code rest ++ suffix)).drop preceding.length).take
        (Ext.encode instruction).length) = some (instruction, (Ext.encode instruction).length) :=
      decode_at preceding (code rest ++ suffix) instruction
    have fits : preceding.length + (Ext.encode instruction).length ≤
        (preceding ++ code (instruction :: rest) ++ suffix).length := by
      simp only [code, List.flatMap_cons, List.length_append]
      omega
    have first : Ext.stepOpt exit before = some middle :=
      Ext.stepOpt_of_loaded loaded pc fits (by simpa only [image] using decoded) notRet executed
    have featureStep : Silmaril.X86.Features.step featureSet extensions exit (lift original before) =
        .retired (lift original middle) :=
      Silmaril.Machine.X86.Decompile.Features.retire_of_loaded original featureSet extensions loaded pc fits
        (by simpa only [image] using decoded) (admitted instruction (by simp)) first
    have nextLoaded : Ext.Loaded middle.memory base ((preceding ++ Ext.encode instruction) ++ code rest ++ suffix) := by
      simpa only [image, List.append_assoc] using loaded_after loaded frame disjoint
    have nextPc : middle.core.rip = base + BitVec.ofNat 64 (preceding ++ Ext.encode instruction).length := by
      rw [advance, pc, List.length_append, BitVec.ofNat_add, add_assoc]
      rfl
    have nextDisjoint : Disjoint base ((preceding ++ Ext.encode instruction) ++ code rest ++ suffix) inside := by
      simpa only [image, List.append_assoc] using disjoint
    have tailAdmitted : Admitted rest := fun instruction member => admitted instruction (by simp [member])
    obtain ⟨remaining, finalLoaded⟩ := ih tailAdmitted (preceding ++ Ext.encode instruction) nextLoaded nextPc nextDisjoint
    refine ⟨?_, ?_⟩
    · rw [List.length_cons, Silmaril.X86.Features.run_succ, Silmaril.X86.Features.stepOpt_eq_some_iff.mpr featureStep]
      exact remaining
    · simpa only [image, List.append_assoc] using finalLoaded

/-- An independently fetched actual RET uses the Features base dispatcher and
retains the same extended state; no Features-success premise is supplied. -/
theorem returned_of_loaded {base exit : Word} {bytes : List Byte} {before final : X86.MState}
    {offset len : Nat} (original : Silmaril.X86.Features.State)
    (featureSet : Silmaril.X86.Features.FeatureSet) (extensions : List Silmaril.X86.Features.Extension)
    (loaded : Ext.Loaded before.memory base bytes)
    (pc : before.core.rip = base + BitVec.ofNat 64 offset) (fits : offset + len ≤ bytes.length)
    (decoded : Ext.decode ((bytes.drop offset).take len) = some (.ret, len))
    (returned : Ext.step exit before = .returned final) :
    Silmaril.X86.Features.step featureSet extensions exit (lift original before) = .returned (lift original final) := by
  have fetched : Ext.fetch before.memory before.core.rip.toNat = .decoded .ret len := by
    apply Ext.fetch_eq_decoded_iff.mpr
    refine ⟨(bytes.drop offset).take len, ?_, decoded⟩
    rw [pc, loaded.toNat_add (by have := (Ext.decode_length decoded).2.1; omega)]
    exact loaded.fetchBytes_sub (Ext.decode_length decoded).2.1 fits
  have dispatched := Silmaril.X86.Features.step_of_base
    (m := lift original before) (F := featureSet) (exts := extensions) (exit := exit) fetched
  rw [dispatched]
  change Silmaril.X86.Features.Outcome.ofBase (original.setCore before.core) (Ext.step exit before) = _
  rw [returned]
  rfl

end Silmaril.X86.FetchTrace.Features

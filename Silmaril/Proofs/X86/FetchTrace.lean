module

public import Silmaril.X86.FetchTrace.Defs
@[expose] public section
namespace Silmaril.X86.FetchTrace
open Silmaril Silmaril.X86

/-- Annotated decoded traces compose at their actual intermediate state. -/
theorem Trace.append {inside : Nat → Prop} {first second : List Ext.Instr}
    {before middle after : X86.MState} (initial : Trace inside first before middle)
    (later : Trace inside second middle after) : Trace inside (first ++ second) before after := by
  induction initial with
  | nil => exact later
  | cons instruction rest before middle final notRet executed pc memory remaining ih =>
    exact .cons _ _ _ _ _ notRet executed pc memory (ih later)

/-- The image survives any proved memory frame disjoint from all code bytes. -/
theorem loaded_after {before after : Process.Memory} {base : Word} {bytes : List Byte} {inside : Nat → Prop}
    (loaded : Ext.Loaded before base bytes) (frame : before.WritesWithin after inside)
    (disjoint : Disjoint base bytes inside) : Ext.Loaded after base bytes :=
  (frame.fetchBytes disjoint).trans loaded

/-- The actual canonical decoder consumes one selected instruction at its
computed location in the complete image; decoder success is derived. -/
theorem decode_at (preceding suffix : List Byte) (instruction : Ext.Instr) :
    Ext.decode (((preceding ++ Ext.encode instruction ++ suffix).drop preceding.length).take
      (Ext.encode instruction).length) = some (instruction, (Ext.encode instruction).length) := by
  simp only [List.append_assoc, List.drop_left, List.take_left, Ext.decode_encode]

theorem Trace.pc {inside : Nat → Prop} {instructions : List Ext.Instr} {before after : X86.MState}
    (trace : Trace inside instructions before after) :
    after.core.rip = before.core.rip + BitVec.ofNat 64 (code instructions).length := by
  induction trace with
  | nil => simp [code]
  | cons instruction rest before middle after notRet executed pc memory later ih =>
    rw [ih, pc]
    simp only [code, List.flatMap_cons, List.length_append, BitVec.ofNat_add, add_assoc]
    rfl

theorem Trace.memory {inside : Nat → Prop} {instructions : List Ext.Instr} {before after : X86.MState}
    (trace : Trace inside instructions before after) : before.memory.WritesWithin after.memory inside := by
  induction trace with
  | nil => exact .refl _ _
  | cons instruction rest before middle after notRet executed pc memory later ih => exact memory.trans ih

/-- Every decoder equation and every intermediate loaded image is derived
from the canonical instruction list and per-step frames. No fetched-machine
step, run or decoder-success premise is an input to this lift. -/
theorem Trace.fetched {inside : Nat → Prop} {instructions : List Ext.Instr} {before after : X86.MState}
    (trace : Trace inside instructions before after) (exit base : Word) (preceding suffix : List Byte)
    (loaded : Ext.Loaded before.memory base (preceding ++ code instructions ++ suffix))
    (pc : before.core.rip = base + BitVec.ofNat 64 preceding.length)
    (disjoint : Disjoint base (preceding ++ code instructions ++ suffix) inside) :
    Ext.Runs exit instructions.length before after ∧
      Ext.Loaded after.memory base (preceding ++ code instructions ++ suffix) := by
  induction trace generalizing preceding with
  | nil state => exact ⟨.nil _, loaded⟩
  | cons instruction rest before middle after notRet executed advance frame later ih =>
    show Ext.Runs exit (instruction :: rest).length before after ∧
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
    have nextLoaded : Ext.Loaded middle.memory base ((preceding ++ Ext.encode instruction) ++ code rest ++ suffix) := by
      simpa only [image, List.append_assoc] using loaded_after loaded frame disjoint
    have nextPc : middle.core.rip = base + BitVec.ofNat 64 (preceding ++ Ext.encode instruction).length := by
      rw [advance, pc, List.length_append, BitVec.ofNat_add, add_assoc]
      rfl
    have nextDisjoint : Disjoint base ((preceding ++ Ext.encode instruction) ++ code rest ++ suffix) inside := by
      simpa only [image, List.append_assoc] using disjoint
    obtain ⟨remaining, finalLoaded⟩ := ih (preceding ++ Ext.encode instruction) nextLoaded nextPc nextDisjoint
    refine ⟨Ext.Runs.cons first remaining, ?_⟩
    simpa only [image, List.append_assoc] using finalLoaded

end Silmaril.X86.FetchTrace

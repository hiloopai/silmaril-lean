module

import Silmaril.Process.ImageAccess.X86.Thms

/-! Two decoded loads: the first reply determines the second address. The small
image is an ownership-scoped table of complete replies, not a filtered `Memory`. -/

namespace Silmaril.Process.ImageAccess.X86

open Silmaril.X86 (State)
open Silmaril.X86.Ext (Mem exec)

private def pointer : Read := ⟨.data, 0x2000, 4⟩
private def target : Read := ⟨.data, 0x2004, 4⟩
private def pointerBytes : List Byte := [0x04, 0x20, 0, 0]
private def valueBytes : List Byte := [0xef, 0xbe, 0xad, 0xde]

private def ownedSnapshot : Reader := fun request =>
  if request = pointer then .ok pointerBytes
  else if request = target then .ok valueBytes
  else .error .ub

private def memory : Memory :=
  ⟨[⟨0x2000, 8, ⟨true, true, false⟩⟩],
    Memory.install (Memory.install ∅ 0x2000 pointerBytes) 0x2004 valueBytes⟩

private def fullReader := (Image.full memory).localReader

private theorem full_pointer : fullReader pointer = .ok pointerBytes := by
  have bytes : memory.readBytes 0x2000 4 = some pointerBytes := by
    apply Memory.readWith_eq memory .read 0x2000 pointerBytes (by decide)
    intro index bound
    change (Memory.install _ 0x2004 valueBytes).get? (0x2000 + index) = _
    rw [Memory.install_outside _ _ _ _ (Or.inl (by change index < 4 at bound; omega))]
    exact Memory.install_get _ _ _ index bound
  change (match memory.readBytes 0x2000 4 with
    | some bytes => Except.ok bytes | none => Except.error Stop.fault) = _
  rw [bytes]

private theorem full_target : fullReader target = .ok valueBytes := by
  have bytes : memory.readBytes 0x2004 4 = some valueBytes :=
    Memory.readWith_eq memory .read 0x2004 valueBytes (by decide) (Memory.install_get _ _ _)
  change (match memory.readBytes 0x2004 4 with
    | some bytes => Except.ok bytes | none => Except.error Stop.fault) = _
  rw [bytes]

private theorem full_refines_snapshot : Reader.Refines fullReader ownedSnapshot := by
  intro request bytes answer
  by_cases first : request = pointer
  · subst request
    change Except.ok pointerBytes = .ok bytes at answer
    cases answer
    exact full_pointer
  · by_cases second : request = target
    · subst request
      change Except.ok valueBytes = .ok bytes at answer
      cases answer
      exact full_target
    · simp [ownedSnapshot, first, second] at answer

private def core : State :=
  { regs := fun reg => if reg = .rbx then 0x2000 else -1
    rip := 0x1000
    flags := ⟨some true, none, none, none, none, none⟩ }

private def pointerSource : Mem := .ofReg .rbx none 0
private def valueSource : Mem := .ofReg .rax none 0
private def readPointer := load .d .rax pointerSource core 2
private def readValue (middle : State) := load .d .rcx valueSource middle 2
private def fragment := readPointer.bind readValue
private def expected : State := { (core.write .rax 0x2004).write .rcx 0xdeadbeef with rip := 0x1004 }

private theorem snapshot_wp : fragment.wp ownedSnapshot (· = expected) := by
  apply (Program.wp_bind readPointer readValue).mpr
  exact ⟨pointerBytes, rfl, valueBytes, rfl, rfl⟩

example : fragment.run fullReader = .ok expected := by
  obtain ⟨after, run, final⟩ := (Program.wp_iff_run _).mp
    (Program.wp_transfer full_refines_snapshot fragment snapshot_wp)
  exact final ▸ run

example : ∃ middle, exec (.load .d .rax pointerSource) core memory 2 = .ok middle memory ∧
    exec (.load .d .rcx valueSource) middle memory 2 = .ok expected memory := by
  obtain ⟨middle, first, rest⟩ :=
    load_exec_of_wp full_refines_snapshot ((Program.wp_bind readPointer readValue).mp snapshot_wp)
  obtain ⟨after, second, final⟩ := load_exec_of_wp full_refines_snapshot rest
  exact ⟨middle, first, final ▸ second⟩

example : (fragment.run fun request =>
    if request = pointer then .ok pointerBytes else .error .ub) = .error .ub := rfl

#print axioms Program.wp_bind

end Silmaril.Process.ImageAccess.X86

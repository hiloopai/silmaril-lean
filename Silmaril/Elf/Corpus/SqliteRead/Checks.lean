module

import Silmaril.Elf.Corpus.SqliteRead.Thms
public meta import Silmaril.Elf.Corpus.SqliteRead.Defs
public meta import Silmaril.Machine.SqliteRead.Defs
public import Silmaril.X86.EntryState
public meta import Silmaril.X86.EntryState

namespace Silmaril.Elf.Corpus.SqliteRead

open Silmaril.Machine SqliteRead Behaviour Observable LittleEndian
open Silmaril.X86 (MState Word)
open Silmaril.X86.EntryState
open Silmaril.X86.Ext (loadN)
open Silmaril.X86.Ext.Wire (Platform)
open Silmaril.Process (Region)

set_option maxRecDepth 4096

private abbrev FixturePlacement := Silmaril.X86.EntryState.Placement

private def page : PageRead := ⟨0x500000, 0x600000, 512, 2⟩
private def methods : Word := 0x10e220
private def target : Word := 0x159b0
private def platform : Platform := ⟨fun _ _ => ⟨0, 0, 0, 0⟩⟩

private def codePlacement : FixturePlacement :=
  ⟨⟨region.base, region.bytes.length, ⟨true, false, true⟩⟩, some region.bytes⟩

private def filePlacement : FixturePlacement :=
  ⟨⟨page.file.toNat, 8, ⟨true, false, false⟩⟩, some (encodeWords [methods])⟩

private def slotPlacement : FixturePlacement :=
  ⟨⟨(methods + 16).toNat, 8, ⟨true, false, false⟩⟩, some (encodeWords [target])⟩

private def stackPlacement : FixturePlacement := ⟨⟨0x6ffff8, 8, ⟨true, true, false⟩⟩, none⟩
private def bufferPlacement : FixturePlacement := ⟨⟨page.buffer.toNat, 512, ⟨true, true, false⟩⟩, none⟩

private def placements (installed : Bool) : List FixturePlacement :=
  [codePlacement, filePlacement, stackPlacement, bufferPlacement] ++ if installed then [slotPlacement] else []

private theorem fixture_wf : WF (placements true) := by
  constructor
  · intro placement member bytes backed
    simp [placements] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> cases backed <;> rfl
  · intro placement member
    simp [placements] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp [placements, List.pairwise_cons, Region.Disjoint, codePlacement, filePlacement,
      stackPlacement, bufferPlacement, slotPlacement, region, page, methods]

private def fixture (installed : Bool) : MState :=
  ⟨⟨(fun reg => match reg with
      | .rdi => page.file
      | .rsi => page.buffer
      | .rdx => 512
      | .rcx => 2
      | .rsp => 0x700000
      | _ => 0), 0x4b10d, unknownFlags, 0⟩, memory (placements installed)⟩

private theorem fixture_entry : Entry (fixture true) page methods target := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, by decide, by decide, ?_, by decide, ?_, by decide,
    by decide, by decide, ?_, ?_, by decide⟩
  · exact fetchBytes_blob fixture_wf (placement := codePlacement) (by simp [placements]) rfl rfl (by decide)
  · have loaded := readBytes_blob fixture_wf (placement := filePlacement) (by simp [placements]) rfl rfl (by decide)
    change (fixture true).memory.readBytes page.file.toNat 8 = some (encodeWords [methods]) at loaded
    rw [loadN, loaded]
    decide +kernel
  · have loaded := readBytes_blob fixture_wf (placement := slotPlacement) (by simp [placements]) rfl rfl (by decide)
    change (fixture true).memory.readBytes (methods + 16).toNat 8 = some (encodeWords [target]) at loaded
    rw [loadN, loaded]
    decide +kernel
  · exact permitted_region fixture_wf (placement := stackPlacement) (by simp [placements]) rfl (by decide)
  · exact permitted_region fixture_wf (placement := stackPlacement) (by simp [placements]) rfl (by decide)

private def owned : Context :=
  ⟨(· = page.file), fun ptr length => ptr = page.buffer ∧ length = 512 ∧
    (fixture true).memory.Permitted .write ptr.toNat length⟩

private theorem fixture_safe : Safe ((contract owned).spec page.request) :=
  (safe_iff_admitted _ _).mpr ⟨by decide, rfl, by decide, by decide, by decide, by decide, by decide, rfl, rfl,
    permitted_region fixture_wf (placement := bufferPlacement) (by simp [placements]) rfl (by decide)⟩

example : observe (run platform 3 (fixture true)) ∈ (contract owned).spec page.request :=
  sound fixture_entry fixture_safe

#guard observe (run platform 3 (fixture true)) == ⟨[⟨0x500000, 0x600000, 512, 1024⟩], .returned .handlerEntry⟩
#guard observe (run platform 3 (fixture false)) == ⟨[], .faulted .data⟩
#guard observe (run platform 2 (fixture true)) == ⟨[], .faulted .validation⟩

example : close .forbidden ((contract owned).spec { page.request with offset := -1 }) = Set.univ :=
  ub_is_top (fun bad => (by decide : ¬ (0xffffffffffffffff + 512 < 2 ^ 63 : Prop)) bad.2.2.2.2.2.1)

private def smallRead : Request := ⟨page.file, page.buffer, 3, 1⟩
private def sentinel : BufferView := fun _ => some 0xff
private def padded : BufferView := fun addr =>
  if addr = 0x600000 then some 0xaa else if 0x600001 ≤ addr ∧ addr < 0x600003 then some 0 else sentinel addr

example : Handler [0xbb, 0xaa] smallRead sentinel padded (Status.ofCode 522) := by
  refine ⟨?_, by decide, ?_⟩
  · intro addr outside
    change addr < 0x600000 ∨ 0x600003 ≤ addr at outside
    unfold padded
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · intro index within
    change index < 3 at within
    have casesIndex : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases casesIndex with rfl | rfl | rfl <;> decide +kernel

end Silmaril.Elf.Corpus.SqliteRead

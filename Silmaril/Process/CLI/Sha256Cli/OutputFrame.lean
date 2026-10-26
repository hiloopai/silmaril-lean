module

public import Silmaril.Process.CLI.Sha256Cli.Output
public import Silmaril.X86.Ext.Store

/-! # Immutable filter code across concrete driver stores -/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.Output

open Silmaril.Process.CLI.X86Linux

set_option maxRecDepth 100000 in
/-- Every instruction in the checked transcript belongs to the executable
segment, which ends strictly below every writable driver buffer and stack. -/
theorem code_end (entry : Entry) (member : entry ∈ Binary.transcript) :
    entry.address + entry.bytes.length ≤ 0x4005c0 := by
  obtain ⟨segment, segmentMember, execute, _, upper, _⟩ := (image_faithful entry member).2
  simp only [image, Binary.image, List.mem_cons, List.not_mem_nil, or_false] at segmentMember
  rcases segmentMember with rfl | rfl
  · have size : Binary.seg0.vaddr + Binary.seg0.fileBytes.length = 0x4005c0 := by rfl
    rwa [size] at upper
  · cases execute

/-- Any concrete store above the executable segment preserves every checked
fetch. This covers the fixed buffers and the explicitly separated stack. -/
theorem intact_of_store {before after : Memory} (intact : Intact before)
    {address : Nat} {bytes : List Byte} (stored : X86.Ext.Stored before after address bytes)
    (above : 0x4005c0 ≤ address) : Intact after := by
  intro entry member
  have bound := code_end entry member
  change after.readWith .execute entry.address entry.bytes.length = some entry.bytes
  rw [stored.readWith_disjoint .execute entry.address entry.bytes.length (by omega)]
  change before.fetchBytes entry.address entry.bytes.length = some entry.bytes
  exact intact entry member

end Silmaril.Process.CLI.Sha256Cli.Output

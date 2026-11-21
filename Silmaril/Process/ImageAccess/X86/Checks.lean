module

import Silmaril.Process.ImageAccess.X86.Thms
import Silmaril.X86.Ext.Decode
meta import Silmaril.Process.ImageAccess.X86.Defs

/-! A two-request fixture: fetch a known instruction's bytes, then execute its decoded
load against three interchangeable readers. The decode check is separate. -/

namespace Silmaril.Process.ImageAccess.X86

open Silmaril.X86 (State)
open Silmaril.X86.Ext (Mem decode exec)

private def opcodes : List Byte := [0x8b, 0x03]
private def payload : List Byte := [0x78, 0x56, 0x34, 0x12]
private def code : Read := ⟨.fetch, 0x1000, 2⟩
private def operand : Read := ⟨.data, 0x2000, 4⟩
private def other : Read := ⟨.data, 0x3000, 1⟩

private def memory : Memory :=
  ⟨[⟨0x1000, 2, ⟨false, false, true⟩⟩, ⟨0x2000, 4, ⟨true, false, false⟩⟩,
      ⟨0x3000, 1, ⟨true, false, false⟩⟩],
    Memory.install (Memory.install (Memory.install ∅ 0x3000 [0xde]) 0x1000 opcodes) 0x2000 payload⟩

private def owns (request : Read) : Bool :=
  match request.kind with
  | .fetch => request.within 0x1000 2
  | .data => request.within 0x2000 4

private def sharedImage : Image Unit :=
  ⟨memory, fun request =>
    if request = operand then .delegate ()
    else if owns request then .mapped else .hidden .unavailable⟩

private def sharedReply : Unit → Reader := fun _ request =>
  if request = operand then .ok payload else .error .unavailable

private def fullReader := (Image.full memory).localReader
private def ownedReader := (Image.owned memory owns .ub).localReader
private def sharedReader := sharedImage.reader sharedReply

private theorem operand_bytes : memory.readBytes 0x2000 4 = some payload := by
  exact Memory.readWith_eq memory .read 0x2000 payload (by decide)
    (Memory.install_get _ _ _)

private theorem code_bytes : memory.fetchBytes 0x1000 2 = some opcodes := by
  apply Memory.readWith_eq memory .execute 0x1000 opcodes (by decide)
  intro index bound
  change (Memory.install _ 0x2000 payload).get? (0x1000 + index) = _
  rw [Memory.install_outside _ _ _ _ (Or.inl (by change index < 2 at bound; omega))]
  exact Memory.install_get _ _ _ index bound

private theorem full_operand : fullReader operand = .ok payload := by
  change (match memory.readBytes 0x2000 4 with
    | some bytes => Except.ok bytes | none => Except.error Stop.fault) = _
  rw [operand_bytes]

private theorem shared_refines_owned : Reader.Refines sharedReader ownedReader := by
  intro request bytes answer
  by_cases same : request = operand
  · subst request
    have good : ownedReader operand = .ok payload := by
      change fullReader operand = .ok payload
      exact full_operand
    rw [good] at answer
    cases answer
    rfl
  · cases route : owns request
    · simp [ownedReader, Image.owned, Image.localReader, Image.reader, route] at answer
    · simpa [ownedReader, sharedReader, sharedImage, Image.owned, Image.localReader,
        Image.reader, route, same] using answer

private theorem full_refines_shared : Reader.Refines fullReader sharedReader := by
  intro request bytes answer
  by_cases same : request = operand
  · subst request
    change Except.ok payload = .ok bytes at answer
    cases answer
    exact full_operand
  · cases route : owns request
    · simp [sharedReader, sharedImage, Image.reader, route, same] at answer
    · simpa [fullReader, Image.full, sharedReader, sharedImage, Image.localReader,
        Image.reader, route, same] using answer

private def core : State :=
  { regs := fun reg => if reg = .rbx then 0x2000 else -1
    rip := 0x1000
    flags := ⟨some true, none, none, none, none, none⟩ }

private def source : Mem := .ofReg .rbx none 0
private def instruction := load .d .rax source core 2
private def expected : State := { core.write .rax 0x12345678 with rip := 0x1002 }

private theorem owned_load : instruction.wp ownedReader (· = expected) := by
  exact ⟨payload, full_operand, rfl⟩

example : ∃ after, exec (.load .d .rax source) core memory 2 = .ok after memory ∧ after = expected :=
  load_exec_of_wp (full_refines_shared.trans shared_refines_owned) owned_load

example : decode opcodes = some (.load .d .rax source, 2) := by decide

example : ∃ after, (Program.read code (fun _ => instruction)).run fullReader = .ok after ∧
    after = expected := by
  apply (Program.wp_iff_run _).mp
  apply Program.wp_transfer (full_refines_shared.trans shared_refines_owned)
  refine ⟨opcodes, ?_, owned_load⟩
  change (match memory.fetchBytes 0x1000 2 with
    | some bytes => Except.ok bytes | none => Except.error Stop.fault) = _
  rw [code_bytes]

example : ownedReader other = .error .ub := rfl
example : sharedReader other = .error .unavailable := rfl
example : (Image.owned memory owns .unavailable).localReader other = .error .unavailable := rfl
example : ownedReader ⟨.data, 0x2002, 4⟩ = .error .ub := rfl
example : fullReader ⟨.data, 0x1000, 2⟩ = .error .fault := rfl
example : sharedImage.reader (fun _ _ => .ok []) operand = .error .unavailable := rfl

#guard fullReader other == .ok [0xde]
#guard match instruction.run sharedReader with
  | .ok after => after.read .rax == 0x12345678 && after.rip == 0x1002
  | .error _ => false

#print axioms Program.wp_iff_run
#print axioms Program.wp_transfer
#print axioms load_full
#print axioms load_exec_of_wp

end Silmaril.Process.ImageAccess.X86

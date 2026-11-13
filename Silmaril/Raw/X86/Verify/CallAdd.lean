module

public import Silmaril.X86.Leaf.Defs
public import Silmaril.X86.Ext.SymExec
public import Silmaril.X86.Ext.Decode
public import Silmaril.X86.EntryState

/-! # A checked direct CALL and two RETs

The selected ELF symbol is a thirteen-byte region containing a caller and its
local addition subroutine. The CALL at offset zero pushes the real continuation
address, enters the callee at offset six, and returns to offset five before the
caller's RET pops its own caller's address. No linker or external-call summary
is hidden in the contract. Arithmetic is unsigned modulo 2^64.

The proof reuses `Leaf.caller_returns` and the proved embedding into `X86.Ext`.
This remains the repository's local handwritten ISA model.
-/

@[expose] public section

namespace Silmaril.X86.Verify.CallAdd

open Silmaril.X86 (Byte Word MState Reg)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

/-- `call +1; ret; mov rax,rdi; add rax,rsi; ret`.
The function symbol's explicit extent includes its local subroutine. -/
def code : List Byte :=
  [0xE8, 1, 0, 0, 0, 0xC3, 0x48, 0x89, 0xF8, 0x48, 0x01, 0xF0, 0xC3]

def instrs : List Ext.Instr :=
  [.call 1, .ret, .mov .q (.reg .rax) .rdi, .alu .q .add (.reg .rax) .rsi, .ret]

theorem decoded : Ext.decodeAll 13 code = some instrs := by decide +kernel

/-- The caller owns an eight-byte stack slot below its incoming stack pointer.
The code and slot are disjoint and the outer return address differs from the
inner continuation, so the callee's RET is an ordinary retirement. -/
structure Entry (bytes : List Byte) (entry exit : Word) (m : MState) : Prop where
  rip : m.core.rip = entry
  image : Ext.Loaded m.memory entry bytes
  ret : m.memory.readBytes (m.core.read .rsp).toNat 8 = some (encodeWords [exit])
  slotWrite : m.memory.Permitted .write ((m.core.read .rsp).toNat - 8) 8
  slotRead : m.memory.Permitted .read ((m.core.read .rsp).toNat - 8) 8
  spLow : 8 ≤ (m.core.read .rsp).toNat
  apart : entry.toNat + 13 ≤ (m.core.read .rsp).toNat - 8 ∨
    (m.core.read .rsp).toNat ≤ entry.toNat
  exit_ne : exit ≠ entry + 5#64

def Post (before final : MState) (entry exit : Word) : Prop :=
  final.core.rip = exit ∧
    final.core.read .rax = before.core.read .rdi + before.core.read .rsi ∧
    final.core.read .rsp = before.core.read .rsp + 8#64 ∧
    (∀ r, r ≠ .rax → r ≠ .rsp → final.core.read r = before.core.read r) ∧
    Memory.WritesOnly before.memory final.memory ((before.core.read .rsp).toNat - 8) 8 ∧
    final.memory.readBytes ((before.core.read .rsp).toNat - 8) 8 =
      some (encodeWords [entry + 5#64])

/-- Finite return, modular addition, register preservation and a tight stack
frame, for every admitted argument/register/memory state. -/
def Contract (bytes : List Byte) : Prop :=
  ∀ {entry exit : Word} {m : MState}, Entry bytes entry exit m →
    ∃ final, Ext.Returns exit m final ∧ Post m final entry exit

theorem correct {bytes : List Byte} (profile : bytes = code) : Contract bytes := by
  intro entry exit m h
  subst bytes
  have hsplow := h.spLow
  have hslot : (m.core.read .rsp - 8#64).toNat = (m.core.read .rsp).toNat - 8 :=
    Ext.toNat_sub_ofNat h.spLow (by decide)
  have hleaf : (entry + 6#64).toNat = entry.toNat + 6 :=
    h.image.toNat_add (by decide : 6 < code.length)
  have admitted : Leaf.CallerEntry m entry (entry + 6#64) exit 1#32 := by
    refine ⟨h.rip, ?_, ?_, ?_, h.ret, ?_, ?_, ?_, ?_, h.exit_ne⟩
    ·
      simpa [code, Leaf.callerBytes, Insn.encode, imm32Bytes] using
        h.image.fetchBytes_sub (offset := 0) (len := 6) (by decide) (by decide)
    ·
      change entry + 5#64 + 1#64 = entry + 6#64
      rw [BitVec.add_assoc]
      rfl
    ·
      rw [hleaf]
      simpa [code, Leaf.bytes] using
        h.image.fetchBytes_sub (offset := 6) (len := 7) (by decide) (by decide)
    · rw [hslot]; exact h.slotWrite
    · rw [hslot]; exact h.slotRead
    ·
      rw [hslot]
      rcases h.apart with left | right
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    ·
      rw [hslot, hleaf]
      rcases h.apart with left | right
      · exact Or.inl left
      · exact Or.inr (by omega)
  obtain ⟨final, ⟨mid, runs, returns⟩, rip, sum, sp, _, regs, frame, slot⟩ :=
    Leaf.caller_returns admitted
  refine ⟨final, Ext.returns_of_x86 ⟨4, mid, runs, returns⟩, rip, sum, sp, regs, ?_, ?_⟩
  · rwa [hslot] at frame
  · rwa [hslot] at slot

/-- Generated modules replay the checked composition against their own byte
profile equality. The external generator has no execution role. -/
macro "certify_call_add" profile:term : tactic =>
  `(tactic| exact Silmaril.X86.Verify.CallAdd.correct $profile)

namespace Example

def codePlacement : EntryState.Placement :=
  ⟨⟨4096, 13, ⟨true, false, true⟩⟩, some code⟩

def slotPlacement : EntryState.Placement :=
  ⟨⟨8184, 8, ⟨true, true, false⟩⟩, none⟩

def returnPlacement : EntryState.Placement :=
  ⟨⟨8192, 8, ⟨true, false, false⟩⟩, some (encodeWords [12288#64])⟩

def placements : List EntryState.Placement :=
  [codePlacement, slotPlacement, returnPlacement]

theorem wf : EntryState.WF placements where
  backing_length := by
    intro placement member bytes backing
    simp only [placements, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · cases backing; decide
    · cases backing
    · cases backing; decide
  noWrap := by
    intro placement member
    simp only [placements, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  disjoint := by decide

def state (a b : Word) : MState :=
  EntryState.build
    (EntryState.sysvCore (EntryState.blankCore 4096#64) 4096#64 a b 8192#64)
    placements

theorem entry (a b : Word) : Entry code 4096#64 12288#64 (state a b) where
  rip := rfl
  image := by
    exact EntryState.fetchBytes_blob wf (placement := codePlacement)
      (by simp [placements]) rfl rfl (by decide)
  ret := by
    exact EntryState.readBytes_blob wf (placement := returnPlacement)
      (by simp [placements]) rfl rfl (by decide)
  slotWrite := by
    exact EntryState.permitted_region wf (placement := slotPlacement)
      (by simp [placements]) rfl (by decide)
  slotRead := by
    exact EntryState.permitted_region wf (placement := slotPlacement)
      (by simp [placements]) rfl (by decide)
  spLow := by change 8 ≤ (8192#64 : Word).toNat; decide
  apart := by
    change (4096#64 : Word).toNat + 13 ≤ (8192#64 : Word).toNat - 8 ∨
      (8192#64 : Word).toNat ≤ (4096#64 : Word).toNat
    decide
  exit_ne := by decide

end Example

/-- The assumptions are inhabited for every pair of 64-bit inputs. -/
theorem realizable {bytes : List Byte} (profile : bytes = code) (a b : Word) :
    ∃ entry exit m, Entry bytes entry exit m ∧ m.core.read .rdi = a ∧ m.core.read .rsi = b := by
  subst bytes
  exact ⟨4096#64, 12288#64, Example.state a b, Example.entry a b, rfl, rfl⟩

end Silmaril.X86.Verify.CallAdd

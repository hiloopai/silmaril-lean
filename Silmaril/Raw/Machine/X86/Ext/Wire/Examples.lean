module

public import Silmaril.Machine.X86.Ext.Wire.SymExec.Defs
public import Silmaril.Machine.X86.Ext.Wire.Decode.Defs

/-!
# Focused wire-codec and execution checks

Original artifact spellings below are unchanged. These are kernel-checked
facts about the local machine, not hardware execution or Jitawa soundness.
-/

@[expose] public section
namespace Silmaril.X86.Ext.Wire.Examples

open Silmaril.X86 (Byte State Word)
open Silmaril.Process (Memory)

/-- Original prefixed JNE at byte offset 0x422. -/
def prefixedJne : Decoded := ⟨.canonical (.jcc8 .ne 9), [0x3E, 0x48, 0x75, 0x09]⟩

theorem prefixedJne_decode (tail : List Byte) :
    decode (prefixedJne.bytes ++ tail) = some prefixedJne := by
  rfl

/-- Four bytes are consumed even though the canonical JNE is two bytes. -/
theorem prefixedJne_taken (platform : Platform) (s : State) (memory : Memory)
    (h : Cond.ne.eval s.flags = some true) :
    exec platform prefixedJne s memory =
      .ok { s with rip := s.rip + 4#64 + 9#64 } memory := by
  simp [exec, execWithLength, Ext.execWithLength, Ext.exec, prefixedJne, Decoded.length, h]

/-- A redundant REX before a RIP-relative load changes its effective address. -/
example : decode [0x40, 0x8B, 0x05, 0, 0, 0, 0] =
    some ⟨.canonical (.load .d .rax (Mem.ofRip 0)), [0x40, 0x8B, 0x05, 0, 0, 0, 0]⟩ := by decide

/-- Original indirect CALL; the REX.W byte remains in the return-address length. -/
example : decode [0x48, 0xFF, 0xD1] = some ⟨.callRM (.reg .rcx), [0x48, 0xFF, 0xD1]⟩ := by decide

example : decode [0x48, 0xFF, 0xA7, 0x38, 0xFF, 0xFF, 0xFF] =
    some ⟨.jmpRM (.mem (Mem.ofReg .rdi none (-200))),
      [0x48, 0xFF, 0xA7, 0x38, 0xFF, 0xFF, 0xFF]⟩ := by decide

example : decode [0x4C, 0x0F, 0x45, 0xE0] =
    some ⟨.canonical (.cmov .q .ne .r12 (.reg .rax)), [0x4C, 0x0F, 0x45, 0xE0]⟩ := by decide

example : decode [0x48, 0x87, 0xC7] = some ⟨.xchg .q .rdi .rax, [0x48, 0x87, 0xC7]⟩ := by decide

example : decode [0x41, 0xF7, 0xE0] =
    some ⟨.canonical (.mul .d (.reg .r8)), [0x41, 0xF7, 0xE0]⟩ := by decide

example : decode [0x43, 0x3A, 0x04, 0x19] =
    some ⟨.cmp8 .rax (.mem (Mem.ofReg .r9 (some ⟨.r11, 0, by decide⟩) 0)),
      [0x43, 0x3A, 0x04, 0x19]⟩ := by decide

example : decode [0x0F, 0xA2] = some ⟨.cpuid, [0x0F, 0xA2]⟩ := by decide

example : decode [0x41, 0xF7, 0xC0, 1, 0, 0, 0] =
    some ⟨.testI .d (.reg .r8) 1, [0x41, 0xF7, 0xC0, 1, 0, 0, 0]⟩ := by decide

/-- Alternate MOV direction and non-minimal displacement remain unchanged. -/
example : decode [0x48, 0x8B, 0xC7] =
    some ⟨.canonical (.mov .q (.reg .rax) .rdi), [0x48, 0x8B, 0xC7]⟩ := by decide

example : decode [0x48, 0x8B, 0x87, 0, 0, 0, 0] =
    some ⟨.canonical (.load .q .rax (Mem.ofReg .rdi none 0)), [0x48, 0x8B, 0x87, 0, 0, 0, 0]⟩ := by decide

/-- Unsupported memory XCHG, high-byte CMP and LOCK stay outside the subset. -/
example : decode [0x48, 0x87, 0x07] = none := by decide
example : decode [0x3A, 0xE0] = none := by decide
example : decode [0xF0, 0x48, 0x87, 0x07] = none := by decide
example : decode [0x41, 0x90] = none := by decide

/-- The original SHA `84 c9` and redundant prefixes retain their own lengths. -/
example : decode [0x84, 0xC9] =
    some ⟨.canonical (.test8 (.reg .rcx) .rcx), [0x84, 0xC9]⟩ := by decide
example : decode [0x40, 0x84, 0xC9] =
    some ⟨.canonical (.test8 (.reg .rcx) .rcx), [0x40, 0x84, 0xC9]⟩ := by decide
example : decode [0x3E, 0x84, 0xC9] =
    some ⟨.canonical (.test8 (.reg .rcx) .rcx), [0x3E, 0x84, 0xC9]⟩ := by decide
example : decodeLengths 2 [0x3E, 0x84, 0xC9, 0x75, 0xFC] = some [3, 2] := by decide

/-- Prefix fallback must not admit the legacy high-byte registers either. -/
example :
    decode [0x84, 0xE0] = none ∧ decode [0x84, 0xE8] = none ∧
    decode [0x84, 0xF0] = none ∧ decode [0x84, 0xF8] = none ∧
    decode [0x84, 0xC4] = none ∧ decode [0x84, 0xC5] = none ∧
    decode [0x84, 0xC6] = none ∧ decode [0x84, 0xC7] = none ∧
    decode [0x3E, 0x84, 0xE0] = none ∧ decode [0x3E, 0x84, 0xC4] = none := by decide

example : decode [0x40, 0x84, 0xE0] =
    some ⟨.canonical (.test8 (.reg .rax) .rsp), [0x40, 0x84, 0xE0]⟩ := by decide

/-- All registers and all memory survive TEST; only flags and RIP change. -/
theorem test8_preserves_registers_memory (s : State) (memory : Memory) :
    Ext.exec (.test8 (.reg .rcx) .rcx) s memory =
      .ok { s with
        rip := s.rip + 2#64
        flags := logicFlagsN ((s.read .rcx).setWidth 8 &&& (s.read .rcx).setWidth 8) } memory := by
  rfl

/-- Bit 7, not bit 31 or 63, is the sign bit. AF remains undefined; the other
status flags follow the byte result. -/
example : logicFlagsN (0x80#8) =
    ⟨some false, some false, none, some false, some true, some false⟩ := by decide

private def test8Input (value : Word) : State :=
  { regs := fun r => if r = .rcx then value else 0, rip := 0, flags := undefinedFlags }

/-- Nonzero upper bits cannot make a zero low byte nonzero. -/
example (memory : Memory) :
    (match Ext.exec (.test8 (.reg .rcx) .rcx) (test8Input 0x100) memory with
    | .ok core _ => some core.flags
    | _ => none) =
      some ⟨some false, some true, none, some true, some false, some false⟩ := by rfl

/-- Two set low-byte bits give even parity, independently of upper bits. -/
example (memory : Memory) :
    (match Ext.exec (.test8 (.reg .rcx) .rcx) (test8Input 0x10003) memory with
    | .ok core _ => some core.flags
    | _ => none) =
      some ⟨some false, some true, none, some false, some false, some false⟩ := by rfl

/-- The undefined AF does not make a condition code undefined. -/
example (s : State) (c : Cond) :
    (c.eval (logicFlagsN ((s.read .rcx).setWidth 8))).isSome :=
  eval_logicFlagsN_isSome _ c

/-- Redundant prefixes are part of the next RIP used by a memory TEST. -/
def prefixedTest8Rip : Decoded :=
  ⟨.canonical (.test8 (.mem (Mem.ofRip 0)) .rax), [0x40, 0x84, 0x05, 0, 0, 0, 0]⟩

example : decode prefixedTest8Rip.bytes = some prefixedTest8Rip := by decide
example : decode [0x3E, 0x84, 0x05, 0, 0, 0, 0] =
    some ⟨.canonical (.test8 (.mem (Mem.ofRip 0)) .rax),
      [0x3E, 0x84, 0x05, 0, 0, 0, 0]⟩ := by decide

theorem prefixedTest8Rip_exec (platform : Platform) (s : State) (memory : Memory)
    (h : loadN memory (s.rip + 7#64) 1 = some 0x80#64) :
    exec platform prefixedTest8Rip s memory =
      .ok { s with
        rip := s.rip + 7#64
        flags := logicFlagsN (0x80#8 &&& (s.read .rax).setWidth 8) } memory := by
  simp only [exec, prefixedTest8Rip, execWithLength, Ext.execWithLength, Ext.exec,
    Decoded.length, List.length_cons, List.length_nil, readNarrow]
  simp [Mem.addr, Mem.ofRip, Narrow.bytes, Narrow.bits, h, retire]

private def test8ReadOnly : Memory :=
  ⟨[⟨0x1000, 1, ⟨true, false, false⟩⟩], (∅ : Process.ByteMemory).insert 0x1000 0x80⟩

/-- A concrete readable, backed byte with no write permission. It also
witnesses the load hypothesis of `prefixedTest8Rip_exec` at RIP `0xff9`. -/
private theorem test8ReadOnly_load : loadN test8ReadOnly 0x1000 1 = some 0x80 := by
  have permitted : test8ReadOnly.checkSpan .read 0x1000 1 = true := by decide
  change (test8ReadOnly.readBytes 0x1000 1).map (fun bytes => BitVec.ofNat 64 (leValue bytes)) = _
  unfold Memory.readBytes Memory.readWith
  rw [permitted]
  simp [test8ReadOnly, Memory.readBacking, leValue]

example : loadN test8ReadOnly 0x1000 1 = some 0x80 ∧
    test8ReadOnly.checkSpan .write 0x1000 1 = false := ⟨test8ReadOnly_load, by decide⟩

/-- TEST requires read permission only; no destination store is attempted. -/
example (s : State) :
    Ext.exec (.test8 (.mem (Mem.ofRip 0)) .rax) { s with rip := 0xFFA } test8ReadOnly =
      .ok { s with
        rip := 0x1000
        flags := logicFlagsN (0x80#8 &&& (s.read .rax).setWidth 8) } test8ReadOnly := by
  simp only [Ext.exec, readNarrow]
  change retire 0x1000
    (((loadN test8ReadOnly 0x1000 1).map fun v => v.setWidth 8).map fun x =>
      ({ { s with rip := 0xFFA } with
        flags := logicFlagsN (x &&& (s.read .rax).setWidth 8) }, test8ReadOnly)) = _
  rw [test8ReadOnly_load]
  rfl

/-- An unreadable (or unbacked) operand faults rather than guessing flags. -/
example (s : State) (memory : Memory)
    (h : loadN memory (s.rip + 6#64) 1 = none) :
    Ext.exec (.test8 (.mem (Mem.ofRip 0)) .rax) s memory = .dataFault := by
  have length : (Instr.test8 (.mem (Mem.ofRip 0)) .rax).length = 6 := by rfl
  simp only [Ext.exec, length, readNarrow]
  simp [Mem.addr, Mem.ofRip, Narrow.bytes, Narrow.bits, h, retire]

/-- Byte-immediate CMP retains both the immediate and redundant prefixes. -/
example : decode [0x80, 0xF9, 0x5C] =
    some ⟨.canonical (.cmpI8 (.reg .rcx) 0x5C), [0x80, 0xF9, 0x5C]⟩ := by decide
example : decode [0x3C, 0x09] = some ⟨.canonical (.cmpA8 0x09), [0x3C, 0x09]⟩ := by decide
example : decode [0x3E, 0x80, 0xF9, 0x80] =
    some ⟨.canonical (.cmpI8 (.reg .rcx) 0x80), [0x3E, 0x80, 0xF9, 0x80]⟩ := by decide
example : decode [0x40, 0x3C, 0x5B] =
    some ⟨.canonical (.cmpA8 0x5B), [0x40, 0x3C, 0x5B]⟩ := by decide
example : decode [0x3E, 0x80, 0xC1, 0x5C] = none ∧
    decode [0x3E, 0x80, 0xFC, 0x5C] = none := by decide

/-- Both forms preserve all registers and memory; only RIP and flags change. -/
example (s : State) (memory : Memory) (imm : BitVec 8) :
    Ext.exec (.cmpI8 (.reg .rcx) imm) s memory =
      .ok { s with
        rip := s.rip + 3#64
        flags := subFlagsN ((s.read .rcx).setWidth 8) imm } memory := by rfl
example (s : State) (memory : Memory) (imm : BitVec 8) :
    Ext.exec (.cmpA8 imm) s memory =
      .ok { s with
        rip := s.rip + 2#64
        flags := subFlagsN ((s.read .rax).setWidth 8) imm } memory := by rfl

/-- Width-sensitive signed overflow, borrow, adjust, parity and zero controls. -/
example :
    subFlagsN (0x80#8) 1 = ⟨some false, some false, some true, some false, some false, some true⟩ ∧
    subFlagsN (0#8) 1 = ⟨some true, some true, some true, some false, some true, some false⟩ ∧
    subFlagsN (0#8) 0x80 = ⟨some true, some false, some false, some false, some true, some true⟩ ∧
    subFlagsN (0#8) 0 = ⟨some false, some true, some false, some true, some false, some false⟩ := by decide

/-- Upper register bits do not participate in byte comparison. -/
example (memory : Memory) :
    (match Ext.exec (.cmpI8 (.reg .rcx) 1) (test8Input 0x100) memory with
    | .ok core _ => some core.flags
    | _ => none) =
      some ⟨some true, some true, some true, some false, some true, some false⟩ := by rfl
example (memory : Memory) :
    (match Ext.exec (.cmpA8 0x80)
        { regs := fun _ => 0x100, rip := 0, flags := undefinedFlags } memory with
    | .ok core _ => some core.flags
    | _ => none) =
      some ⟨some true, some false, some false, some false, some true, some true⟩ := by rfl

/-- The immediate is included in the consumed next RIP, as is a DS prefix. -/
private def prefixedCmpI8Rip : Decoded :=
  ⟨.canonical (.cmpI8 (.mem (Mem.ofRip 0)) 1), [0x3E, 0x80, 0x3D, 0, 0, 0, 0, 1]⟩

example : decode prefixedCmpI8Rip.bytes = some prefixedCmpI8Rip := by decide
example (platform : Platform) (s : State) (memory : Memory)
    (h : loadN memory (s.rip + 8#64) 1 = some 0x80#64) :
    exec platform prefixedCmpI8Rip s memory =
      .ok { s with rip := s.rip + 8#64, flags := subFlagsN (0x80#8) 1 } memory := by
  simp only [exec, prefixedCmpI8Rip, execWithLength, Ext.execWithLength, Ext.exec,
    Decoded.length, List.length_cons, List.length_nil, readNarrow]
  simp [Mem.addr, Mem.ofRip, Narrow.bytes, Narrow.bits, h, retire]

/-- Read-only memory is enough for CMP; the byte and all registers survive. -/
example (s : State) :
    Ext.exec (.cmpI8 (.mem (Mem.ofRip 0)) 1) { s with rip := 0xFF9 } test8ReadOnly =
      .ok { s with rip := 0x1000, flags := subFlagsN (0x80#8) 1 } test8ReadOnly := by
  simp only [Ext.exec, readNarrow]
  change retire 0x1000
    (((loadN test8ReadOnly 0x1000 1).map fun v => v.setWidth 8).map fun x =>
      ({ { s with rip := 0xFF9 } with flags := subFlagsN x 1 }, test8ReadOnly)) = _
  rw [test8ReadOnly_load]
  rfl

example (s : State) (memory : Memory)
    (h : loadN memory (s.rip + 7#64) 1 = none) :
    Ext.exec (.cmpI8 (.mem (Mem.ofRip 0)) 1) s memory = .dataFault := by
  have length : (Instr.cmpI8 (.mem (Mem.ofRip 0)) 1).length = 7 := by rfl
  simp only [Ext.exec, length, readNarrow]
  simp [Mem.addr, Mem.ofRip, Narrow.bytes, Narrow.bits, h, retire]

/-- Canonical CMOV reuses the established wire semantics, including 32-bit
zero-extension when its condition is false. Flags and memory are unchanged. -/
example (platform : Platform) (c : Cond) (dst src : X86.Reg) (length : Nat)
    (s : State) (memory : Memory) (h : c.eval s.flags = some false) :
    Ext.execWithLength (.cmov .d c dst (.reg src)) length s memory =
      .ok { Sz.d.write s dst (Sz.d.read s dst) with
        rip := s.rip + BitVec.ofNat 64 length } memory := by
  exact cmov_d_false platform c dst src length s memory h

private def cmovInput (carry : Option Bool) : State :=
  { regs := fun r => if r = .rax then 0xFEEDFACE12345678 else
      if r = .rcx then 0xFEDCBA9876543210 else 0
    rip := 0
    flags := { undefinedFlags with carry := carry } }

/-- The three AE outcomes have explicit satisfiable flag witnesses. -/
example : Cond.ae.eval (cmovInput (some false)).flags = some true ∧
    Cond.ae.eval (cmovInput (some true)).flags = some false ∧
    Cond.ae.eval (cmovInput none).flags = none := by decide
example (memory : Memory) :
    (match Ext.exec (.cmov .d .ae .rax (.reg .rcx)) (cmovInput (some true)) memory with
    | .ok core _ => some (core.read .rax, core.flags)
    | _ => none) = some (0x12345678#64, (cmovInput (some true)).flags) := by rfl
example (memory : Memory) :
    (match Ext.exec (.cmov .d .ae .rax (.reg .rcx)) (cmovInput (some false)) memory with
    | .ok core _ => some (core.read .rax, core.flags)
    | _ => none) = some (0x76543210#64, (cmovInput (some false)).flags) := by rfl
example (memory : Memory) :
    (match Ext.exec (.cmov .q .ae .rax (.reg .rcx)) (cmovInput (some true)) memory with
    | .ok core _ => some (core.read .rax, core.flags)
    | _ => none) = some (0xFEEDFACE12345678#64, (cmovInput (some true)).flags) := by rfl
example (memory : Memory) :
    Ext.exec (.cmov .q .ae .rax (.reg .rcx)) (cmovInput none) memory =
      .undefinedCondition .ae := by rfl

private def cmovUnmapped : Memory := ⟨[], ∅⟩

/-- A false condition cannot suppress an unconditionally attempted source read. -/
example (platform : Platform) :
    Ext.execWithLength (.cmov .q .ae .rax (.mem (Mem.ofRip 0))) 7
      (cmovInput (some true)) cmovUnmapped = .dataFault := by
  apply cmov_dataFault platform
  have noBytes : (List.range 8).all (fun _ => false) = false := by decide
  simp [readRM, loadN, cmovUnmapped, Memory.readBytes, Memory.readWith,
    Memory.checkSpan, Memory.permits, Sz.bytes, noBytes]

/-- A redundant DS prefix changes the RIP-relative source address to next+8. -/
private def prefixedCmovRip : Decoded :=
  ⟨.canonical (.cmov .d .ae .rax (.mem (Mem.ofRip 0))),
    [0x3E, 0x0F, 0x43, 0x05, 0, 0, 0, 0]⟩

example : decode prefixedCmovRip.bytes = some prefixedCmovRip := by decide
private theorem prefixedCmovRip_exec (platform : Platform) (s : State) (memory : Memory)
    (read : loadN memory (s.rip + 8#64) 4 = some 0x76543210#64)
    (taken : Cond.ae.eval s.flags = some true) :
    exec platform prefixedCmovRip s memory =
      .ok { Sz.d.write s .rax 0x76543210 with rip := s.rip + 8#64 } memory := by
  simp only [exec, prefixedCmovRip, execWithLength, Ext.execWithLength, Ext.exec,
    Decoded.length, List.length_cons, List.length_nil, readRM]
  simp [Mem.addr, Mem.ofRip, Sz.bytes, read, taken, retire]

private def cmovReadOnly : Memory :=
  ⟨[⟨0x1000, 4, ⟨true, false, false⟩⟩],
    Memory.install ∅ 0x1000 [0x10, 0x32, 0x54, 0x76]⟩

/-- The prefixed dword-read hypothesis is satisfiable by read-only memory. -/
private theorem cmovReadOnly_load : loadN cmovReadOnly 0x1000 4 = some 0x76543210 := by
  have permitted : cmovReadOnly.checkSpan .read 0x1000 4 = true := by decide
  change (cmovReadOnly.readBytes 0x1000 4).map (fun bytes => BitVec.ofNat 64 (leValue bytes)) = _
  unfold Memory.readBytes Memory.readWith
  rw [permitted]
  simp [cmovReadOnly, Memory.readBacking, Memory.install, leValue, Std.ExtHashMap.getElem_insert]

example (platform : Platform) :
    exec platform prefixedCmovRip { cmovInput (some false) with rip := 0xFF8 } cmovReadOnly =
      .ok { Sz.d.write { cmovInput (some false) with rip := 0xFF8 } .rax 0x76543210 with
        rip := 0x1000 } cmovReadOnly := by
  apply prefixedCmovRip_exec
  · exact cmovReadOnly_load
  · rfl

/-- Undefined conditions are not replaced by a branch choice. -/
example (platform : Platform) (s : State) (memory : Memory)
    (h : Cond.ne.eval s.flags = none) :
    execWithLength platform (.cmov .d .ne .rax (.reg .rbx)) 3 s memory =
      .undefinedCondition .ne := by
  simp [execWithLength, Ext.execWithLength, Ext.exec, readRM, h]

/-- The original prefixed branch executes from checked code memory and retires
at base + 13, rather than the base + 11 of a canonicalized two-byte branch. -/
theorem prefixedJne_fetched {platform : Platform} {base exit : Word} {m : X86.MState}
    (loaded : Loaded m.memory base prefixedJne.bytes) (at_base : m.core.rip = base)
    (taken : Cond.ne.eval m.core.flags = some true) :
    stepOpt platform exit m = some ⟨{ m.core with rip := base + 4#64 + 9#64 }, m.memory⟩ := by
  apply stepOpt_of_loaded (offset := 0) (d := prefixedJne) loaded
  · simpa using at_base
  · decide
  · exact prefixedJne_decode []
  · decide
  · simpa [at_base] using prefixedJne_taken platform m.core m.memory taken

private def multiplyInput : State :=
  { regs := fun r => if r = .rax then 0xDEADBEEFFFFFFFFF else
      if r = .rdx then 0xABCDEF1200000003 else if r = .r8 then 0xFACE000000000002 else 0,
    rip := 0, flags := undefinedFlags }

/-- Original MUL32 gives EDX:EAX = 00000001:FFFFFFFE, zero-extending both
registers and preserving undefined status for SF/ZF/AF/PF. -/
example (platform : Platform) (memory : Memory) :
    (match execWithLength platform (.mul .d (.reg .r8)) 3 multiplyInput memory with
    | .ok core _ => some (core.read .rax, core.read .rdx, core.flags)
    | _ => none) = some (0xFFFFFFFE#64, 1#64, mulFlags true) := by rfl

/-- Canonical MUL32 zero-extends both outputs while preserving memory and
every register other than RAX/RDX, including upper bits of the source. -/
example (memory : Memory) : Ext.exec (.mul .d (.reg .r8)) multiplyInput memory =
    .ok { Sz.d.write (Sz.d.write multiplyInput .rax 0xFFFFFFFE) .rdx 1 with
      rip := 3, flags := Ext.mulFlags true } memory := by rfl

/-- Only CF/OF are defined, even when the complete product is zero. -/
example : Ext.mulFlags true = ⟨some true, none, none, none, none, some true⟩ ∧
    Ext.mulFlags false = ⟨some false, none, none, none, none, some false⟩ := by decide

private def multiplyAliasInput : State :=
  { regs := fun r => if r = .rax then 3 else if r = .rdx then 7 else
      if r = .r8 then 11 else 0, rip := 0, flags := undefinedFlags }

/-- RAX and RDX aliases are sampled before either implicit output is written. -/
example (memory : Memory) :
    (match Ext.exec (.mul .q (.reg .rax)) multiplyAliasInput memory with
    | .ok core _ => some (core.read .rax, core.read .rdx, core.flags)
    | _ => none) = some (9#64, 0#64, Ext.mulFlags false) := by rfl
example (memory : Memory) :
    (match Ext.exec (.mul .q (.reg .rdx)) multiplyAliasInput memory with
    | .ok core _ => some (core.read .rax, core.read .rdx, core.flags)
    | _ => none) = some (21#64, 0#64, Ext.mulFlags false) := by rfl
example (memory : Memory) :
    (match Ext.exec (.mul .q (.reg .rbx)) multiplyAliasInput memory with
    | .ok core _ => some (core.read .rax, core.read .rdx, core.flags)
    | _ => none) = some (0#64, 0#64, Ext.mulFlags false) := by rfl
example (memory : Memory) :
    (match Ext.exec (.mul .q (.reg .rdi))
        { multiplyAliasInput with regs := fun r =>
            if r = .rax then 0xFFFFFFFFFFFFFFFF else if r = .rdi then 2 else 0 } memory with
    | .ok core _ => some (core.read .rax, core.read .rdx, core.flags)
    | _ => none) = some (0xFFFFFFFFFFFFFFFE#64, 1#64, Ext.mulFlags true) := by rfl

private def prefixedMulRip : Decoded :=
  ⟨.canonical (.mul .d (.mem (Mem.ofRip 0))), [0x3E, 0xF7, 0x25, 0, 0, 0, 0]⟩

/-- The DS prefix counts toward the source address, and MUL accepts read-only
memory. The earlier dword fixture witnesses the source value and permission. -/
example : decode prefixedMulRip.bytes = some prefixedMulRip := by decide
example (platform : Platform) :
    exec platform prefixedMulRip { multiplyAliasInput with rip := 0xFF9 } cmovReadOnly =
      .ok { Sz.d.write (Sz.d.write { multiplyAliasInput with rip := 0xFF9 }
          .rax 0x62FC9630) .rdx 1 with rip := 0x1000, flags := Ext.mulFlags true } cmovReadOnly := by
  have read : readRM .d (.mem (Mem.ofRip 0))
      { multiplyAliasInput with rip := 0xFF9 } cmovReadOnly 0x1000 = some 0x76543210 := by
    change (loadN cmovReadOnly 0x1000 4).map (fun v => v.setWidth 32) = _
    rw [cmovReadOnly_load]
    rfl
  simp only [exec, prefixedMulRip, execWithLength, Ext.execWithLength, Ext.exec,
    Decoded.length, List.length_cons, List.length_nil]
  erw [read]
  rfl

example (s : State) (memory : Memory)
    (h : readRM .q (.mem (Mem.ofRip 0)) s memory (s.rip + 7#64) = none) :
    Ext.exec (.mul .q (.mem (Mem.ofRip 0))) s memory = .dataFault := by
  change Ext.exec (.mul .q (.mem (Mem.ofRip 0))) s memory 7 = .dataFault
  simp only [Ext.exec]
  rw [h]

/-- Original byte-immediate TEST and redundant accumulator prefix retain bytes. -/
example : decode [0x41, 0xF6, 0xC4, 1] =
    some ⟨.canonical (.testI8 (.reg .r12) 1), [0x41, 0xF6, 0xC4, 1]⟩ := by decide
example : decode [0x40, 0xA8, 0x80] =
    some ⟨.canonical (.testA8 0x80), [0x40, 0xA8, 0x80]⟩ := by decide
example : decode [0x3E, 0xF6, 0xC4, 1] = none ∧
    decode [0x3E, 0xF6, 0xC8, 1] = none := by decide

/-- Both forms leave every register bit and all memory unchanged. -/
example (s : State) (memory : Memory) (imm : BitVec 8) :
    Ext.exec (.testI8 (.reg .rcx) imm) s memory =
      .ok { s with
        rip := s.rip + 3#64
        flags := logicFlagsN ((s.read .rcx).setWidth 8 &&& imm) } memory := by rfl
example (s : State) (memory : Memory) (imm : BitVec 8) :
    Ext.exec (.testA8 imm) s memory =
      .ok { s with
        rip := s.rip + 2#64
        flags := logicFlagsN ((s.read .rax).setWidth 8 &&& imm) } memory := by rfl

/-- A zero low byte ignores nonzero upper bits; two low bits give even parity. -/
example (memory : Memory) :
    (match Ext.exec (.testI8 (.reg .rcx) 0xFF) (test8Input 0x100) memory with
    | .ok core _ => some core.flags
    | _ => none) =
      some ⟨some false, some true, none, some true, some false, some false⟩ := by rfl
example (memory : Memory) :
    (match Ext.exec (.testI8 (.reg .rcx) 0xFF) (test8Input 0x10003) memory with
    | .ok core _ => some core.flags
    | _ => none) =
      some ⟨some false, some true, none, some false, some false, some false⟩ := by rfl

/-- SF uses bit 7; undefined AF does not make any branch condition undefined. -/
example (memory : Memory) :
    (match Ext.exec (.testA8 0x80)
        { regs := fun _ => 0x180, rip := 0, flags := undefinedFlags } memory with
    | .ok core _ => some core.flags
    | _ => none) =
      some ⟨some false, some false, none, some false, some true, some false⟩ := by rfl
example (s : State) (imm : BitVec 8) (c : Cond) :
    (c.eval (logicFlagsN ((s.read .rax).setWidth 8 &&& imm))).isSome :=
  eval_logicFlagsN_isSome _ c

private def prefixedTestI8Rip : Decoded :=
  ⟨.canonical (.testI8 (.mem (Mem.ofRip 0)) 0x80), [0x3E, 0xF6, 0x05, 0, 0, 0, 0, 0x80]⟩

/-- The immediate and DS prefix count toward next RIP; the readonly byte
fixture supplies a concrete backed source without write permission. -/
example : decode prefixedTestI8Rip.bytes = some prefixedTestI8Rip := by decide
example (platform : Platform) (s : State) :
    exec platform prefixedTestI8Rip { s with rip := 0xFF8 } test8ReadOnly =
      .ok { s with
        rip := 0x1000
        flags := logicFlagsN (0x80#8) } test8ReadOnly := by
  have read : readNarrow .b (.mem (Mem.ofRip 0)) { s with rip := 0xFF8 }
      test8ReadOnly 0x1000 = some 0x80 := by
    change (loadN test8ReadOnly 0x1000 1).map (fun v => v.setWidth 8) = _
    rw [test8ReadOnly_load]
    rfl
  simp only [exec, prefixedTestI8Rip, execWithLength, Ext.execWithLength, Ext.exec,
    Decoded.length, List.length_cons, List.length_nil]
  erw [read]
  rfl

example (s : State) (memory : Memory)
    (h : readNarrow .b (.mem (Mem.ofRip 0)) s memory (s.rip + 7#64) = none) :
    Ext.exec (.testI8 (.mem (Mem.ofRip 0)) 0x80) s memory = .dataFault := by
  change Ext.exec (.testI8 (.mem (Mem.ofRip 0)) 0x80) s memory 7 = .dataFault
  simp only [Ext.exec]
  rw [h]
  rfl

/-- CPUID writes all four platform outputs, not an arbitrary no-op. -/
example (platform : Platform) (s : State) :
    let reply := platform.cpuid (Sz.d.read s .rax) (Sz.d.read s .rcx)
    (cpuidState platform s).read .rax = reply.eax.setWidth 64 ∧
    (cpuidState platform s).read .rbx = reply.ebx.setWidth 64 ∧
    (cpuidState platform s).read .rcx = reply.ecx.setWidth 64 ∧
    (cpuidState platform s).read .rdx = reply.edx.setWidth 64 := by
  simp [cpuidState, Sz.write]

end Silmaril.X86.Ext.Wire.Examples

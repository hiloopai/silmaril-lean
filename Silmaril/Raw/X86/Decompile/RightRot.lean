module

public import Silmaril.X86.Bench.Objects.RightRotClangO0.Defs
public import Silmaril.X86.CallingConvention
public import Silmaril.X86.Decompile.Cert
/-!
# `right_rot`, decompiled into logic

The worked example for `Silmaril/X86/Decompile/Cert.lean`. `right_rot` is

```c
uint32_t right_rot(uint32_t value, unsigned int count) {
  return value >> count | value << (32 - count);   /* 0 < count < 32 */
}
```

(`xcompile/src/sha256/sha-256.c:16-22`), compiled by `clang -O0` for
`x86_64-linux-gnu`. Its 37 bytes are at `.text` offset `0xc90` of the pinned
`sha256.o` that `Silmaril.X86.Bench.Objects.RightRotClangO0` ingests, and
`code_eq_functionBytes` checks that the `code` below is byte-for-byte what
`Silmaril.Formats.ELF`'s reader selected for the `right_rot` symbol — the bytes
are *ingested*, not typed in.

```
c90: push   %rbp                  55
c91: mov    %rsp,%rbp             48 89 e5
c94: mov    %edi,-0x4(%rbp)       89 7d fc
c97: mov    %esi,-0x8(%rbp)       89 75 f8
c9a: mov    -0x4(%rbp),%eax       8b 45 fc
c9d: mov    -0x8(%rbp),%ecx       8b 4d f8
ca0: shr    %cl,%eax              d3 e8
ca2: mov    -0x4(%rbp),%edx       8b 55 fc
ca5: mov    $0x20,%ecx            b9 20 00 00 00
caa: sub    -0x8(%rbp),%ecx       2b 4d f8
cad: shl    %cl,%edx              d3 e2
caf: mov    %edx,%ecx             89 d1
cb1: or     %ecx,%eax             09 c8
cb3: pop    %rbp                  5d
cb4: ret                          c3
```

## What is proved

`rightRotSpec` is the decompiled function: a plain Lean function on
`BitVec 32`, with no `State`, no `Memory` and no `exec` anywhere in it.
`right_rot_returns` is the certificate: from any ABI-conformant System V entry
state, the real machine (`Ext.step`, through `Ext.Returns`) returns to the
caller with `eax = rightRotSpec value count`, `rsp` popped past the return
address, every `sysv64` callee-saved register restored — `rbp` is saved and
restored by the prologue and epilogue, the other five are never touched — and
memory changed only in the sixteen frame bytes below the entry `rsp`.
`decompiled` packages it as a `Decompile.Decompiled`.

## This is a `-O0` function, and that is the point

`clang -O0` spills both arguments to the frame and reloads them, so the proof
has to carry real memory reasoning: a `push` and three stores, then four loads
that must read back what was stored, all while the code itself stays fetchable.
That is exactly the bookkeeping `Cert.lean`'s `Image.of_writesOnly`,
`loadN_storeN` and `loadN_storeN_disjoint` exist to handle, and it is the
reason an `-O0` leaf is a more honest first benchmark than an `-O2` one.

## Red zone

`right_rot` is a leaf that never adjusts `rsp` beyond its own `push`. Of the
sixteen frame bytes it touches, the top eight hold the saved `rbp` (at the
post-push `rsp`) and the bottom eight are System V red zone — `sysv64.redZone`
is 128, so eight is well inside. `Entry` asks for exactly those sixteen bytes
and `Post` promises to change no others.

Everything here is a statement about the handwritten local model of
`Silmaril/X86/Ext`; it is not evidence about hardware.
-/

@[expose] public section

namespace Silmaril.X86.Decompile.RightRot

open Silmaril.X86 (Byte Word State MState Reg AluOp)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

/-! ## The decompiled function -/

/-- **The decompilation of `right_rot`.** A plain Lean function: no machine
state, no memory, no `exec`. Every later fact about this machine code is a fact
about this function. -/
def rightRotSpec (value : BitVec 32) (count : Nat) : BitVec 32 :=
  value >>> count ||| value <<< (32 - count)

/-- The decompiled function is literally what the two shift instructions
compute, OR-ed: `ShiftOp.shr.result` at the count, then `ShiftOp.shl.result` at
`32 - count`. This is the bridge the certificate crosses. -/
theorem rightRotSpec_eq_shifts (value : BitVec 32) (count : Nat) :
    rightRotSpec value count =
      ShiftOp.shr.result value count ||| ShiftOp.shl.result value (32 - count) := rfl

/-! ## The code -/

/-- `[rbp + disp]`, the only addressing mode this function uses. -/
def frame (disp : BitVec 32) : Mem := Mem.ofReg .rbp none disp

/-- The 37 bytes of `right_rot`. -/
def code : List Byte :=
  [0x55, 0x48, 0x89, 0xE5, 0x89, 0x7D, 0xFC, 0x89, 0x75, 0xF8, 0x8B, 0x45, 0xFC,
   0x8B, 0x4D, 0xF8, 0xD3, 0xE8, 0x8B, 0x55, 0xFC, 0xB9, 0x20, 0x00, 0x00, 0x00,
   0x2B, 0x4D, 0xF8, 0xD3, 0xE2, 0x89, 0xD1, 0x09, 0xC8, 0x5D, 0xC3]

/-- These are exactly the bytes `ObjectFile.symbolData` selected for the
`right_rot` symbol of the pinned object: the code is ingested, not typed in. -/
theorem code_eq_functionBytes :
    code = Bench.Objects.RightRotClangO0.functionBytes.toList := by decide

/-- The decompiler's reading of `code`: fifteen instructions, left to right
down the disassembly. -/
def instrs : List Ext.Instr :=
  [.push .rbp,
   .mov .q (.reg .rbp) .rsp,
   .mov .d (.mem (frame 0xFFFFFFFC)) .rdi,
   .mov .d (.mem (frame 0xFFFFFFF8)) .rsi,
   .load .d .rax (frame 0xFFFFFFFC),
   .load .d .rcx (frame 0xFFFFFFF8),
   .shift .d .shr (.reg .rax) .cl,
   .load .d .rdx (frame 0xFFFFFFFC),
   .movI32 .rcx 0x20,
   .aluR .d .sub .rcx (.mem (frame 0xFFFFFFF8)),
   .shift .d .shl (.reg .rdx) .cl,
   .mov .d (.reg .rcx) .rdx,
   .alu .d .or (.reg .rax) .rcx,
   .pop .rbp,
   .ret]

/-- The model's decoder reads `code` as exactly `instrs`. -/
theorem code_decodeAll : decodeAll 37 code = some instrs := by decide

/-- The per-instruction lengths, which a reader can check against the
disassembly, and whose sum is the 37 bytes `readelf` reports for the symbol. -/
theorem code_decodeLengths :
    decodeLengths 37 code = some [1, 3, 3, 3, 3, 3, 2, 3, 5, 3, 2, 2, 2, 1, 1] := by decide

/-- Every byte belongs to one instruction, and each is spelled the way `encode`
spells it (`Ext.Covered`). -/
theorem code_covered : Covered code := covered_of_decodeAll code_decodeAll

/-! ## ABI-conformant entry -/

/-- **An ABI-conformant System V entry state** for `right_rot` at `entry`,
whose return address is `exit`.

Reading it against `Silmaril.X86.sysv64`:

* `rip = entry` and the function's 37 bytes are fetchable there;
* `returnAddress = .onStack 0`: `exit` is the eight bytes at `[rsp]`;
* the frame is the sixteen bytes below `rsp` — eight for the pushed `rbp` and
  eight of the 128-byte `redZone`, which a leaf may use without adjusting
  `rsp`;
* `intArgRegs = [rdi, rsi, …]`: `value` is `edi` and `count` is `esi`;
* `0 < count < 32` is the C source's own domain condition, not an ABI one.

The stack frame must not overlap the code, and `rsp` must be at least 16, so
that the frame does not wrap around zero. -/
structure Entry (entry exit : Word) (m : MState) : Prop where
  /-- RIP is at the function's first byte. -/
  rip : m.core.rip = entry
  /-- The 37 bytes are fetchable at `entry`. -/
  image : Image code entry m.memory
  /-- `sysv64.returnAddress = .onStack 0`: the return address is at `[rsp]`. -/
  ret : m.memory.readBytes (m.core.read .rsp).toNat 8 = some (encodeWords [exit])
  /-- The sixteen frame bytes are writable. -/
  frameWrite : m.memory.Permitted .write ((m.core.read .rsp).toNat - 16) 16
  /-- …and readable. -/
  frameRead : m.memory.Permitted .read ((m.core.read .rsp).toNat - 16) 16
  /-- The frame does not wrap around zero. -/
  spLow : 16 ≤ (m.core.read .rsp).toNat
  /-- The frame does not overlap the code. -/
  apart : entry.toNat + 37 ≤ (m.core.read .rsp).toNat - 16 ∨
    (m.core.read .rsp).toNat ≤ entry.toNat
  /-- `right_rot`'s C source is valid for `0 < count` only. -/
  countPos : 0 < (Sz.d.read m.core .rsi).toNat
  /-- …and for `count < 32` only. -/
  countLt : (Sz.d.read m.core .rsi).toNat < 32

/-- The System V integer arguments: `value` in `edi`, `count` in `esi`. -/
def args (m : MState) : BitVec 32 × Nat :=
  (Sz.d.read m.core .rdi, (Sz.d.read m.core .rsi).toNat)

/-- **The System V postcondition.** The result in `eax`; `rsp` popped past the
return address (`linkSize = 8`); every `calleeSaved` register restored; and
memory changed only in the sixteen frame bytes. -/
def Post (result : BitVec 32) (m final : MState) : Prop :=
  Sz.d.read final.core .rax = result ∧
    final.core.read .rsp = m.core.read .rsp + 8#64 ∧
    (∀ r ∈ X86.sysv64.calleeSaved, final.core.read r = m.core.read r) ∧
    Memory.WritesOnly m.memory final.memory ((m.core.read .rsp).toNat - 16) 16

/-! ## The certificate -/

/-! ### Instruction lengths

Each instruction's encoded length, as a numeral, so that the RIP arithmetic in
the certificate is ordinary `Nat` arithmetic. Each is `decide` over `encode`. -/

theorem L0 : (X86.Insn.push Reg.rbp).length = 1 := by decide
theorem L1 : (Ext.Instr.mov .q (.reg Reg.rbp) Reg.rsp).length = 3 := by decide
theorem L2 : (Ext.Instr.mov .d (.mem (frame 0xFFFFFFFC)) Reg.rdi).length = 3 := by decide
theorem L3 : (Ext.Instr.mov .d (.mem (frame 0xFFFFFFF8)) Reg.rsi).length = 3 := by decide
theorem L4 : (Ext.Instr.load .d Reg.rax (frame 0xFFFFFFFC)).length = 3 := by decide
theorem L5 : (Ext.Instr.load .d Reg.rcx (frame 0xFFFFFFF8)).length = 3 := by decide
theorem L6 : (Ext.Instr.shift .d .shr (.reg Reg.rax) .cl).length = 2 := by decide
theorem L7 : (Ext.Instr.load .d Reg.rdx (frame 0xFFFFFFFC)).length = 3 := by decide
theorem L8 : (Ext.Instr.movI32 Reg.rcx 0x20).length = 5 := by decide
theorem L9 : (Ext.Instr.aluR .d .sub Reg.rcx (.mem (frame 0xFFFFFFF8))).length = 3 := by decide
theorem L10 : (Ext.Instr.shift .d .shl (.reg Reg.rdx) .cl).length = 2 := by decide
theorem L11 : (Ext.Instr.mov .d (.reg Reg.rcx) Reg.rdx).length = 2 := by decide
theorem L12 : (Ext.Instr.alu .d .or (.reg Reg.rax) Reg.rcx).length = 2 := by decide
theorem L13 : (X86.Insn.pop Reg.rbp).length = 1 := by decide

/-- Popping the saved `rbp` restores the entry stack pointer. -/
theorem sp_restore (sp : Word) : sp - 8#64 + 8#64 = sp := by
  have h : (-(8#64) : BitVec 64) + 8#64 = 0#64 := by decide
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, h, BitVec.add_zero]

/-! ### Arithmetic the certificate needs

Four small facts, each about the decompiled values alone. They are what the
machine's `Sz`/`BitVec` plumbing has to be reduced *to*; after this point the
proof is pure sequencing. -/

/-- A 32-bit value spilled and reloaded through four frame bytes comes back. -/
theorem reload_setWidth (x : BitVec Sz.d.bits) :
    (BitVec.ofNat 64 ((x.setWidth 64).toNat % 2 ^ (8 * 4))).setWidth Sz.d.bits = x := by
  have hx : x.toNat < 2 ^ 32 := x.isLt
  have hx64 : x.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))
  have h1 : (x.setWidth 64).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hx64
  rw [h1, show 8 * 4 = 32 from rfl, Nat.mod_eq_of_lt hx]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64]
  exact Nat.mod_eq_of_lt hx

/-- The masked CL count of a shift, when the 32-bit value in `ecx` is below 32.
`exec` masks with `% Sz.d.bits`; the hardware's `& 1FH` is the same thing
(`Ext.count_mask`). -/
theorem masked_count (x : BitVec Sz.d.bits) (hx : x.toNat < 32) :
    ((x.setWidth 64).setWidth 8).toNat % Sz.d.bits = x.toNat := by
  have hx32 : x.toNat < 2 ^ 32 := x.isLt
  have hx64 : x.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le hx32 (Nat.pow_le_pow_right (by omega) (by omega))
  have h1 : ((x.setWidth 64).setWidth 8).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx64]
    exact Nat.mod_eq_of_lt (by rw [show (2 : Nat) ^ 8 = 256 from rfl]; omega)
  rw [h1]
  exact Nat.mod_eq_of_lt (show x.toNat < Sz.d.bits from hx)

/-- `32 - count` as the machine computes it (`mov $0x20,%ecx; sub -0x8(%rbp),%ecx`)
is `32 - count` as a natural number, for `0 < count < 32`. -/
theorem sub_from_32 (x : BitVec Sz.d.bits) (hpos : 0 < x.toNat) (hlt : x.toNat < 32) :
    ((0x20 : BitVec Sz.d.bits) - x).toNat = 32 - x.toNat := by
  have h32 : ((0x20 : BitVec Sz.d.bits)).toNat = 32 := by decide
  have hb : (2 : Nat) ^ Sz.d.bits = 2 ^ 32 := rfl
  rw [BitVec.toNat_sub, h32, hb]
  rw [show 2 ^ 32 - x.toNat + 32 = 2 ^ 32 + (32 - x.toNat) by omega, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- The effective address of `[rbp + disp]`. -/
theorem frame_addr (disp : BitVec 32) (t : State) (nxt : Word) :
    (frame disp).addr t nxt = t.read .rbp + disp.signExtend 64 := by
  simp [frame, Mem.addr, Mem.ofReg]

/-- `-0x4(%rbp)` with `rbp` at the post-push `rsp` is twelve below the entry
`rsp`: the four frame bytes holding the spilled `value`. -/
theorem addr4 (sp : Word) :
    sp - 8#64 + ((0xFFFFFFFC : BitVec 32).signExtend 64) = sp - 12#64 := by
  have hs : ((0xFFFFFFFC : BitVec 32).signExtend 64) = -(4#64) := by decide
  have ha : -(8#64) + -(4#64) = -(12#64) := by decide
  rw [hs, BitVec.sub_eq_add_neg, BitVec.add_assoc, ha, ← BitVec.sub_eq_add_neg]

/-- `-0x8(%rbp)` likewise: the four bytes holding the spilled `count`. -/
theorem addr8 (sp : Word) :
    sp - 8#64 + ((0xFFFFFFF8 : BitVec 32).signExtend 64) = sp - 16#64 := by
  have hs : ((0xFFFFFFF8 : BitVec 32).signExtend 64) = -(8#64) := by decide
  have ha : -(8#64) + -(8#64) = -(16#64) := by decide
  rw [hs, BitVec.sub_eq_add_neg, BitVec.add_assoc, ha, ← BitVec.sub_eq_add_neg]

/-- The OR of the two shifts is the decompiled function. -/
theorem or_shifts_eq (value : BitVec 32) (count : Nat) :
    ShiftOp.shr.result value count ||| ShiftOp.shl.result value (32 - count) =
      rightRotSpec value count := rfl

/-- Replay the per-instruction proof for the fully quantified `right_rot`
return certificate. Untrusted generators may invoke this template directly;
the macro expands into ordinary Lean proof terms checked by the kernel. -/
macro "certify_right_rot_returns" : tactic =>
  `(tactic| (
    intro entry exit m h
    obtain ⟨hrip, himage, hretaddr, hfw, hfr, hsplow, hapart, hcpos, hclt⟩ := h
    simp only [args, Post]
    -- ### Bounds and addresses
    have hcl : code.length = 37 := by decide
    have hb : entry.toNat + 37 ≤ 2 ^ 64 := by
      have hbb := himage.bound; rw [hcl] at hbb; exact hbb
    have hsplt : (m.core.read .rsp).toNat < 2 ^ 64 := (m.core.read .rsp).isLt
    have hsp8 : (m.core.read .rsp - 8#64).toNat = (m.core.read .rsp).toNat - 8 :=
      toNat_sub_lit (k := 8) (by omega) (by omega)
    have hsp12 : (m.core.read .rsp - 12#64).toNat = (m.core.read .rsp).toNat - 12 :=
      toNat_sub_lit (k := 12) (by omega) (by omega)
    have hsp16 : (m.core.read .rsp - 16#64).toNat = (m.core.read .rsp).toNat - 16 :=
      toNat_sub_lit (k := 16) (by omega) (by omega)
    -- Anything inside the frame is disjoint from the code.
    have hdis : ∀ a l : Nat, (m.core.read .rsp).toNat - 16 ≤ a →
        a + l ≤ (m.core.read .rsp).toNat →
        entry.toNat + code.length ≤ a ∨ a + l ≤ entry.toNat := by
      intro a l h1 h2
      rw [hcl]
      rcases hapart with hap | hap
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    -- Permissions, transported along the chain of writes (which keep the regions).
    have permOf : ∀ {a b : Memory}, b.regions = a.regions → ∀ {acc : Process.Access} {ad l : Nat},
        a.Permitted acc ad l → b.Permitted acc ad l := by
      intro a b hr acc ad l hp
      rw [Memory.Permitted, X86.Memory.checkSpan_congr hr]
      exact hp
    have hpushW : m.memory.Permitted .write (m.core.read .rsp - 8#64).toNat 8 := by
      rw [hsp8]
      have hs := permitted_sub hfw (off := 8) (count := 8) (by omega) (by omega)
      rwa [show (m.core.read .rsp).toNat - 16 + 8 = (m.core.read .rsp).toNat - 8 by omega] at hs
    have hpushR : m.memory.Permitted .read (m.core.read .rsp - 8#64).toNat 8 := by
      rw [hsp8]
      have hs := permitted_sub hfr (off := 8) (count := 8) (by omega) (by omega)
      rwa [show (m.core.read .rsp).toNat - 16 + 8 = (m.core.read .rsp).toNat - 8 by omega] at hs
    have hs12W : m.memory.Permitted .write (m.core.read .rsp - 12#64).toNat 4 := by
      rw [hsp12]
      have hs := permitted_sub hfw (off := 4) (count := 4) (by omega) (by omega)
      rwa [show (m.core.read .rsp).toNat - 16 + 4 = (m.core.read .rsp).toNat - 12 by omega] at hs
    have hs12R : m.memory.Permitted .read (m.core.read .rsp - 12#64).toNat 4 := by
      rw [hsp12]
      have hs := permitted_sub hfr (off := 4) (count := 4) (by omega) (by omega)
      rwa [show (m.core.read .rsp).toNat - 16 + 4 = (m.core.read .rsp).toNat - 12 by omega] at hs
    have hs16W : m.memory.Permitted .write (m.core.read .rsp - 16#64).toNat 4 := by
      rw [hsp16]
      have hs := permitted_sub hfw (off := 0) (count := 4) (by omega) (by omega)
      rwa [Nat.add_zero] at hs
    have hs16R : m.memory.Permitted .read (m.core.read .rsp - 16#64).toNat 4 := by
      rw [hsp16]
      have hs := permitted_sub hfr (off := 0) (count := 4) (by omega) (by omega)
      rwa [Nat.add_zero] at hs
    -- `[rbp - 4]` and `[rbp - 8]` once `rbp` holds the post-push `rsp`.
    have hframe4 : ∀ (t : State) (nxt : Word), t.read .rbp = m.core.read .rsp - 8#64 →
        (frame 0xFFFFFFFC).addr t nxt = m.core.read .rsp - 12#64 := by
      intro t nxt ht
      rw [frame_addr, ht, addr4]
    have hframe8 : ∀ (t : State) (nxt : Word), t.read .rbp = m.core.read .rsp - 8#64 →
        (frame 0xFFFFFFF8).addr t nxt = m.core.read .rsp - 16#64 := by
      intro t nxt ht
      rw [frame_addr, ht, addr8]
    have hdb : Sz.d.bytes = 4 := rfl
    have hrip₀ : m.core.rip.toNat = entry.toNat + 0 := by rw [hrip]; omega
    -- The register-read tactic used throughout: unfold the state updates `exec`
    -- produced and discharge the register disequalities.
    -- ### c90  55                 push %rbp
    obtain ⟨mem₁, hmem₁⟩ : ∃ mm : Memory, X86.pushWord m.core m.memory (m.core.read .rbp) =
        some (m.core.write .rsp (m.core.read .rsp - 8#64), mm) :=
      ⟨_, X86.pushWord_eq_some hpushW⟩
    obtain ⟨c₁, hc₁⟩ : ∃ c : State, c =
        { m.core.write .rsp (m.core.read .rsp - 8#64) with
          rip := m.core.rip + BitVec.ofNat 64 (X86.Insn.push Reg.rbp).length } := ⟨_, rfl⟩
    have e₀ : Ext.exec (.push .rbp) m.core m.memory = .ok c₁ mem₁ := by
      rw [Ext.exec_push, hc₁]
      simp only [X86.Insn.exec, hmem₁, Option.map_some]
    have hstep₀ : Ext.stepOpt exit m = some ⟨c₁, mem₁⟩ :=
      retires_instr himage 0 (.push .rbp) hrip₀ (by decide) (by decide) (by decide) e₀
    have hwo₁ : Memory.WritesOnly m.memory mem₁ (m.core.read .rsp - 8#64).toNat 8 :=
      X86.pushWord_writesOnly hmem₁
    have hreg₁ : mem₁.regions = m.memory.regions := hwo₁.1
    have himg₁ : Image code entry mem₁ :=
      Image.of_writesOnly himage hwo₁ (by rw [hsp8]; exact hdis _ 8 (by omega) (by omega))
    have hrip₁ : c₁.rip.toNat = entry.toNat + 1 := by
      rw [hc₁]; rw [L0]; exact rip_step (len := 1) hrip₀ (by omega)
    have hc₁rsp : c₁.read .rsp = m.core.read .rsp - 8#64 := by simp [hc₁]
    have hc₁oth : ∀ r : Reg, r ≠ .rsp → c₁.read r = m.core.read r := by
      intro r hr; simp [hc₁, hr]
    -- ### c91  48 89 e5           mov %rsp,%rbp
    obtain ⟨c₂, hc₂⟩ : ∃ c : State, c =
        { Sz.q.write c₁ .rbp (Sz.q.read c₁ .rsp) with
          rip := c₁.rip + BitVec.ofNat 64 (Ext.Instr.mov .q (.reg Reg.rbp) Reg.rsp).length } :=
      ⟨_, rfl⟩
    have e₁ : Ext.exec (.mov .q (.reg .rbp) .rsp) c₁ mem₁ = .ok c₂ mem₁ := by
      rw [hc₂]; exact Ext.exec_mov_reg c₁ mem₁ .q .rbp .rsp
    have hstep₁ : Ext.stepOpt exit ⟨c₁, mem₁⟩ = some ⟨c₂, mem₁⟩ :=
      retires_instr himg₁ 1 (.mov .q (.reg .rbp) .rsp) hrip₁ (by decide) (by decide) (by decide) e₁
    have hrip₂ : c₂.rip.toNat = entry.toNat + 4 := by
      rw [hc₂]; rw [L1]; exact rip_step (len := 3) hrip₁ (by omega)
    have hc₂rbp : c₂.read .rbp = m.core.read .rsp - 8#64 := by simp [hc₂, hc₁rsp]
    have hc₂oth : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₂.read r = m.core.read r := by
      intro r h1 h2; simp [hc₂, h2, hc₁oth r h1]
    have hc₂rdi : Sz.d.read c₂ .rdi = Sz.d.read m.core .rdi := by
      simp only [Sz.read, hc₂oth .rdi (by decide) (by decide)]
    have hc₂rsi : Sz.d.read c₂ .rsi = Sz.d.read m.core .rsi := by
      simp only [Sz.read, hc₂oth .rsi (by decide) (by decide)]
    have hc₂rsp : c₂.read .rsp = m.core.read .rsp - 8#64 := by simp [hc₂, hc₁rsp]
    -- ### c94  89 7d fc           mov %edi,-0x4(%rbp)
    obtain ⟨mem₂, hst₂⟩ := storeN_isSome (memory := mem₁)
      (address := m.core.read .rsp - 12#64) (k := 4)
      (v := (Sz.d.read m.core .rdi).setWidth 64) (permOf hreg₁ hs12W)
    obtain ⟨c₃, hc₃⟩ : ∃ c : State, c =
        { c₂ with rip := c₂.rip +
          BitVec.ofNat 64 (Ext.Instr.mov .d (.mem (frame 0xFFFFFFFC)) Reg.rdi).length } := ⟨_, rfl⟩
    have e₂ : Ext.exec (.mov .d (.mem (frame 0xFFFFFFFC)) .rdi) c₂ mem₁ = .ok c₃ mem₂ := by
      rw [Ext.exec_store, hframe4 _ _ hc₂rbp, hdb, hc₂rdi, hst₂, hc₃]
    have hstep₂ : Ext.stepOpt exit ⟨c₂, mem₁⟩ = some ⟨c₃, mem₂⟩ :=
      retires_instr himg₁ 4 (.mov .d (.mem (frame 0xFFFFFFFC)) .rdi) hrip₂
        (by decide) (by decide) (by decide) e₂
    have hwo₂ : Memory.WritesOnly mem₁ mem₂ (m.core.read .rsp - 12#64).toNat 4 :=
      Ext.storeN_writesOnly hst₂
    have hreg₂ : mem₂.regions = m.memory.regions := hwo₂.1.trans hreg₁
    have himg₂ : Image code entry mem₂ :=
      Image.of_writesOnly himg₁ hwo₂ (by rw [hsp12]; exact hdis _ 4 (by omega) (by omega))
    have hrip₃ : c₃.rip.toNat = entry.toNat + 7 := by
      rw [hc₃]; rw [L2]; exact rip_step (len := 3) hrip₂ (by omega)
    have hc₃rbp : c₃.read .rbp = m.core.read .rsp - 8#64 := by simp [hc₃, hc₂rbp]
    have hc₃oth : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₃.read r = m.core.read r := by
      intro r h1 h2; simp [hc₃, hc₂oth r h1 h2]
    have hc₃rsi : Sz.d.read c₃ .rsi = Sz.d.read m.core .rsi := by
      simp only [Sz.read, hc₃oth .rsi (by decide) (by decide)]
    -- ### c97  89 75 f8           mov %esi,-0x8(%rbp)
    obtain ⟨mem₃, hst₃⟩ := storeN_isSome (memory := mem₂)
      (address := m.core.read .rsp - 16#64) (k := 4)
      (v := (Sz.d.read m.core .rsi).setWidth 64) (permOf hreg₂ hs16W)
    obtain ⟨c₄, hc₄⟩ : ∃ c : State, c =
        { c₃ with rip := c₃.rip +
          BitVec.ofNat 64 (Ext.Instr.mov .d (.mem (frame 0xFFFFFFF8)) Reg.rsi).length } := ⟨_, rfl⟩
    have e₃ : Ext.exec (.mov .d (.mem (frame 0xFFFFFFF8)) .rsi) c₃ mem₂ = .ok c₄ mem₃ := by
      rw [Ext.exec_store, hframe8 _ _ hc₃rbp, hdb, hc₃rsi, hst₃, hc₄]
    have hstep₃ : Ext.stepOpt exit ⟨c₃, mem₂⟩ = some ⟨c₄, mem₃⟩ :=
      retires_instr himg₂ 7 (.mov .d (.mem (frame 0xFFFFFFF8)) .rsi) hrip₃
        (by decide) (by decide) (by decide) e₃
    have hwo₃ : Memory.WritesOnly mem₂ mem₃ (m.core.read .rsp - 16#64).toNat 4 :=
      Ext.storeN_writesOnly hst₃
    have himg₃ : Image code entry mem₃ :=
      Image.of_writesOnly himg₂ hwo₃ (by rw [hsp16]; exact hdis _ 4 (by omega) (by omega))
    have hrip₄ : c₄.rip.toNat = entry.toNat + 10 := by
      rw [hc₄]; rw [L3]; exact rip_step (len := 3) hrip₃ (by omega)
    have hc₄rbp : c₄.read .rbp = m.core.read .rsp - 8#64 := by simp [hc₄, hc₃rbp]
    have hc₄oth : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₄.read r = m.core.read r := by
      intro r h1 h2; simp [hc₄, hc₃oth r h1 h2]
    -- ### The two reload facts, once both arguments are spilled.
    have hload12 : Ext.loadN mem₃ (m.core.read .rsp - 12#64) 4 =
        some (BitVec.ofNat 64 (((Sz.d.read m.core .rdi).setWidth 64).toNat % 2 ^ (8 * 4))) := by
      rw [Ext.loadN_storeN_disjoint hst₃ (by rw [hsp12, hsp16]; omega)]
      exact Ext.loadN_storeN hst₂ (permOf hreg₁ hs12R)
    have hload16 : Ext.loadN mem₃ (m.core.read .rsp - 16#64) 4 =
        some (BitVec.ofNat 64 (((Sz.d.read m.core .rsi).setWidth 64).toNat % 2 ^ (8 * 4))) :=
      Ext.loadN_storeN hst₃ (permOf hreg₂ hs16R)
    -- ### The state-to-state read lemmas: each body instruction writes one register.
    have szr : ∀ {a b : State} {r : Reg}, a.read r = b.read r → Sz.d.read a r = Sz.d.read b r := by
      intro a b r hh; simp only [Sz.read, hh]
    have hc₃rsp : c₃.read .rsp = m.core.read .rsp - 8#64 := by simp [hc₃, hc₂rsp]
    have hc₄rsp : c₄.read .rsp = m.core.read .rsp - 8#64 := by simp [hc₄, hc₃rsp]
    -- ### c9a  8b 45 fc           mov -0x4(%rbp),%eax
    obtain ⟨c₅, hc₅⟩ : ∃ c : State, c =
        { Sz.d.write c₄ .rax (Sz.d.read m.core .rdi) with
          rip := c₄.rip +
            BitVec.ofNat 64 (Ext.Instr.load .d Reg.rax (frame 0xFFFFFFFC)).length } := ⟨_, rfl⟩
    have e₄ : Ext.exec (.load .d .rax (frame 0xFFFFFFFC)) c₄ mem₃ = .ok c₅ mem₃ := by
      rw [Ext.exec_load, hframe4 _ _ hc₄rbp, hdb, hload12]
      simp only [reload_setWidth, hc₅]
    have hstep₄ : Ext.stepOpt exit ⟨c₄, mem₃⟩ = some ⟨c₅, mem₃⟩ :=
      retires_instr himg₃ 10 (.load .d .rax (frame 0xFFFFFFFC)) hrip₄
        (by decide) (by decide) (by decide) e₄
    have hrip₅ : c₅.rip.toNat = entry.toNat + 13 := by
      rw [hc₅]; rw [L4]; exact rip_step (len := 3) hrip₄ (by omega)
    have hr₅ : ∀ r : Reg, r ≠ .rax → c₅.read r = c₄.read r := by
      intro r hh; rw [hc₅]; exact Sz.read_write_other _ _ _ _ _ hh
    have hv₅ : Sz.d.read c₅ .rax = Sz.d.read m.core .rdi := by
      simp only [hc₅, szRead_setRip, Sz.read_write]
    -- ### c9d  8b 4d f8           mov -0x8(%rbp),%ecx
    obtain ⟨c₆, hc₆⟩ : ∃ c : State, c =
        { Sz.d.write c₅ .rcx (Sz.d.read m.core .rsi) with
          rip := c₅.rip +
            BitVec.ofNat 64 (Ext.Instr.load .d Reg.rcx (frame 0xFFFFFFF8)).length } := ⟨_, rfl⟩
    have e₅ : Ext.exec (.load .d .rcx (frame 0xFFFFFFF8)) c₅ mem₃ = .ok c₆ mem₃ := by
      rw [Ext.exec_load, hframe8 _ _ ((hr₅ .rbp (by decide)).trans hc₄rbp), hdb, hload16]
      simp only [reload_setWidth, hc₆]
    have hstep₅ : Ext.stepOpt exit ⟨c₅, mem₃⟩ = some ⟨c₆, mem₃⟩ :=
      retires_instr himg₃ 13 (.load .d .rcx (frame 0xFFFFFFF8)) hrip₅
        (by decide) (by decide) (by decide) e₅
    have hrip₆ : c₆.rip.toNat = entry.toNat + 16 := by
      rw [hc₆]; rw [L5]; exact rip_step (len := 3) hrip₅ (by omega)
    have hr₆ : ∀ r : Reg, r ≠ .rcx → c₆.read r = c₅.read r := by
      intro r hh; rw [hc₆]; exact Sz.read_write_other _ _ _ _ _ hh
    have hv₆ : Sz.d.read c₆ .rax = Sz.d.read m.core .rdi :=
      (szr (hr₆ .rax (by decide))).trans hv₅
    have hcnt₆ : (Count.cl.raw c₆).toNat % Sz.d.bits = (Sz.d.read m.core .rsi).toNat := by
      have hrcx : c₆.read .rcx = (Sz.d.read m.core .rsi).setWidth 64 := by
        simp only [hc₆, read_setRip, read_szWrite_same]
      simp only [Count.raw, hrcx]
      exact masked_count _ hclt
    -- ### ca0  d3 e8              shr %cl,%eax
    obtain ⟨c₇, hc₇⟩ : ∃ c : State, c =
        { Sz.d.write c₆ .rax
            (ShiftOp.shr.result (Sz.d.read c₆ .rax) ((Count.cl.raw c₆).toNat % Sz.d.bits)) with
          flags := ShiftOp.shr.flags (Sz.d.read c₆ .rax)
            ((Count.cl.raw c₆).toNat % Sz.d.bits) c₆.flags
          rip := c₆.rip +
            BitVec.ofNat 64 (Ext.Instr.shift .d .shr (.reg Reg.rax) .cl).length } := ⟨_, rfl⟩
    have e₆ : Ext.exec (.shift .d .shr (.reg .rax) .cl) c₆ mem₃ = .ok c₇ mem₃ := by
      rw [hc₇]; exact Ext.exec_shift_reg c₆ mem₃ .d .shr .rax .cl
    have hstep₆ : Ext.stepOpt exit ⟨c₆, mem₃⟩ = some ⟨c₇, mem₃⟩ :=
      retires_instr himg₃ 16 (.shift .d .shr (.reg .rax) .cl) hrip₆
        (by decide) (by decide) (by decide) e₆
    have hrip₇ : c₇.rip.toNat = entry.toNat + 18 := by
      rw [hc₇]; rw [L6]; exact rip_step (len := 2) hrip₆ (by omega)
    have hr₇ : ∀ r : Reg, r ≠ .rax → c₇.read r = c₆.read r := by
      intro r hh; rw [hc₇]; exact Sz.read_write_other _ _ _ _ _ hh
    have hshr : Sz.d.read c₇ .rax =
        ShiftOp.shr.result (Sz.d.read m.core .rdi) (Sz.d.read m.core .rsi).toNat := by
      simp only [hc₇, szRead_setFlagsRip, Sz.read_write, hv₆, hcnt₆]
    -- ### ca2  8b 55 fc           mov -0x4(%rbp),%edx
    obtain ⟨c₈, hc₈⟩ : ∃ c : State, c =
        { Sz.d.write c₇ .rdx (Sz.d.read m.core .rdi) with
          rip := c₇.rip +
            BitVec.ofNat 64 (Ext.Instr.load .d Reg.rdx (frame 0xFFFFFFFC)).length } := ⟨_, rfl⟩
    have e₇ : Ext.exec (.load .d .rdx (frame 0xFFFFFFFC)) c₇ mem₃ = .ok c₈ mem₃ := by
      rw [Ext.exec_load, hframe4 _ _ ((hr₇ .rbp (by decide)).trans
        ((hr₆ .rbp (by decide)).trans ((hr₅ .rbp (by decide)).trans hc₄rbp))), hdb, hload12]
      simp only [reload_setWidth, hc₈]
    have hstep₇ : Ext.stepOpt exit ⟨c₇, mem₃⟩ = some ⟨c₈, mem₃⟩ :=
      retires_instr himg₃ 18 (.load .d .rdx (frame 0xFFFFFFFC)) hrip₇
        (by decide) (by decide) (by decide) e₇
    have hrip₈ : c₈.rip.toNat = entry.toNat + 21 := by
      rw [hc₈]; rw [L7]; exact rip_step (len := 3) hrip₇ (by omega)
    have hr₈ : ∀ r : Reg, r ≠ .rdx → c₈.read r = c₇.read r := by
      intro r hh; rw [hc₈]; exact Sz.read_write_other _ _ _ _ _ hh
    have hv₈ : Sz.d.read c₈ .rdx = Sz.d.read m.core .rdi := by
      simp only [hc₈, szRead_setRip, Sz.read_write]
    -- ### ca5  b9 20 00 00 00     mov $0x20,%ecx
    obtain ⟨c₉, hc₉⟩ : ∃ c : State, c =
        { c₈.write .rcx ((0x20 : BitVec 32).setWidth 64) with
          rip := c₈.rip + BitVec.ofNat 64 (Ext.Instr.movI32 Reg.rcx 0x20).length } := ⟨_, rfl⟩
    have e₈ : Ext.exec (.movI32 .rcx 0x20) c₈ mem₃ = .ok c₉ mem₃ := by
      rw [hc₉]; exact Ext.exec_movI32 c₈ mem₃ .rcx 0x20
    have hstep₈ : Ext.stepOpt exit ⟨c₈, mem₃⟩ = some ⟨c₉, mem₃⟩ :=
      retires_instr himg₃ 21 (.movI32 .rcx 0x20) hrip₈ (by decide) (by decide) (by decide) e₈
    have hrip₉ : c₉.rip.toNat = entry.toNat + 26 := by
      rw [hc₉]; rw [L8]; exact rip_step (len := 5) hrip₈ (by omega)
    have hr₉ : ∀ r : Reg, r ≠ .rcx → c₉.read r = c₈.read r := by
      intro r hh; rw [hc₉]; exact State.read_write_other _ _ _ _ hh
    have hv₉rcx : Sz.d.read c₉ .rcx = (0x20 : BitVec Sz.d.bits) := by
      simp only [hc₉, Sz.read, read_setRip, State.read_write_same]
      decide
    -- ### caa  2b 4d f8           sub -0x8(%rbp),%ecx
    have hc₉rbp : c₉.read .rbp = m.core.read .rsp - 8#64 :=
      (hr₉ .rbp (by decide)).trans ((hr₈ .rbp (by decide)).trans ((hr₇ .rbp (by decide)).trans
        ((hr₆ .rbp (by decide)).trans ((hr₅ .rbp (by decide)).trans hc₄rbp))))
    have hrm : ∀ nxt : Word, Ext.readRM .d (.mem (frame 0xFFFFFFF8)) c₉ mem₃ nxt =
        some (Sz.d.read m.core .rsi) := by
      intro nxt
      simp only [Ext.readRM, hframe8 _ _ hc₉rbp, hdb, hload16, Option.map_some, reload_setWidth]
    obtain ⟨c₁₀, hc₁₀⟩ : ∃ c : State, c =
        { Sz.d.write c₉ .rcx
            (Ext.AluOp.resultN .sub (Sz.d.read c₉ .rcx) (Sz.d.read m.core .rsi)) with
          flags := Ext.AluOp.flagsN .sub (Sz.d.read c₉ .rcx) (Sz.d.read m.core .rsi)
          rip := c₉.rip +
            BitVec.ofNat 64 (Ext.Instr.aluR .d .sub Reg.rcx
              (.mem (frame 0xFFFFFFF8))).length } := ⟨_, rfl⟩
    have e₉ : Ext.exec (.aluR .d .sub .rcx (.mem (frame 0xFFFFFFF8))) c₉ mem₃ = .ok c₁₀ mem₃ := by
      rw [hc₁₀]; exact exec_aluR_mem .d .sub .rcx (frame 0xFFFFFFF8) c₉ mem₃ (by decide) (hrm _)
    have hstep₉ : Ext.stepOpt exit ⟨c₉, mem₃⟩ = some ⟨c₁₀, mem₃⟩ :=
      retires_instr himg₃ 26 (.aluR .d .sub .rcx (.mem (frame 0xFFFFFFF8))) hrip₉
        (by decide) (by decide) (by decide) e₉
    have hrip₁₀ : c₁₀.rip.toNat = entry.toNat + 29 := by
      rw [hc₁₀]; rw [L9]; exact rip_step (len := 3) hrip₉ (by omega)
    have hr₁₀ : ∀ r : Reg, r ≠ .rcx → c₁₀.read r = c₉.read r := by
      intro r hh; rw [hc₁₀]; exact Sz.read_write_other _ _ _ _ _ hh
    have hcnt₁₀ : (Count.cl.raw c₁₀).toNat % Sz.d.bits = 32 - (Sz.d.read m.core .rsi).toNat := by
      have hrcx : c₁₀.read .rcx =
          ((0x20 : BitVec Sz.d.bits) - Sz.d.read m.core .rsi).setWidth 64 := by
        simp only [hc₁₀, read_setFlagsRip, read_szWrite_same, hv₉rcx, Ext.AluOp.resultN]
      simp only [Count.raw, hrcx]
      rw [masked_count _ (by rw [sub_from_32 _ hcpos hclt]; omega)]
      exact sub_from_32 _ hcpos hclt
    have hv₁₀rdx : Sz.d.read c₁₀ .rdx = Sz.d.read m.core .rdi :=
      (szr (hr₁₀ .rdx (by decide))).trans ((szr (hr₉ .rdx (by decide))).trans hv₈)
    -- ### cad  d3 e2              shl %cl,%edx
    obtain ⟨c₁₁, hc₁₁⟩ : ∃ c : State, c =
        { Sz.d.write c₁₀ .rdx
            (ShiftOp.shl.result (Sz.d.read c₁₀ .rdx) ((Count.cl.raw c₁₀).toNat % Sz.d.bits)) with
          flags := ShiftOp.shl.flags (Sz.d.read c₁₀ .rdx)
            ((Count.cl.raw c₁₀).toNat % Sz.d.bits) c₁₀.flags
          rip := c₁₀.rip +
            BitVec.ofNat 64 (Ext.Instr.shift .d .shl (.reg Reg.rdx) .cl).length } := ⟨_, rfl⟩
    have e₁₀ : Ext.exec (.shift .d .shl (.reg .rdx) .cl) c₁₀ mem₃ = .ok c₁₁ mem₃ := by
      rw [hc₁₁]; exact Ext.exec_shift_reg c₁₀ mem₃ .d .shl .rdx .cl
    have hstep₁₀ : Ext.stepOpt exit ⟨c₁₀, mem₃⟩ = some ⟨c₁₁, mem₃⟩ :=
      retires_instr himg₃ 29 (.shift .d .shl (.reg .rdx) .cl) hrip₁₀
        (by decide) (by decide) (by decide) e₁₀
    have hrip₁₁ : c₁₁.rip.toNat = entry.toNat + 31 := by
      rw [hc₁₁]; rw [L10]; exact rip_step (len := 2) hrip₁₀ (by omega)
    have hr₁₁ : ∀ r : Reg, r ≠ .rdx → c₁₁.read r = c₁₀.read r := by
      intro r hh; rw [hc₁₁]; exact Sz.read_write_other _ _ _ _ _ hh
    have hshl : Sz.d.read c₁₁ .rdx =
        ShiftOp.shl.result (Sz.d.read m.core .rdi) (32 - (Sz.d.read m.core .rsi).toNat) := by
      simp only [hc₁₁, szRead_setFlagsRip, Sz.read_write, hv₁₀rdx, hcnt₁₀]
    -- ### caf  89 d1              mov %edx,%ecx
    obtain ⟨c₁₂, hc₁₂⟩ : ∃ c : State, c =
        { Sz.d.write c₁₁ .rcx (Sz.d.read c₁₁ .rdx) with
          rip := c₁₁.rip +
            BitVec.ofNat 64 (Ext.Instr.mov .d (.reg Reg.rcx) Reg.rdx).length } := ⟨_, rfl⟩
    have e₁₁ : Ext.exec (.mov .d (.reg .rcx) .rdx) c₁₁ mem₃ = .ok c₁₂ mem₃ := by
      rw [hc₁₂]; exact Ext.exec_mov_reg c₁₁ mem₃ .d .rcx .rdx
    have hstep₁₁ : Ext.stepOpt exit ⟨c₁₁, mem₃⟩ = some ⟨c₁₂, mem₃⟩ :=
      retires_instr himg₃ 31 (.mov .d (.reg .rcx) .rdx) hrip₁₁
        (by decide) (by decide) (by decide) e₁₁
    have hrip₁₂ : c₁₂.rip.toNat = entry.toNat + 33 := by
      rw [hc₁₂]; rw [L11]; exact rip_step (len := 2) hrip₁₁ (by omega)
    have hr₁₂ : ∀ r : Reg, r ≠ .rcx → c₁₂.read r = c₁₁.read r := by
      intro r hh; rw [hc₁₂]; exact Sz.read_write_other _ _ _ _ _ hh
    have hv₁₂rcx : Sz.d.read c₁₂ .rcx =
        ShiftOp.shl.result (Sz.d.read m.core .rdi) (32 - (Sz.d.read m.core .rsi).toNat) := by
      simp only [hc₁₂, szRead_setRip, Sz.read_write, hshl]
    have hv₁₂rax : Sz.d.read c₁₂ .rax =
        ShiftOp.shr.result (Sz.d.read m.core .rdi) (Sz.d.read m.core .rsi).toNat :=
      (szr (hr₁₂ .rax (by decide))).trans ((szr (hr₁₁ .rax (by decide))).trans
        ((szr (hr₁₀ .rax (by decide))).trans ((szr (hr₉ .rax (by decide))).trans
          ((szr (hr₈ .rax (by decide))).trans hshr))))
    -- ### cb1  09 c8              or %ecx,%eax
    obtain ⟨c₁₃, hc₁₃⟩ : ∃ c : State, c =
        { Sz.d.write c₁₂ .rax
            (Ext.AluOp.resultN .or (Sz.d.read c₁₂ .rax) (Sz.d.read c₁₂ .rcx)) with
          flags := Ext.AluOp.flagsN .or (Sz.d.read c₁₂ .rax) (Sz.d.read c₁₂ .rcx)
          rip := c₁₂.rip +
            BitVec.ofNat 64 (Ext.Instr.alu .d .or (.reg Reg.rax) Reg.rcx).length } := ⟨_, rfl⟩
    have e₁₂ : Ext.exec (.alu .d .or (.reg .rax) .rcx) c₁₂ mem₃ = .ok c₁₃ mem₃ := by
      rw [hc₁₃]; exact Ext.exec_alu_reg c₁₂ mem₃ .d .or .rax .rcx (by decide)
    have hstep₁₂ : Ext.stepOpt exit ⟨c₁₂, mem₃⟩ = some ⟨c₁₃, mem₃⟩ :=
      retires_instr himg₃ 33 (.alu .d .or (.reg .rax) .rcx) hrip₁₂
        (by decide) (by decide) (by decide) e₁₂
    have hrip₁₃ : c₁₃.rip.toNat = entry.toNat + 35 := by
      rw [hc₁₃]; rw [L12]; exact rip_step (len := 2) hrip₁₂ (by omega)
    have hr₁₃ : ∀ r : Reg, r ≠ .rax → c₁₃.read r = c₁₂.read r := by
      intro r hh; rw [hc₁₃]; exact Sz.read_write_other _ _ _ _ _ hh
    -- **The functional conclusion**: `eax` holds the decompiled function's value.
    have hrax : Sz.d.read c₁₃ .rax =
        rightRotSpec (Sz.d.read m.core .rdi) (Sz.d.read m.core .rsi).toNat := by
      simp only [hc₁₃, szRead_setFlagsRip, Sz.read_write, hv₁₂rax, hv₁₂rcx, Ext.AluOp.resultN]
      exact or_shifts_eq _ _
    -- ### cb3  5d                 pop %rbp
    have hrsp₁₃ : c₁₃.read .rsp = m.core.read .rsp - 8#64 := by
      rw [hr₁₃ _ (by decide), hr₁₂ _ (by decide), hr₁₁ _ (by decide), hr₁₀ _ (by decide),
        hr₉ _ (by decide), hr₈ _ (by decide), hr₇ _ (by decide), hr₆ _ (by decide),
        hr₅ _ (by decide)]
      exact hc₄rsp
    have hpb₁ : mem₁.readBytes (m.core.read .rsp - 8#64).toNat 8 =
        some (encodeWords [m.core.read .rbp]) := X86.pushWord_readBytes hmem₁ hpushR
    have hpb₃ : mem₃.readBytes (m.core.read .rsp - 8#64).toNat 8 =
        some (encodeWords [m.core.read .rbp]) := by
      show mem₃.readWith .read _ 8 = _
      rw [X86.Memory.readWith_writesOnly hwo₃ .read _ 8 (by rw [hsp8, hsp16]; omega),
        X86.Memory.readWith_writesOnly hwo₂ .read _ 8 (by rw [hsp8, hsp12]; omega)]
      exact hpb₁
    have hpop : X86.popWord c₁₃ mem₃ =
        some (m.core.read .rbp, c₁₃.write .rsp (c₁₃.read .rsp + 8#64)) :=
      X86.popWord_of_readBytes (by rw [hrsp₁₃]; exact hpb₃)
    obtain ⟨c₁₄, hc₁₄⟩ : ∃ c : State, c =
        { (c₁₃.write .rsp (c₁₃.read .rsp + 8#64)).write .rbp (m.core.read .rbp) with
          rip := c₁₃.rip + BitVec.ofNat 64 (X86.Insn.pop Reg.rbp).length } := ⟨_, rfl⟩
    have e₁₃ : Ext.exec (.pop .rbp) c₁₃ mem₃ = .ok c₁₄ mem₃ := by
      rw [Ext.exec_pop, hc₁₄]
      simp only [X86.Insn.exec, hpop, Option.map_some]
    have hstep₁₃ : Ext.stepOpt exit ⟨c₁₃, mem₃⟩ = some ⟨c₁₄, mem₃⟩ :=
      retires_instr himg₃ 35 (.pop .rbp) hrip₁₃ (by decide) (by decide) (by decide) e₁₃
    have hrip₁₄ : c₁₄.rip.toNat = entry.toNat + 36 := by
      rw [hc₁₄]; rw [L13]; exact rip_step (len := 1) hrip₁₃ (by omega)
    have hr₁₄ : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₁₄.read r = c₁₃.read r := by
      intro r h1 h2; simp [hc₁₄, h1, h2]
    have hrbp₁₄ : c₁₄.read .rbp = m.core.read .rbp := by simp [hc₁₄]
    have hrsp₁₄ : c₁₄.read .rsp = m.core.read .rsp := by
      simp only [hc₁₄, read_setRip, State.read_write_other _ _ _ _ (by decide : Reg.rsp ≠ Reg.rbp),
        State.read_write_same, hrsp₁₃]
      exact sp_restore _
    -- ### cb4  c3                 ret
    have hra₃ : mem₃.readBytes (m.core.read .rsp).toNat 8 = some (encodeWords [exit]) := by
      show mem₃.readWith .read _ 8 = _
      rw [X86.Memory.readWith_writesOnly hwo₃ .read _ 8 (by rw [hsp16]; omega),
        X86.Memory.readWith_writesOnly hwo₂ .read _ 8 (by rw [hsp12]; omega),
        X86.Memory.readWith_writesOnly hwo₁ .read _ 8 (by rw [hsp8]; omega)]
      exact hretaddr
    have hpop₂ : X86.popWord c₁₄ mem₃ =
        some (exit, c₁₄.write .rsp (c₁₄.read .rsp + 8#64)) :=
      X86.popWord_of_readBytes (by rw [hrsp₁₄]; exact hra₃)
    obtain ⟨c₁₅, hc₁₅⟩ : ∃ c : State, c =
        { c₁₄.write .rsp (c₁₄.read .rsp + 8#64) with rip := exit } := ⟨_, rfl⟩
    have e₁₄ : Ext.exec .ret c₁₄ mem₃ = .ok c₁₅ mem₃ := by
      rw [Ext.exec_ret, hc₁₅]
      simp only [X86.Insn.exec, hpop₂, Option.map_some]
    have hreturn : Ext.step exit ⟨c₁₄, mem₃⟩ = .returned ⟨c₁₅, mem₃⟩ :=
      returns_ret himg₃ 36 hrip₁₄ (by decide) (by decide) e₁₄ (by simp [hc₁₅])
    -- ### Sequencing: fourteen retirements, then the RET.
    have a0 : Advances exit m ⟨c₁, mem₁⟩ := Advances.one hstep₀
    have a1 := a0.step hstep₁
    have a2 := a1.step hstep₂
    have a3 := a2.step hstep₃
    have a4 := a3.step hstep₄
    have a5 := a4.step hstep₅
    have a6 := a5.step hstep₆
    have a7 := a6.step hstep₇
    have a8 := a7.step hstep₈
    have a9 := a8.step hstep₉
    have a10 := a9.step hstep₁₀
    have a11 := a10.step hstep₁₁
    have a12 := a11.step hstep₁₂
    have a13 := a12.step hstep₁₃
    -- ### The memory footprint
    have hframe : Memory.WritesOnly m.memory mem₃ ((m.core.read .rsp).toNat - 16) 16 :=
      writesOnly_trans (writesOnly_trans
        (writesOnly_widen hwo₁ (by rw [hsp8]; omega) (by rw [hsp8]; omega))
        (writesOnly_widen hwo₂ (by rw [hsp12]; omega) (by rw [hsp12]; omega)))
        (writesOnly_widen hwo₃ (by rw [hsp16]) (by rw [hsp16]; omega))
    have hr₁₅ : ∀ r : Reg, r ≠ .rsp → c₁₅.read r = c₁₄.read r := by
      intro r hh; rw [hc₁₅]; exact State.read_write_other _ _ _ _ hh
    have hrsp₁₅ : c₁₅.read .rsp = m.core.read .rsp + 8#64 := by
      rw [hc₁₅]
      show (c₁₄.write .rsp (c₁₄.read .rsp + 8#64)).read .rsp = _
      rw [State.read_write_same, hrsp₁₄]
    have hsaved : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₁₅.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5
      rw [hr₁₅ _ h1, hr₁₄ _ h1 h2, hr₁₃ _ h3, hr₁₂ _ h4, hr₁₁ _ h5, hr₁₀ _ h4, hr₉ _ h4,
        hr₈ _ h5, hr₇ _ h3, hr₆ _ h4, hr₅ _ h3]
      exact hc₄oth _ h1 h2
    refine ⟨⟨c₁₅, mem₃⟩, returns_of_advances a13 hreturn, by simp [hc₁₅], ?_, ?_, ?_, hframe⟩
    · -- the System V result: `eax` holds the decompiled function's value
      show Sz.d.read c₁₅ .rax = _
      rw [szr (hr₁₅ .rax (by decide)), szr (hr₁₄ .rax (by decide) (by decide))]
      exact hrax
    · -- `rsp` is popped past the return address (`sysv64.linkSize = 8`)
      exact hrsp₁₅
    · -- every System V callee-saved register comes back
      intro r hr
      have hcs : r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 :=
        (X86.sysv64_mem_calleeSaved r).mp hr
      rcases hcs with hcs | hcs | hcs | hcs | hcs | hcs
      all_goals subst r
      · exact hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact (hr₁₅ _ (by decide)).trans hrbp₁₄
      · exact hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)
  ))

set_option maxHeartbeats 2000000 in
/-- **`right_rot` returns, computing `rightRotSpec`.** From any ABI-conformant
System V entry state, the real machine returns to `exit` with the System V
result `eax = rightRotSpec value count`, `rsp` restored past the return
address, every callee-saved register preserved, and memory changed only in the
function's sixteen frame bytes. -/
theorem right_rot_returns :
    ∀ {entry exit : Word} {m : MState}, Entry entry exit m →
      ∃ final, Returns exit m final ∧ final.core.rip = exit ∧
        Post (rightRotSpec (args m).1 (args m).2) m final := by
  certify_right_rot_returns

/-- The same, as a `Decompile.Decompiled` certificate. -/
theorem decompiled :
    Decompiled code Entry args (fun p => rightRotSpec p.1 p.2) Post where
  covered := code_covered
  cert entry exit m h := by
    obtain ⟨final, hret, -, hpost⟩ := right_rot_returns h
    exact ⟨final, hret, hpost⟩

end Silmaril.X86.Decompile.RightRot

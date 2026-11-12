module

public import Silmaril.Libc.X86Alloc.Ladder.SizeClass.Defs
public import Silmaril.Raw.Libc.X86Alloc.Steps
public import Silmaril.Raw.Libc.X86Alloc.Whole
public import Silmaril.X86.Sep.Alloc.Thms

/-! # Proofs: rung 07 (size classes) — the listing, decoded once, and the step forms it needs -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClass

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.SizeClass
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Whole

/-- The operand `d(%b,%i,1)`. -/
def idx (b i : Reg) (h : i ≠ .rsp) (d : BitVec 32) : Silmaril.X86.Ext.Mem :=
  ⟨.reg b, some ⟨i, 0, h⟩, d, fun h => by cases h⟩

theorem idx_addr (b i : Reg) (h : i ≠ .rsp) (d : BitVec 32) (s : Silmaril.X86.State) (next : Word) :
    (idx b i h d).addr s next = s.read b + s.read i + d.signExtend 64 := by
  simp [Silmaril.X86.Ext.Mem.addr, idx, Silmaril.X86.Ext.Base.value, Silmaril.X86.Ext.Index.value]

/-- `jbe` after `cmp y, x`: taken iff `x ≤ y` unsigned. -/
theorem eval_be_cmp (x y : Word) :
    Silmaril.X86.Ext.Cond.be.eval (Silmaril.X86.Ext.AluOp.flagsN .cmp x y) =
      some (decide (x.toNat ≤ y.toNat)) := by
  simp only [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN,
    Silmaril.X86.Ext.subBorrowN_eq, BitVec.ult, Silmaril.X86.Ext.isZeroN]
  simp only [Silmaril.X86.Ext.kOr, Option.some.injEq]
  by_cases h : x = y
  · subst h; simp
  · have : (x - y == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; exact h (by have := congrArg (· + y) e; simpa using this)
    rw [this]
    have hne : x.toNat ≠ y.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    by_cases hl : x.toNat < y.toNat
    · simp [hl]; omega
    · simp [hl]; omega

/-- `jne` after `test r, r`: taken iff `r ≠ 0`. -/
theorem eval_ne_test (x : Word) :
    Silmaril.X86.Ext.Cond.ne.eval (Silmaril.X86.Ext.logicFlagsN (x &&& x)) = some (x != 0) := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN,
    Silmaril.X86.Ext.kNot, bne]

/-- `jmp rel32`. -/
theorem c_jmp32 {σ : Type} {I : Isa σ} (E : Silmaril.X86.Open.isa.Extends I) {b : Nat}
    {code : List Byte} {o k : Nat} {pc : Word} (hpc : pc.toNat = b + o) (hfit : o + k ≤ code.length)
    {rel : BitVec 32} {f : Reg → Word} {fl : Flags} {M : SProp} {pc' : Word}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.jmp rel, k))
    (hnext : pc + BitVec.ofNat 64 k + rel.signExtend 64 = pc') :
    SPEC I (codePt b code) (St pc f fl M) (St pc' f fl M) := by
  have hl := dec_len hfit hdec
  refine c_whole E hpc hfit hdec (by simp) fun s mem hrip hregs hfl => ⟨_, rfl, ?_, ?_, ?_, hfl⟩
  · show s.rip + _ + _ = _; rw [hrip, ← hl, hnext]
  · exact hregs
  · intro q _; rfl

/-! ## The listing -/

theorem d0 : Silmaril.X86.Ext.decode ((code.drop 0).take 4) = some (.aluI8 .q .cmp (.reg .rdi) 0x10, 4) := by
  decide +kernel
theorem d4 : Silmaril.X86.Ext.decode ((code.drop 4).take 2) = some (.jcc8 .a 0x22, 2) := by
  decide +kernel
theorem d6 : Silmaril.X86.Ext.decode ((code.drop 6).take 7) = some (.load .q .rax (ripMem 0x1da3), 7) := by
  decide +kernel
theorem d13 : Silmaril.X86.Ext.decode ((code.drop 13).take 5) = some (.movI32 .rdx 0x10, 5) := by
  decide +kernel
theorem d18 : Silmaril.X86.Ext.decode ((code.drop 18).take 5) = some (.movI32 .rcx 0x4030e0, 5) := by
  decide +kernel
theorem d23 : Silmaril.X86.Ext.decode ((code.drop 23).take 3) = some (.test .q (.reg .rax) .rax, 3) := by
  decide +kernel
theorem d26 : Silmaril.X86.Ext.decode ((code.drop 26).take 2) = some (.jcc8 .e 0x2c, 2) := by
  decide +kernel
theorem d28 : Silmaril.X86.Ext.decode ((code.drop 28).take 3) = some (.load .q .rdx (Silmaril.X86.Sep.Insn.memAt .rax 0x0), 3) := by
  decide +kernel
theorem d31 : Silmaril.X86.Ext.decode ((code.drop 31).take 3) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rcx 0x0)) .rdx, 3) := by
  decide +kernel
theorem r34 : (code.drop 34).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem d40 : Silmaril.X86.Ext.decode ((code.drop 40).take 4) = some (.aluI8 .q .cmp (.reg .rdi) 0x20, 4) := by
  decide +kernel
theorem d44 : Silmaril.X86.Ext.decode ((code.drop 44).take 2) = some (.jcc8 .a 0x52, 2) := by
  decide +kernel
theorem d46 : Silmaril.X86.Ext.decode ((code.drop 46).take 7) = some (.load .q .rax (ripMem 0x1d73), 7) := by
  decide +kernel
theorem d53 : Silmaril.X86.Ext.decode ((code.drop 53).take 5) = some (.movI32 .rdx 0x20, 5) := by
  decide +kernel
theorem d58 : Silmaril.X86.Ext.decode ((code.drop 58).take 5) = some (.movI32 .rcx 0x4030d8, 5) := by
  decide +kernel
theorem d63 : Silmaril.X86.Ext.decode ((code.drop 63).take 3) = some (.test .q (.reg .rax) .rax, 3) := by
  decide +kernel
theorem d66 : Silmaril.X86.Ext.decode ((code.drop 66).take 2) = some (.jcc8 .ne 0xd8, 2) := by
  decide +kernel
theorem d68 : Silmaril.X86.Ext.decode ((code.drop 68).take 4) = some (.nop 3, 4) := by
  decide +kernel
theorem d72 : Silmaril.X86.Ext.decode ((code.drop 72).take 7) = some (.load .q .rsi (ripMem 0x1d69), 7) := by
  decide +kernel
theorem d79 : Silmaril.X86.Ext.decode ((code.drop 79).take 5) = some (.movI32 .rcx 0x1000, 5) := by
  decide +kernel
theorem d84 : Silmaril.X86.Ext.decode ((code.drop 84).take 4) = some (.lea .q .rdi (Silmaril.X86.Sep.Insn.memAt .rdx 0x10), 4) := by
  decide +kernel
theorem d88 : Silmaril.X86.Ext.decode ((code.drop 88).take 3) = some (.alu .q .sub (.reg .rcx) .rsi, 3) := by
  decide +kernel
theorem d91 : Silmaril.X86.Ext.decode ((code.drop 91).take 3) = some (.alu .q .cmp (.reg .rcx) .rdi, 3) := by
  decide +kernel
theorem d94 : Silmaril.X86.Ext.decode ((code.drop 94).take 2) = some (.jcc8 .b 0x1d, 2) := by
  decide +kernel
theorem d96 : Silmaril.X86.Ext.decode ((code.drop 96).take 4) = some (.lea .q .rax (Silmaril.X86.Sep.Insn.memAt .rsi 0x10), 4) := by
  decide +kernel
theorem d100 : Silmaril.X86.Ext.decode ((code.drop 100).take 7) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0x4030f0)) .rdx, 7) := by
  decide +kernel
theorem d107 : Silmaril.X86.Ext.decode ((code.drop 107).take 4) = some (.lea .q .rcx (idx .rdx .rax (by decide) 0), 4) := by
  decide +kernel
theorem d111 : Silmaril.X86.Ext.decode ((code.drop 111).take 7) = some (.lea .q .rax (Silmaril.X86.Sep.Insn.memAt .rsi 0x403100), 7) := by
  decide +kernel
theorem d118 : Silmaril.X86.Ext.decode ((code.drop 118).take 7) = some (.mov .q (.mem (ripMem 0x1d3b)) .rcx, 7) := by
  decide +kernel
theorem r125 : (code.drop 125).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem d128 : Silmaril.X86.Ext.decode ((code.drop 128).take 4) = some (.aluI8 .q .cmp (.reg .rdi) 0x40, 4) := by
  decide +kernel
theorem d132 : Silmaril.X86.Ext.decode ((code.drop 132).take 2) = some (.jcc8 .be 0x22, 2) := by
  decide +kernel
theorem d134 : Silmaril.X86.Ext.decode ((code.drop 134).take 7) = some (.aluI .q .cmp (.reg .rdi) 0x80, 7) := by
  decide +kernel
theorem d141 : Silmaril.X86.Ext.decode ((code.drop 141).take 2) = some (.jcc8 .a 0x31, 2) := by
  decide +kernel
theorem d143 : Silmaril.X86.Ext.decode ((code.drop 143).take 7) = some (.load .q .rax (ripMem 0x1d02), 7) := by
  decide +kernel
theorem d150 : Silmaril.X86.Ext.decode ((code.drop 150).take 5) = some (.movI32 .rdx 0x80, 5) := by
  decide +kernel
theorem d155 : Silmaril.X86.Ext.decode ((code.drop 155).take 5) = some (.movI32 .rcx 0x4030c8, 5) := by
  decide +kernel
theorem d160 : Silmaril.X86.Ext.decode ((code.drop 160).take 5) = some (.jmp 0xffffff72, 5) := by
  decide +kernel
theorem d168 : Silmaril.X86.Ext.decode ((code.drop 168).take 7) = some (.load .q .rax (ripMem 0x1cf1), 7) := by
  decide +kernel
theorem d175 : Silmaril.X86.Ext.decode ((code.drop 175).take 5) = some (.movI32 .rdx 0x40, 5) := by
  decide +kernel
theorem d180 : Silmaril.X86.Ext.decode ((code.drop 180).take 5) = some (.movI32 .rcx 0x4030d0, 5) := by
  decide +kernel
theorem d185 : Silmaril.X86.Ext.decode ((code.drop 185).take 5) = some (.jmp 0xffffff59, 5) := by
  decide +kernel
theorem d192 : Silmaril.X86.Ext.decode ((code.drop 192).take 2) = some (.alu .d .xor (.reg .rax) .rax, 2) := by
  decide +kernel
theorem r194 : (code.drop 194).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem d208 : Silmaril.X86.Ext.decode ((code.drop 208).take 3) = some (.test .q (.reg .rdi) .rdi, 3) := by
  decide +kernel
theorem d211 : Silmaril.X86.Ext.decode ((code.drop 211).take 2) = some (.jcc8 .e 0x28, 2) := by
  decide +kernel
theorem d213 : Silmaril.X86.Ext.decode ((code.drop 213).take 4) = some (.load .q .rax (Silmaril.X86.Sep.Insn.memAt .rdi 0xfffffff0), 4) := by
  decide +kernel
theorem d217 : Silmaril.X86.Ext.decode ((code.drop 217).take 4) = some (.aluI8 .q .cmp (.reg .rax) 0x10, 4) := by
  decide +kernel
theorem d221 : Silmaril.X86.Ext.decode ((code.drop 221).take 2) = some (.jcc8 .e 0x31, 2) := by
  decide +kernel
theorem d223 : Silmaril.X86.Ext.decode ((code.drop 223).take 4) = some (.aluI8 .q .cmp (.reg .rax) 0x20, 4) := by
  decide +kernel
theorem d227 : Silmaril.X86.Ext.decode ((code.drop 227).take 2) = some (.jcc8 .e 0x3b, 2) := by
  decide +kernel
theorem d229 : Silmaril.X86.Ext.decode ((code.drop 229).take 4) = some (.aluI8 .q .cmp (.reg .rax) 0x40, 4) := by
  decide +kernel
theorem d233 : Silmaril.X86.Ext.decode ((code.drop 233).take 2) = some (.jcc8 .e 0x15, 2) := by
  decide +kernel
theorem d235 : Silmaril.X86.Ext.decode ((code.drop 235).take 7) = some (.load .q .rdx (ripMem 0x1ca6), 7) := by
  decide +kernel
theorem d242 : Silmaril.X86.Ext.decode ((code.drop 242).take 5) = some (.movI32 .rax 0x4030c8, 5) := by
  decide +kernel
theorem d247 : Silmaril.X86.Ext.decode ((code.drop 247).take 3) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rdi 0x0)) .rdx, 3) := by
  decide +kernel
theorem d250 : Silmaril.X86.Ext.decode ((code.drop 250).take 3) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rax 0x0)) .rdi, 3) := by
  decide +kernel
theorem r253 : (code.drop 253).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem d256 : Silmaril.X86.Ext.decode ((code.drop 256).take 7) = some (.load .q .rdx (ripMem 0x1c99), 7) := by
  decide +kernel
theorem d263 : Silmaril.X86.Ext.decode ((code.drop 263).take 5) = some (.movI32 .rax 0x4030d0, 5) := by
  decide +kernel
theorem d268 : Silmaril.X86.Ext.decode ((code.drop 268).take 2) = some (.jmp8 0xe9, 2) := by
  decide +kernel
theorem d272 : Silmaril.X86.Ext.decode ((code.drop 272).take 7) = some (.load .q .rdx (ripMem 0x1c99), 7) := by
  decide +kernel
theorem d279 : Silmaril.X86.Ext.decode ((code.drop 279).take 5) = some (.movI32 .rax 0x4030e0, 5) := by
  decide +kernel
theorem d284 : Silmaril.X86.Ext.decode ((code.drop 284).take 2) = some (.jmp8 0xd9, 2) := by
  decide +kernel
theorem d288 : Silmaril.X86.Ext.decode ((code.drop 288).take 7) = some (.load .q .rdx (ripMem 0x1c81), 7) := by
  decide +kernel
theorem d295 : Silmaril.X86.Ext.decode ((code.drop 295).take 5) = some (.movI32 .rax 0x4030d8, 5) := by
  decide +kernel
theorem d300 : Silmaril.X86.Ext.decode ((code.drop 300).take 2) = some (.jmp8 0xc9, 2) := by
  decide +kernel
theorem hlen : code.length = 304 := by decide +kernel

theorem fit (o k : Nat) (h : o + k ≤ 304 := by decide) : o + k ≤ code.length := hlen ▸ h

end Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClass

module

public import Silmaril.X86.Bir9.Defs
import Silmaril.Proofs.X86.Bir9.Simp

/-!
# Bir9: the block simulation theorem

* `symExec_sound`, `liftBlock_sound`: **`liftBlock L = some b` (closed by `decide +kernel`)
  gives `execBlock L s mem = b.run s mem` for every state and memory.** The proof is in
  `Silmaril.Proofs.X86.Bir9` (one symbolic step per instruction, `Sound.lean`, `Block.lean`;
  the simplifier, `Simp.lean`).
* `runL9_eq_runB9`: the same on machine states.
* `E.simp_den`, `F.simp_den`, `Block.simp_run`: the simplifier keeps meanings.
* `LInstr.decodeOk_ext`, `LInstr.decodeOk_n9`: what `listingOk` checks.
* `block_reg`, `state_read`, `state_rip`, `state_flags`: reading a block's final state with
  `simp`.
* Kernel-checked examples (`decide +kernel`): the lifts of `div`, `cmov`, `cmp r/m8,imm8`,
  three-operand `imul` and `bsr`; decoder rejections of mutated listings; the `#DE` stop of
  a division by zero.

The bridge from Bir9 blocks to `Ext9` listings and `Open9` runs (`runX_eq_runB9`) is in
`Silmaril.X86.BlockCert9.Thms`.
-/

@[expose] public section

namespace Silmaril.X86.Bir9

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Sz RM Mem)
open Silmaril.Process (Memory)

/-- **The block simulation theorem**: if the symbolic executor accepts a listing, the
listing and the block agree on every entry state and memory. -/
theorem symExec_sound {instrs : List (LInstr × Nat)} {b : Block}
    (h : symExec instrs = some b) (s : XState) (mem : Memory) :
    execBlock instrs s mem = b.run s mem :=
  Silmaril.Proofs.X86.Bir9.symExec_sound h s mem

/-- **The lifter's certificate.** A listing whose lift the kernel computes to `b` runs as
`b` on every entry state and memory. -/
theorem liftBlock_sound {instrs : List (LInstr × Nat)} {b : Block}
    (h : liftBlock instrs = some b) (s : XState) (mem : Memory) :
    execBlock instrs s mem = b.run s mem :=
  Silmaril.Proofs.X86.Bir9.liftBlock_sound h s mem

/-- A lifted listing runs as its block, on machine states. -/
theorem runL9_eq_runB9 {L : List (LInstr × Nat)} {b : Block} (h : liftBlock L = some b)
    (m : MState) : runL9 L m = runB9 b m := by
  simp only [runL9, runB9, liftBlock_sound h]

theorem E.simp_den (env : Env) (e : E) : e.simp.den env = e.den env :=
  Silmaril.Proofs.X86.Bir9.E.simp_den env e

theorem F.simp_den (env : Env) (f : F) : f.simp.den env = f.den env :=
  Silmaril.Proofs.X86.Bir9.F.simp_den env f

theorem Block.simp_run (b : Block) (s : XState) (mem : Memory) :
    b.simp.run s mem = b.run s mem :=
  Silmaril.Proofs.X86.Bir9.Block.simp_run b s mem

/-! ## What the listing check checks -/

theorem LInstr.decodeOk_ext {bytes : List Byte} {i : Silmaril.X86.Ext.Instr} {len : Nat}
    (h : (LInstr.ext i).decodeOk bytes len = true) :
    Silmaril.X86.Ext.decode bytes = some (i, len) := by
  simpa [LInstr.decodeOk] using h

theorem LInstr.decodeOk_n9 {bytes : List Byte} {i : Ext9.New} {len : Nat}
    (h : (LInstr.n9 i).decodeOk bytes len = true) :
    Ext9.decode bytes = some (.new i, len) := by
  simpa [LInstr.decodeOk] using h

/-! ## Reading a block's final state (for `simp`) -/

theorem block_reg (b : Block) (r : Reg) : b.reg r = lookupE r b.regs := by
  unfold Block.reg
  generalize b.regs = l
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨a, e⟩ := p
    simp only [List.lookup_cons, lookupE]
    by_cases h : r = a
    · subst h; simp
    · have : (r == a) = false := by simpa using h
      simp [this, h, ih]

@[simp] theorem state_read (b : Block) (env : Env) (r : Reg) :
    (b.state env).core.read r = (lookupE r b.regs).den env := by
  simp [Block.state, Silmaril.X86.State.read, block_reg]

@[simp] theorem state_rip (b : Block) (env : Env) : (b.state env).core.rip = b.rip.den env := rfl

@[simp] theorem state_flags (b : Block) (env : Env) :
    (b.state env).core.flags = b.flags.den env := rfl

/-! ## Examples: lifts of the operator forms (`decide +kernel`) -/

/-- `xor %edx,%edx; div %ecx`. -/
def divListing : List (LInstr × Nat) :=
  [(.ext (.alu .d .xor (.reg .rdx) .rdx), 2), (.ext (.div .d false (.reg .rcx)), 2)]

theorem div_decodes : listingOk [[0x31, 0xd2], [0xf7, 0xf1]] divListing = true := by
  decide +kernel

/-- Its block: the `#DE` check, then `eax := q`, `edx := r` of `0:eax / ecx`. -/
def divBlock : Block :=
  let hi : E := .zext 32 (.alu 32 .xor (.reg .rdx) (.reg .rdx))
  { stmts := [.chk (.div .d false) hi (.reg .rax) (.reg .rcx)],
    regs := [(.rax, .xop (.divq .d false) hi (.reg .rax) (.reg .rcx)),
      (.rdx, .xop (.divr .d false) hi (.reg .rax) (.reg .rcx))],
    flags := .undef, rip := .add .rip (.imm 4) }

theorem div_lifts : liftBlock divListing = some divBlock := by decide +kernel

/-- `cmovle %edi,%eax`, as the `Ext` form. -/
theorem cmov_decodes : listingOk [[0x0f, 0x4e, 0xc7]] [(.ext (.cmov .d .le .rax (.reg .rdi)), 3)] =
    true := by decide +kernel

theorem cmov_lifts : (liftBlock [(.ext (.cmov .d .le .rax (.reg .rdi)), 3)]).isSome = true := by
  decide +kernel

/-- `cmpb $0x0,(%rdi)`. -/
theorem cmpI8_decodes :
    listingOk [[0x80, 0x3f, 0x00]]
      [(.ext (.cmpI8 (.mem (Mem.ofReg .rdi none 0x0)) 0), 3)] = true := by
  decide +kernel

theorem cmpI8_lifts : liftBlock [(.ext (.cmpI8 (.mem (Mem.ofReg .rdi none 0x0)) 0), 3)] =
    some
      { stmts := [.load 1 (.reg .rdi)], regs := [],
        flags := .alu 8 .cmp (.v 0) (.imm 0), rip := .add .rip (.imm 3) } := by
  decide +kernel

/-- `imul $0x1010101,%eax,%eax`. -/
theorem imulI_decodes :
    listingOk [[0x69, 0xc0, 0x01, 0x01, 0x01, 0x01]]
      [(.n9 (.imulI .d .rax (.reg .rax) 0x01010101), 6)] = true := by
  decide +kernel

theorem imulI_lifts : liftBlock [(.n9 (.imulI .d .rax (.reg .rax) 0x01010101), 6)] =
    some
      { stmts := [], regs := [(.rax, .mul 32 (.reg .rax) (.imm 0x01010101))],
        flags := .imul 32 (.reg .rax) (.imm 0x01010101), rip := .add .rip (.imm 6) } := by
  decide +kernel

/-- `bsr %edi,%eax`: the zero-source check, then the index. -/
theorem bsr_decodes :
    listingOk [[0x0f, 0xbd, 0xc7]] [(.n9 (.bsr .d .rax (.reg .rdi)), 3)] = true := by
  decide +kernel

theorem bsr_lifts : liftBlock [(.n9 (.bsr .d .rax (.reg .rdi)), 3)] =
    some
      { stmts := [.chk (.nz .d) (.reg .rdi) (.imm 0) (.imm 0)],
        regs := [(.rax, .xop (.bsr .d) (.reg .rdi) (.imm 0) (.imm 0))],
        flags := .xop .scan (.imm 0) (.imm 0) (.imm 0), rip := .add .rip (.imm 3) } := by
  decide +kernel

/-- `listingOk` rejects an `Ext9` entry whose immediate disagrees with the bytes. -/
theorem imulI_mutated_rejected :
    listingOk [[0x69, 0xc0, 0x01, 0x01, 0x01, 0x01]]
      [(.n9 (.imulI .d .rax (.reg .rax) 0x01010102), 6)] = false := by
  decide +kernel

/-- `listingOk` rejects a signed `idiv` entry for the bytes of an unsigned `div`. -/
theorem div_signed_rejected :
    listingOk [[0x31, 0xd2], [0xf7, 0xf1]]
      [(.ext (.alu .d .xor (.reg .rdx) .rdx), 2), (.ext (.div .d true (.reg .rcx)), 2)] =
      false := by
  decide +kernel

/-- `adc` is not lifted. -/
theorem adc_not_lifted : liftBlock [(.n9 (.adc .d false (.reg .rax) .rcx), 2)] = none := by
  decide +kernel

/-- `liftBlock` does not compute `divBlock` with the quotient and remainder swapped. -/
theorem div_swapped_rejected : liftBlock divListing ≠ some
    { divBlock with regs := divBlock.regs.map fun (r, e) => match e with
        | .xop (.divq sz s) a b c => (r, .xop (.divr sz s) a b c)
        | .xop (.divr sz s) a b c => (r, .xop (.divq sz s) a b c)
        | e => (r, e) } := by
  rw [div_lifts]; decide +kernel

/-- The `#DE` check is not vacuous: on a zero divisor the lifted `div` block stops with
`divideError` (and, by `liftBlock_sound`, so does the listing). -/
theorem divBlock_faults_on_zero (s : XState) (mem : Memory)
    (h : s.core.read .rcx = 0) : divBlock.run s mem = .divideError := by
  simp [divBlock, Block.run, runStmts, Stmt.run, COp.fault, E.den, h, Silmaril.X86.Ext.divide,
    Fault.toX]

end Silmaril.X86.Bir9

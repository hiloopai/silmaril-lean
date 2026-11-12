module

public import Silmaril.Raw.Libc.X86Alloc.MemStep

/-!
# Proofs: the instruction forms of rung 08 (boundary tags) on the canonical frame

Memory forms, from `c_rd`/`c_wr`: `cmp %src, m` (`c_cmpM`), `cmpb $imm, m` (`c_cmpB`),
`add m, %dst` (`c_addM`), `mov %src, m` for any operand `m` (`c_storeM`, e.g. with an index
register), `movb $imm, m` (`c_movI8M`), `movq $imm32, m` (`c_movIM`). Each takes the effective
address of `m` as a function of the frame's registers (`haddr`).

Register forms, from `c_whole`: `jcc rel32` (`c_jcc32_taken`, `c_jcc32_not`), `cmovcc`
(`c_cmov`), `op $imm32, %r` (`c_aluI`), `shr $c, %r` (`c_shr`), `mov $imm32, %r64`
(`c_movIQ`), `jmp rel32` (`c_jmp32`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.MemStep

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Ext (Mem Sz ShiftOp)
open Silmaril.Process (Memory)
open Silmaril.X86.Sep
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Whole

variable {σ : Type} {I : Isa σ}

theorem bytesPt_single (a : Nat) (v : Byte) : bytesPt a [v] = bytePt a v := by
  simp only [bytesPt, bytesAt, sep_emp]; rfl

theorem bytePt_blockAny (a : Nat) (v : Byte) : bytePt a v ⊢ₛ blockAny a 1 := by
  rw [← bytesPt_single]; exact bytesPt_blockAny a [v]

theorem leBytes_one (x : BitVec 8) : Silmaril.X86.Ext.leBytes (x.setWidth 64) 1 = [x] := by
  simp only [Silmaril.X86.Ext.leBytes, List.ofFn_succ, List.ofFn_zero,
    Silmaril.Machine.LittleEndian.wordByte, Fin.val_zero, Nat.mul_zero, BitVec.ushiftRight_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem loadN_word {mem : Memory} {A : Word} {a : Nat} {w : Word} (hA : A.toNat = a)
    (h : mem.readBytes a (Silmaril.Machine.LittleEndian.encodeWords [w]).length =
      some (Silmaril.Machine.LittleEndian.encodeWords [w])) :
    Silmaril.X86.Ext.loadN mem A 8 = some w := by
  have hl : (Silmaril.Machine.LittleEndian.encodeWords [w]).length = 8 := by
    rw [← Silmaril.X86.Ext.leBytes_eight, Silmaril.X86.Ext.length_leBytes]
  rw [hl] at h
  simp only [Silmaril.X86.Ext.loadN, hA, h, Option.map_some, Option.some.injEq]
  rw [← Silmaril.X86.Ext.leBytes_eight, Silmaril.X86.Ext.leValue_leBytes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := w.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem loadN_byte {mem : Memory} {A : Word} {a : Nat} {v : Byte} (hA : A.toNat = a)
    (h : mem.readBytes a [v].length = some [v]) :
    Silmaril.X86.Ext.loadN mem A 1 = some (v.setWidth 64) := by
  simp only [Silmaril.X86.Ext.loadN, hA, List.length_singleton] at h ⊢
  rw [h]
  simp only [Option.map_some, Option.some.injEq, Silmaril.X86.Ext.leValue]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have := v.isLt
  omega

section Forms

variable (E : Silmaril.X86.Open.isa.Extends I) {b : Nat} {code : List Byte} {o k : Nat}
  {pc : Word} (hpc : pc.toNat = b + o) (hfit : o + k ≤ code.length)

include E hpc hfit

/-- `cmp %src, m` (64-bit), `m` the owned word. -/
theorem c_cmpM {src : Reg} (hs : src ∈ frameRegs) {mo : Mem} {a : Nat} {w : Word}
    {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.alu .q .cmp (.mem mo) src, k))
    (haddr : ∀ s : State, (∀ q ∈ frameRegs, s.read q = f q) → ∀ next, (mo.addr s next).toNat = a) :
    SPEC I (codePt b code) (St pc f fl (wordPt a w ∗ M))
      (St (pc + BitVec.ofNat 64 k) f (Silmaril.X86.Ext.AluOp.flagsN .cmp w (f src))
        (wordPt a w ∗ M)) := by
  have hl := dec_len hfit hdec
  refine c_rd E hpc hfit (by simp [Silmaril.Machine.LittleEndian.encodeWords]) hdec (by simp)
    fun s mem hrip hregs _ hrd => ⟨{ s with flags := (Silmaril.X86.Ext.AluOp.flagsN .cmp w (f src)), rip := (pc + BitVec.ofNat 64 k) },
      ?_, rfl, hregs, fun _ _ => rfl, rfl⟩
  have hload := loadN_word (A := mo.addr s (s.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.length
    (.alu .q .cmp (.mem mo) src)))) (haddr s hregs _) hrd
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
    Sz.bytes, hload, Option.map_some, ite_true, Silmaril.X86.Ext.retire, Sz.bits, Sz.read_q, hregs src hs,
    BitVec.setWidth_eq]
  rw [hrip, ← hl]

/-- `cmpb $imm, m`, `m` the owned byte. -/
theorem c_cmpB {mo : Mem} {a : Nat} {v imm : Byte} {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.cmpI8 (.mem mo) imm, k))
    (haddr : ∀ s : State, (∀ q ∈ frameRegs, s.read q = f q) → ∀ next, (mo.addr s next).toNat = a) :
    SPEC I (codePt b code) (St pc f fl (bytePt a v ∗ M))
      (St (pc + BitVec.ofNat 64 k) f (Silmaril.X86.Ext.subFlagsN v imm) (bytePt a v ∗ M)) := by
  have hl := dec_len hfit hdec
  rw [← bytesPt_single]
  refine c_rd E hpc hfit (by simp) hdec (by simp)
    fun s mem hrip hregs _ hrd => ⟨{ s with flags := (Silmaril.X86.Ext.subFlagsN v imm), rip := (pc + BitVec.ofNat 64 k) },
      ?_, rfl, hregs, fun _ _ => rfl, rfl⟩
  have hload := loadN_byte (A := mo.addr s (s.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.length
    (.cmpI8 (.mem mo) imm)))) (haddr s hregs _) hrd
  have hv : (v.setWidth 64).setWidth 8 = v := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; have := v.isLt; omega
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.Narrow.bytes,
    Silmaril.X86.Ext.Narrow.bits, hload, Option.map_some, Silmaril.X86.Ext.retire, hv]
  rw [hrip, ← hl]

/-- `op m, %dst` (64-bit, not `cmp`), `m` the owned word. -/
theorem c_aluM {op : Silmaril.X86.AluOp} (hop : op ≠ .cmp) {dst : Reg} (hd : dst ∈ frameRegs)
    {mo : Mem} {a : Nat} {w : Word} {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.aluR .q op dst (.mem mo), k))
    (haddr : ∀ s : State, (∀ q ∈ frameRegs, s.read q = f q) → ∀ next, (mo.addr s next).toNat = a) :
    SPEC I (codePt b code) (St pc f fl (wordPt a w ∗ M))
      (St (pc + BitVec.ofNat 64 k)
        (Function.update f dst (Silmaril.X86.Ext.AluOp.resultN op (f dst) w))
        (Silmaril.X86.Ext.AluOp.flagsN op (f dst) w) (wordPt a w ∗ M)) := by
  have hl := dec_len hfit hdec
  refine c_rd E hpc hfit (by simp [Silmaril.Machine.LittleEndian.encodeWords]) hdec (by simp)
    fun s mem hrip hregs _ hrd => ⟨{ (Sz.q.write s dst (Silmaril.X86.Ext.AluOp.resultN op (f dst) w)) with flags := (Silmaril.X86.Ext.AluOp.flagsN op (f dst) w), rip := (pc + BitVec.ofNat 64 k) },
      ?_, rfl, ?_, ?_, rfl⟩
  · have hload := loadN_word (A := mo.addr s (s.rip + BitVec.ofNat 64
      (Silmaril.X86.Ext.Instr.length (.aluR .q op dst (.mem mo))))) (haddr s hregs _) hrd
    simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.readRM,
      Sz.bytes, hload, Option.map_some, hop, ite_false, Silmaril.X86.Ext.retire, Sz.bits, Sz.read_q,
      hregs dst hd, BitVec.setWidth_eq]
    rw [hrip, ← hl]
  · intro q hq
    show (Sz.q.write s dst _).read q = _
    by_cases e : q = dst
    · subst e; simp
    · simp [Sz.write, e, hregs q hq]
  · intro q hq
    show (Sz.q.write s dst _).read q = _
    have : q ≠ dst := fun e => hq (e ▸ hd)
    simp [Sz.write, this]

/-- `mov %src, m` (64-bit) into the owned block `B`, for any memory operand `m`. -/
theorem c_storeM {src : Reg} (hs : src ∈ frameRegs) {mo : Mem} {a : Nat}
    {f : Reg → Word} {fl : Flags} {B M : SProp} (hB : B ⊢ₛ blockAny a 8)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.mov .q (.mem mo) src, k))
    (haddr : ∀ s : State, (∀ q ∈ frameRegs, s.read q = f q) → ∀ next, (mo.addr s next).toNat = a) :
    SPEC I (codePt b code) (St pc f fl (B ∗ M))
      (St (pc + BitVec.ofNat 64 k) f fl (wordPt a (f src) ∗ M)) := by
  have hl := dec_len hfit hdec
  have h : SPEC I (codePt b code) (St pc f fl (blockAny a 8 ∗ M))
      (St (pc + BitVec.ofNat 64 k) f fl (bytesPt a (Silmaril.X86.Ext.leBytes (f src) 8) ∗ M)) := by
    refine c_wr E hpc hfit (by decide) hdec (by simp) fun s mem hrip hregs hfl =>
      ⟨mo.addr s (s.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.length
        (.mov .q (.mem mo) src))), haddr s hregs _, { s with rip := pc + BitVec.ofNat 64 k },
        fun after hst => ?_, rfl, hregs, fun _ _ => rfl, hfl⟩
    simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM, Sz.bytes, Sz.read_q, Sz.bits,
      BitVec.setWidth_eq, hregs src hs, hst, Option.map_some, Silmaril.X86.Ext.retire]
    rw [hrip, ← hl]
  refine SPEC.conseq (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
    (sep_mono_left _ hB)))) h (entails_of_eq ?_)
  rw [Silmaril.X86.Ext.leBytes_eight]; rfl

/-- `movb $imm, m` into the owned byte `B`. -/
theorem c_movI8M {mo : Mem} {a : Nat} {imm : Byte}
    {f : Reg → Word} {fl : Flags} {B M : SProp} (hB : B ⊢ₛ blockAny a 1)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.movI8 (.mem mo) imm, k))
    (haddr : ∀ s : State, (∀ q ∈ frameRegs, s.read q = f q) → ∀ next, (mo.addr s next).toNat = a) :
    SPEC I (codePt b code) (St pc f fl (B ∗ M))
      (St (pc + BitVec.ofNat 64 k) f fl (bytePt a imm ∗ M)) := by
  have hl := dec_len hfit hdec
  have h : SPEC I (codePt b code) (St pc f fl (blockAny a 1 ∗ M))
      (St (pc + BitVec.ofNat 64 k) f fl (bytesPt a (Silmaril.X86.Ext.leBytes (imm.setWidth 64) 1) ∗ M)) := by
    refine c_wr E hpc hfit (by decide) hdec (by simp) fun s mem hrip hregs hfl =>
      ⟨mo.addr s (s.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.length
        (.movI8 (.mem mo) imm))), haddr s hregs _, { s with rip := pc + BitVec.ofNat 64 k },
        fun after hst => ?_, rfl, hregs, fun _ _ => rfl, hfl⟩
    simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM8, hst, Option.map_some,
      Silmaril.X86.Ext.retire]
    rw [hrip, ← hl]
  refine SPEC.conseq (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
    (sep_mono_left _ hB)))) h (entails_of_eq ?_)
  rw [leBytes_one, bytesPt_single]

/-- `movq $imm32, m` (sign-extended) into the owned block `B`. -/
theorem c_movIM {mo : Mem} {a : Nat} {imm : BitVec 32}
    {f : Reg → Word} {fl : Flags} {B M : SProp} (hB : B ⊢ₛ blockAny a 8)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.movI .q (.mem mo) imm, k))
    (haddr : ∀ s : State, (∀ q ∈ frameRegs, s.read q = f q) → ∀ next, (mo.addr s next).toNat = a) :
    SPEC I (codePt b code) (St pc f fl (B ∗ M))
      (St (pc + BitVec.ofNat 64 k) f fl (wordPt a (imm.signExtend 64) ∗ M)) := by
  have hl := dec_len hfit hdec
  have h : SPEC I (codePt b code) (St pc f fl (blockAny a 8 ∗ M))
      (St (pc + BitVec.ofNat 64 k) f fl (bytesPt a (Silmaril.X86.Ext.leBytes (imm.signExtend 64) 8) ∗ M)) := by
    refine c_wr E hpc hfit (by decide) hdec (by simp) fun s mem hrip hregs hfl =>
      ⟨mo.addr s (s.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.length
        (.movI .q (.mem mo) imm))), haddr s hregs _, { s with rip := pc + BitVec.ofNat 64 k },
        fun after hst => ?_, rfl, hregs, fun _ _ => rfl, hfl⟩
    simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM, Sz.bytes, BitVec.setWidth_eq,
      Sz.bits, hst, Option.map_some, Silmaril.X86.Ext.retire]
    rw [hrip, ← hl]
  refine SPEC.conseq (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
    (sep_mono_left _ hB)))) h (entails_of_eq ?_)
  rw [Silmaril.X86.Ext.leBytes_eight]; rfl

/-! ## Register forms -/

/-- A taken `jcc rel32`. -/
theorem c_jcc32_taken {c : Silmaril.X86.Ext.Cond} {rel : BitVec 32} {f : Reg → Word} {fl : Flags}
    {M : SProp} {pc' : Word} (hev : c.eval fl = some true)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.jcc c rel, k))
    (hnext : pc + BitVec.ofNat 64 k + rel.signExtend 64 = pc') :
    SPEC I (codePt b code) (St pc f fl M) (St pc' f fl M) := by
  have hl := dec_len hfit hdec
  refine c_whole E hpc hfit hdec (by simp) fun s mem hrip hregs hfl =>
    ⟨{ s with rip := pc' }, ?_, rfl, hregs, fun _ _ => rfl, hfl⟩
  simp only [Silmaril.X86.Ext.exec, hfl, hev]
  rw [hrip, ← hl, hnext]

/-- A `jcc rel32` that falls through. -/
theorem c_jcc32_not {c : Silmaril.X86.Ext.Cond} {rel : BitVec 32} {f : Reg → Word} {fl : Flags}
    {M : SProp} (hev : c.eval fl = some false)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.jcc c rel, k)) :
    SPEC I (codePt b code) (St pc f fl M) (St (pc + BitVec.ofNat 64 k) f fl M) := by
  have hl := dec_len hfit hdec
  refine c_whole E hpc hfit hdec (by simp) fun s mem hrip hregs hfl =>
    ⟨{ s with rip := pc + BitVec.ofNat 64 k }, ?_, rfl, hregs, fun _ _ => rfl, hfl⟩
  simp only [Silmaril.X86.Ext.exec, hfl, hev]
  rw [hrip, ← hl]

/-- `jmp rel32`. -/
theorem c_jmp32 {rel : BitVec 32} {f : Reg → Word} {fl : Flags} {M : SProp} {pc' : Word}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.jmp rel, k))
    (hnext : pc + BitVec.ofNat 64 k + rel.signExtend 64 = pc') :
    SPEC I (codePt b code) (St pc f fl M) (St pc' f fl M) := by
  have hl := dec_len hfit hdec
  refine c_whole E hpc hfit hdec (by simp) fun s mem hrip hregs hfl => ⟨_, rfl, ?_, ?_, ?_, hfl⟩
  · show s.rip + _ + _ = _; rw [hrip, ← hl, hnext]
  · exact hregs
  · intro q _; rfl

/-- `cmovcc %src, %dst` (64-bit). -/
theorem c_cmov {c : Silmaril.X86.Ext.Cond} {dst src : Reg} (hd : dst ∈ frameRegs)
    (hs : src ∈ frameRegs) {t : Bool} {f : Reg → Word} {fl : Flags} {M : SProp}
    (hev : c.eval fl = some t)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.cmov .q c dst (.reg src), k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) (Function.update f dst (if t then f src else f dst)) fl M) := by
  have hl := dec_len hfit hdec
  refine c_whole E hpc hfit hdec (by simp) fun s mem hrip hregs hfl =>
    ⟨{ Sz.q.write s dst (if t then f src else f dst) with rip := pc + BitVec.ofNat 64 k },
      ?_, rfl, ?_, ?_, hfl⟩
  · simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM, hfl, hev, Sz.read_q,
      hregs src hs, hregs dst hd, Silmaril.X86.Ext.retire]
    rw [hrip, ← hl]
  · intro q hq
    show (Sz.q.write s dst _).read q = _
    by_cases e : q = dst
    · subst e; simp
    · simp [Sz.write, e, hregs q hq]
  · intro q hq
    show (Sz.q.write s dst _).read q = _
    have : q ≠ dst := fun e => hq (e ▸ hd)
    simp [Sz.write, this]

/-- `op $imm32, %r` (64-bit, not `cmp`). -/
theorem c_aluI {op : Silmaril.X86.AluOp} (hop : op ≠ .cmp) {r : Reg} (hr : r ∈ frameRegs)
    {imm : BitVec 32} {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.aluI .q op (.reg r) imm, k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k)
        (Function.update f r (Silmaril.X86.Ext.AluOp.resultN op (f r) (imm.signExtend 64)))
        (Silmaril.X86.Ext.AluOp.flagsN op (f r) (imm.signExtend 64)) M) :=
  c_reg1 E hpc hfit hr hdec (by simp) rfl fun s mem h1 =>
    ⟨_, by simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire, hop]; rfl, rfl, by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
        Silmaril.X86.Ext.writeRM, hop, h1],
      fun t ht => by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
        Silmaril.X86.Ext.writeRM, hop, ht],
      by simp [Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, hop,
        h1]⟩

/-- `shr $c, %r` (64-bit). -/
theorem c_shr {r : Reg} (hr : r ∈ frameRegs) {c : BitVec 8} (hc : c.toNat % 64 ≠ 0)
    {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (.shift .q .shr (.reg r) (.imm c), k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) (Function.update f r (ShiftOp.shr.result (f r) (c.toNat % 64)))
        (ShiftOp.shr.flags (f r) (c.toNat % 64) fl) M) := by
  refine c_reg1 E hpc hfit hr hdec (by simp) rfl (f := f) (fl := fl) fun s mem h1 =>
    ⟨_, rfl, rfl, by simp [Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM,
        Silmaril.X86.Ext.Count.raw, h1],
      fun t ht => by simp [Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, ht], ?_⟩
  simp only [Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Sz.read_q, h1, Option.map_some]
  simp [ShiftOp.flags, hc, Silmaril.X86.Ext.Count.raw]; rfl

/-- `mov $imm32, %r64` (sign-extended). -/
theorem c_movIQ {r : Reg} (hr : r ∈ frameRegs) {imm : BitVec 32} {f : Reg → Word} {fl : Flags}
    {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.movI .q (.reg r) imm, k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) (Function.update f r (imm.signExtend 64)) fl M) := by
  have hl := dec_len hfit hdec
  refine c_whole E hpc hfit hdec (by simp) fun s mem hrip hregs hfl =>
    ⟨{ Sz.q.write s r (imm.signExtend 64) with rip := pc + BitVec.ofNat 64 k }, ?_, rfl, ?_, ?_,
      hfl⟩
  · simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire]
    rw [hrip, ← hl]; rfl
  · intro q hq
    show (Sz.q.write s r _).read q = _
    by_cases e : q = r
    · subst e; simp
    · simp [Sz.write, e, hregs q hq]
  · intro q hq
    show (Sz.q.write s r _).read q = _
    have : q ≠ r := fun e => hq (e ▸ hr)
    simp [Sz.write, this]

end Forms

end Silmaril.Raw.Libc.X86Alloc.MemStep

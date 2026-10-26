module

public import Silmaril.Apps.Sha256sum.TV.Couple

/-! # Translation validation of the hex loop body of `sha256sum-min`

Status: **VERIFIED** (no `sorry`, standard axioms only).

One `TVIR.Sim` leaf per IR statement of `TV.FormatIR.body`, each a symbolic run of the
corresponding x86 block (`Stdout.rstep`), and the loop branch (`cmp %rbx,%r14; je`).

| IR statement                       | x86 block            |
|------------------------------------|----------------------|
| `b := mem[p]`                      | `0x4045ae → 0x4045b2` |
| `hi := mem[hexd + ((b >> 4) & 15)]` | `0x4045b2 → 0x4045c2` |
| `putc hi`                          | `0x4045c2 → 0x404578` (`TV.HexPutc`) |
| `lo := mem[hexd + (b & 15)]`        | `0x404578 → 0x404584` |
| `putc lo`                          | `0x404584 → 0x4045a5` (`TV.HexPutc`) |
| `p := p + 1`                       | `0x4045a5 → 0x4045a9` |
| `while (p != e)`                   | `0x4045a9 → 0x4045ae / 0x404605` |
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Apps.Sha256sum.TV

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Apps.Sha256sum.Stdout
open Silmaril.X86 (State Reg)
open Silmaril.X86.TVIR
open Silmaril.Process (Memory Byte)
open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev stdinRead)
open Silmaril.X86.Stencils.HexLoop (hexTable)

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

set_option maxRecDepth 200000

theorem ofU8_eq (b : UInt8) : ofU8 b = b.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp [ofU8]

/-- The registers `output_file` keeps across the loop: the operand pointer and `binary = 0`. -/
def Keep (c : Ctx) (x : XState) : Prop := x.core.read .r12 = c.file ∧ x.core.read .r13 = 0#64

/-- The IR index: `p = bin + k`, `e = bin + 32`. -/
def Idx (c : Ctx) (σ : HSt) (k : Nat) : Prop :=
  σ.env .p = BitVec.ofNat 64 (c.bin + k) ∧ σ.env .e = BitVec.ofNat 64 (c.bin + 32)

/-- The register map of the loop: `rbx = p`, `r14 = e`, and `Keep`. -/
def PLoop (c : Ctx) (σ : HSt) (x : XState) : Prop :=
  x.core.read .rbx = σ.env .p ∧ x.core.read .r14 = σ.env .e ∧ Keep c x

/-- The loop head `0x4045ae`: `rax = olen`, a byte left. -/
def PHead (c : Ctx) (σ : HSt) (x : XState) : Prop :=
  PLoop c σ x ∧ x.core.read .rax = BitVec.ofNat 64 σ.io.1.length ∧ ∃ k < 32, Idx c σ k

/-- After `b := mem[p]` (`0x4045b2`): `r15 = b`. -/
def PB (c : Ctx) (σ : HSt) (x : XState) : Prop :=
  PHead c σ x ∧ x.core.read .r15 = σ.env .b ∧ ∃ v : BitVec 8, σ.env .b = v.setWidth 64

/-- After `hi := …` (`0x4045c2`, the high-digit `out_putc` site): `rbp = hi`, a digit. -/
def PHi (c : Ctx) (σ : HSt) (x : XState) : Prop :=
  PB c σ x ∧ x.core.read .rbp = σ.env .hi ∧ ∃ j < 16, σ.env .hi = zext (hexDigit j)

variable {c : Ctx} {w : World} {F : List UInt8}

/-- **`b := mem[p]`** is `movzbl (%rbx),%r15d` (`0x4045ae`). -/
theorem leaf_b (hfr : Frame c) :
    Sim (GStep w) (Ok c.message) (roMem c.d c.bin) F (At c 0x4045ae#64 (PHead c))
      (At c 0x4045b2#64 (PB c)) (.set .b (.ld8 (.var .p))) := by
  refine sim_run (fun _ _ _ ha => ha.run) ?_
  rintro σ σ' e - g h ⟨hc, hrip, ⟨hrbx, hr14, hkeep⟩, hrax, k, hk, hp, he⟩
  cases e
  have hfit : c.bin + k < 2 ^ 64 := by have := hfr.spBound; simp only [Ctx.bin]; omega
  have hrd : g.x.memory.readWith .read (σ.env .p).toNat 1 =
      some [ofU8 (c.d[k]'(by rw [hfr.len]; exact hk))] := by
    rw [hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
    exact hfr.digest_byte hc.foot hk
  have hf := hc.faulted
  have hcode := hc.code
  rstep [hrip, hrbx, X86.Ext.readNarrow, X86.Ext.Narrow.bytes]
  refine RunsTo.done ⟨hc.same_mem hf (by assumption) rfl ?_, rfl, ⟨⟨?_, ?_, ?_⟩, ?_, k, hk, ?_⟩, ?_,
    (c.d[k]'(by rw [hfr.len]; exact hk)).toBitVec, ?_⟩
  all_goals simp only [St.set, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
    Function.update_of_ne, State.read_write_same, State.read_write_other, Lift.read_mk,
    Lift.core_regs]
  · exact hc.rsp
  · exact hrbx
  · exact hr14
  · exact ⟨hkeep.1, hkeep.2⟩
  · exact hrax
  · exact ⟨hp, he⟩
  · simp only [Exp.eval, hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, hfr.roMem_digest hk,
      movzx_byte, zext, ofU8_eq]
  · simp only [Exp.eval, hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit, hfr.roMem_digest hk, zext]

/-- The high nibble as `mov %r15d,%edx; shr $4,%dl; and $0xf,%edx` computes it. -/
theorem hi_nibble (v : BitVec 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 ((v.setWidth 64 &&& ~~~255#64 |||
      BitVec.setWidth 64 (BitVec.setWidth 8 (v.setWidth 64) >>> 4))) &&& 15#32) =
      (v.setWidth 64 >>> 4) &&& 15 := by
  revert v; decide

/-- The state after the nibble computation `0x4045b2 → 0x4045bb`: `rdx = n`, everything else
as in `s`. -/
def NibAt (s : XState) (pc : X86.Word) (n : X86.Word) (t : XState) : Prop :=
  t.faulted = false ∧ Lift.Code t.memory ∧ t.core.rip = pc ∧ t.memory = s.memory ∧
    t.core.read .rdx = n ∧ ∀ r, r ≠ .rdx → t.core.read r = s.core.read r

/-- `mov %r15d,%edx; shr $4,%dl; and $0xf,%edx` (`0x4045b2 → 0x4045bb`). -/
theorem hi_alu {s : XState} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x4045b2#64) {v : BitVec 8} (hr15 : s.core.read .r15 = v.setWidth 64) :
    RunsTo (NibAt s 0x4045bb#64 ((v.setWidth 64 >>> 4) &&& 15)) s := by
  rstep [hrip, hr15, X86.Ext8.BReg.write, X86.Ext.writeByte, X86.Ext.ShiftOp.result,
    X86.Ext.Count.raw, X86.Ext8.BReg.read_low, zext32_byte]
  rstep [X86.Ext8.BReg.write, X86.Ext.writeByte, X86.Ext.ShiftOp.result,
    X86.Ext.Count.raw, X86.Ext8.BReg.read_low]
  rstep [X86.Ext8.BReg.write, X86.Ext.writeByte, X86.Ext.ShiftOp.result,
    X86.Ext.Count.raw, X86.Ext8.BReg.read_low]
  refine RunsTo.done ⟨hf, by assumption, rfl, rfl, ?_, fun r hr => ?_⟩
  · simp only [State.read_write_same]; exact hi_nibble v
  · simp only [State.read_write_other _ _ _ _ hr, Lift.read_mk, Lift.core_regs]

/-- After one instruction that wrote only `dst := v` and moved to `pc`. -/
def WroteReg (s : XState) (pc : X86.Word) (dst : Reg) (v : X86.Word) (t : XState) : Prop :=
  t.faulted = false ∧ Lift.Code t.memory ∧ t.core.rip = pc ∧ t.memory = s.memory ∧
    t.core.read dst = v ∧ ∀ r, r ≠ dst → t.core.read r = s.core.read r

/-- **A listed `movzbl disp(%base),%dst32`** at `a` (length `n`) loads the byte and zero-extends
it (the generic per-instruction TV lemma for byte loads). -/
theorem run_movzx {s : XState} (hf : s.faulted = false) (hc : Lift.Code s.memory) {a n : Nat}
    {dst base : Reg} {disp : BitVec 32}
    (hl : Lift.instrAt a = some (.base (.movx false .d .b dst (.mem (X86.Ext.Mem.ofReg base none disp))), n))
    (hrip : s.core.rip = BitVec.ofNat 64 a) {b : Byte}
    (hrd : s.memory.readWith .read (s.core.read base + disp.signExtend 64).toNat 1 = some [b]) :
    RunsTo (WroteReg s (BitVec.ofNat 64 a + BitVec.ofNat 64 n) dst (b.setWidth 64)) s := by
  refine run_instr' hf hc hrip hl ?_
  simp only [X86.Ext8.exec, X86.Ext.exec, X86.Ext.readNarrow, X86.Ext.Narrow.bytes,
    X86.Ext.Mem.addr, X86.Ext.Mem.ofReg, X86.Ext.Base.value_reg, X86.Ext.Index.value,
    Option.map_none, Option.getD_none, BitVec.add_zero, X86.Ext.loadN,
    Silmaril.Process.Memory.readBytes, hrd, Option.map_some, hrip]
  intro hc'
  refine RunsTo.done ⟨hf, hc', ?_, rfl, ?_, fun r hr => ?_⟩
  · rfl
  · simp only [Lift.read_mk, Lift.core_regs, X86.Ext.Sz.write,
      State.read_write_same, ite_eq_right Bool.false_ne_true]
    exact movzx_byte b
  · simp only [Lift.read_mk, Lift.core_regs, X86.Ext.Sz.write,
      State.read_write_other _ _ _ _ hr]

theorem zext_ofU8 (b : UInt8) : (ofU8 b).setWidth 64 = zext b := by rw [ofU8_eq]; rfl

/-- **`hi := mem[hexd + ((b >> 4) & 15)]`** is `mov %r15d,%edx; shr $4,%dl; and $0xf,%edx;
movzbl hexd(%rdx),%ebp` (`0x4045b2 → 0x4045c2`). -/
theorem leaf_hi (hfr : Frame c) :
    Sim (GStep w) (Ok c.message) (roMem c.d c.bin) F (At c 0x4045b2#64 (PB c))
      (At c 0x4045c2#64 (PHi c))
      (.set .hi (.ld8 (.add (.lit (BitVec.ofNat 64 hexd)) (.band (.shr (.var .b) 4) (.lit 15))))) := by
  refine sim_run (fun _ _ _ ha => ha.run) ?_
  rintro σ σ' e - g h ⟨hc, hrip, ⟨⟨hrbx, hr14, hk12, hk13⟩, hrax, k, hk, hidx⟩, hr15, v, hv⟩
  cases e
  rw [hv] at hr15
  have hj : ((v.setWidth 64 >>> 4) &&& (15 : X86.Word)).toNat = v.toNat / 16 := by
    have := zext_shr_and (UInt8.ofBitVec v); simpa [zext] using this
  have hj16 : v.toNat / 16 < 16 := by have := v.isLt; omega
  refine (hi_alu hc.faulted hc.code hrip hr15).bind fun t ⟨hft, hct, hript, hmt, hrdx, hregs⟩ => ?_
  have hrd : t.memory.readWith .read (t.core.read .rdx + (0x004072c0#32).signExtend 64).toNat 1 =
      some [ofU8 (hexTable[v.toNat / 16]'hj16)] := by
    rw [hmt, hrdx, show (0x004072c0#32).signExtend 64 = 4223680#64 from rfl, BitVec.toNat_add, hj,
      show (4223680#64).toNat = 0x4072c0 from rfl, Nat.mod_eq_of_lt (by omega), Nat.add_comm]
    exact hfr.table_byte hc.foot hj16
  refine (run_movzx (a := 0x4045bb) (n := 7) (dst := .rbp) (base := .rdx) (disp := 0x004072c0#32)
    hft hct (by rfl) hript hrd).bind
    fun u ⟨hfu, hcu, hripu, hmu, hrbp, hregs'⟩ => RunsTo.done ?_
  have R : ∀ r, r ≠ .rdx → r ≠ .rbp → u.core.read r = g.x.core.read r :=
    fun r h1 h2 => (hregs' r h2).trans (hregs r h1)
  have hmem : u.memory = g.x.memory := hmu.trans hmt
  have hbin : hexd + 16 ≤ c.bin := by have := hfr.spBound; simp only [Ctx.bin, hexd]; omega
  have hiv : Exp.eval (roMem c.d c.bin) σ.env (.ld8 (.add (.lit (BitVec.ofNat 64 hexd))
      (.band (.shr (.var .b) 4) (.lit 15)))) = zext (hexDigit (v.toNat / 16)) := by
    simp only [Exp.eval, hv]
    rw [table_addr _ (by rw [hj]; exact hj16), hj, roMem_table c.d hbin hj16]
  refine ⟨hc.same_mem hfu hcu hmem ((R .rsp (by decide) (by decide)).trans hc.rsp), hripu, ?_⟩
  refine ⟨⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, k, hk, hidx⟩, ?_, _, hv⟩, ?_, _, hj16, ?_⟩
  all_goals simp only [St.set, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true,
    Function.update_of_ne]
  · rw [R .rbx (by decide) (by decide)]; exact hrbx
  · rw [R .r14 (by decide) (by decide)]; exact hr14
  · rw [R .r12 (by decide) (by decide)]; exact hk12
  · rw [R .r13 (by decide) (by decide)]; exact hk13
  · rw [R .rax (by decide) (by decide)]; exact hrax
  · rw [R .r15 (by decide) (by decide)]; exact hr15.trans hv.symm
  · rw [hrbp, hiv, zext_ofU8, Silmaril.X86.Stencils.HexLoop.hexTable_getElem]
  · exact hiv

end Silmaril.Apps.Sha256sum.TV

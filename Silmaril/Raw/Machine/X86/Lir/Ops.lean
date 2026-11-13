module

public import Silmaril.Machine.X86.Lir.LinMem.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-!
# Selected operations on the machine

For every supported Lir operator, the selected instruction sequence runs to
completion (`runSeq` succeeds), writes the Lir result to the destination
register and changes no other register except the scratch registers `rax rcx
rdx r11` (`Keeps`). The sources may alias the destination.

* Comparisons: the flags SETcc reads are those of the immediately preceding
  CMP, so every tested condition is defined (`eval_after_cmp_q`/`_d`), and it
  is the Lir comparison (`ofLir_afterCmp`).
* Division: DIV and IDIV are only executed on operands for which Lir division
  is defined (nonzero divisor, and no `intMin / -1` for the signed forms), and
  on exactly those operands they do not raise `#DE` (`divide_unsigned`,
  `divide_signed`), so `exec` retires (`run_selDiv_q`, `run_selDiv_d`).
* Loads and stores: `run_selLoad` and `run_selStore` relate the access to
  `[r15 + r11]` with the Lir access through `MemRel`.
* Bit counts: LZCNT, TZCNT and POPCNT of the model count as `BitVec.clz`,
  `ctz` and `cpop` (`clz_eq`, `ctz_eq`, `cpop_eq`).
* High products: `mulhuCore` computes `Lir.mulHigh false` from four 32-bit
  partial products (`mulhu_gen`, `mulhuVal_eq`), and `mulhsFix` corrects it to
  `Lir.mulHigh true` (`mulHigh_true`).
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State Word Byte Reg Flags AluOp)
open Silmaril.Machine

@[simp] theorem read_rip (s : State) (v : Word) (r : Reg) : ({ s with rip := v } : State).read r = s.read r := rfl
@[simp] theorem read_flags_rip (s : State) (f : Flags) (v : Word) (r : Reg) :
  ({ s with flags := f, rip := v } : State).read r = s.read r := rfl
@[simp] theorem flags_rip (s : State) (v : Word) : ({ s with rip := v } : State).flags = s.flags := rfl
@[simp] theorem rip_rip (s : State) (v : Word) : ({ s with rip := v } : State).rip = v := rfl
@[simp] theorem d_read (s : State) (r : Reg) : Ext.Sz.d.read s r = (s.read r).setWidth 32 := rfl
@[simp] theorem d_write (s : State) (r : Reg) (v : BitVec 32) : Ext.Sz.d.write s r v = s.write r (v.setWidth 64) := rfl
/-- `s'` agrees with `s` on every non-scratch register other than `d`. -/
def Keeps (s s' : State) (d : Reg) : Prop := ∀ r, ¬ Scratch r → r ≠ d → s'.read r = s.read r

theorem not_scratch_iff (r : Reg) :
    ¬ Scratch r ↔ r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r11 := by
  simp [Scratch]

/-! ## Register-only operations -/

/-! ## 64-bit forms without the size views -/

theorem exec_mov_q (s : State) (m : Memory) (dst src : Reg) :
    Ext.exec (.mov .q (.reg dst) src) s m =
      .ok { s.write dst (s.read src) with
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.mov .q (.reg dst) src).length } m := rfl

theorem exec_alu_q (s : State) (m : Memory) (op : AluOp) (dst src : Reg) (h : op ≠ .cmp) :
    Ext.exec (.alu .q op (.reg dst) src) s m =
      .ok { s.write dst (Ext.AluOp.resultN op (s.read dst) (s.read src)) with
        flags := Ext.AluOp.flagsN op (s.read dst) (s.read src)
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.alu .q op (.reg dst) src).length } m := by
  rw [Ext.exec_alu_reg _ _ _ _ _ _ h]; rfl

theorem exec_cmpI_q (s : State) (m : Memory) (dst : Reg) (imm : BitVec 32) :
    Ext.exec (.aluI .q .cmp (.reg dst) imm) s m =
      .ok { s with
        flags := Ext.subFlagsN (s.read dst) (imm.signExtend 64)
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.aluI .q .cmp (.reg dst) imm).length } m := by
  rw [Ext.exec_cmpI_reg]; rfl

theorem exec_div_ok (sz : Ext.Sz) (signed : Bool) (src : Reg) (s : State) (m : Memory)
    {q r : BitVec sz.bits}
    (h : Ext.divide sz signed (sz.read s .rdx) (sz.read s .rax) (sz.read s src) = some (q, r)) :
    Ext.exec (.div sz signed (.reg src)) s m =
      .ok { sz.write (sz.write s .rax q) .rdx r with
        flags := Ext.undefinedFlags
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.div sz signed (.reg src)).length } m := by
  rw [Ext.exec_div_reg, h]

theorem run_selAlu (s : State) (m : Memory) (o : AluOp) (ho : o ≠ .cmp) (d x y : Reg) (hy : ¬ Scratch y) :
    ∃ s', runSeq (selAlu o d x y) s m = some (s', m) ∧
      s'.read d = Ext.AluOp.resultN o (s.read x) (s.read y) ∧ Keeps s s' d := by
  have hy' := (not_scratch_iff y).mp hy
  unfold selAlu
  rw [runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl,
    runSeq_cons_of (Ext.exec_alu_reg _ _ _ _ _ _ ho) (by intro h; cases h) rfl,
    runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp [State.read_write_other _ _ _ _ hy'.2.2.2]
  · intro r hr hrd
    have := (not_scratch_iff r).mp hr
    simp [State.read_write_other _ _ _ _ hrd, State.read_write_other _ _ _ _ this.2.2.2]

theorem run_selMul (s : State) (m : Memory) (d x y : Reg) (hy : ¬ Scratch y) :
    ∃ s', runSeq (selMul d x y) s m = some (s', m) ∧
      s'.read d = s.read x * s.read y ∧ Keeps s s' d := by
  have hy' := (not_scratch_iff y).mp hy
  unfold selMul
  rw [runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl,
    runSeq_cons_of (Ext.exec_imul_reg _ _ _ _ _) (by intro h; cases h) rfl,
    runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp [State.read_write_other _ _ _ _ hy'.2.2.2]; rfl
  · intro r hr hrd
    have := (not_scratch_iff r).mp hr
    simp [State.read_write_other _ _ _ _ hrd, State.read_write_other _ _ _ _ this.2.2.2]

theorem run_selShift (s : State) (m : Memory) (sz : Ext.Sz) (o : Ext.ShiftOp) (d x y : Reg) (hx : ¬ Scratch x) :
    ∃ s', runSeq (selShift sz o d x y) s m = some (s', m) ∧
      s'.read d = (o.result (sz.read s x) ((s.read y).toNat % sz.bits)).setWidth 64 ∧ Keeps s s' d := by
  have hx' := (not_scratch_iff x).mp hx
  unfold selShift
  rw [runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl,
    runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl,
    runSeq_cons_of (Ext.exec_shift_reg _ _ _ _ _ _) (by intro h; cases h) rfl,
    runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl]
  refine ⟨_, rfl, ?_, ?_⟩
  · have hmod : sz.bits ∣ 256 := by cases sz <;> decide
    simp [Ext.Sz.write, Ext.Sz.read, Ext.Count.raw, State.read_write_other _ _ _ _ hx'.2.1,
      BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ hmod]
  · intro r hr hrd
    have := (not_scratch_iff r).mp hr
    simp [Ext.Sz.write, State.read_write_other _ _ _ _ hrd, State.read_write_other _ _ _ _ this.2.2.2,
      State.read_write_other _ _ _ _ this.2.1]

theorem run_selDiv_q (s : State) (m : Memory) (signed rem : Bool) (d x y : Reg) (hy : ¬ Scratch y)
    {z : Word} (he : Lir.divOp signed rem (s.read x) (s.read y) = some z) :
    ∃ s', runSeq (selDiv .q signed rem d x y) s m = some (s', m) ∧ s'.read d = z ∧ Keeps s s' d := by
  have hy' := (not_scratch_iff y).mp hy
  unfold Lir.divOp at he
  have hy0 : s.read y ≠ 0 := by intro h; simp [h] at he
  rw [ite_eq_right hy0] at he
  cases signed
  · simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at he
    have hdiv := (Ext.divide_unsigned .q (s.read x) (s.read y)).trans (ite_eq_right hy0)
    cases rem <;> simp only [selDiv, Bool.false_eq_true, ite_false, ite_true] at he ⊢ <;>
    rw [runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl,
      runSeq_cons_of (Ext.exec_movI_reg _ _ _ _ _) (by intro h; cases h) rfl,
      runSeq_cons_of (exec_div_ok .q false y _ m (q := s.read x / s.read y) (r := s.read x % s.read y)
        (by simp [State.read_write_other _ _ _ _ hy'.1, State.read_write_other _ _ _ _ hy'.2.2.1]; exact hdiv))
        (by intro h; cases h) rfl,
      runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl] <;>
    refine ⟨_, rfl, ?_, ?_⟩ <;>
    first
    | (simp_all; done)
    | (intro r hr hrd
       have := (not_scratch_iff r).mp hr
       simp [State.read_write_other _ _ _ _ hrd, State.read_write_other _ _ _ _ this.1,
        State.read_write_other _ _ _ _ this.2.2.1])
  · have hov : ¬ (s.read x = BitVec.intMin 64 ∧ s.read y = -1) := by
      intro h; simp [h] at he
    rw [ite_eq_right hov] at he
    simp only [Option.some.injEq, ite_true] at he
    have hdiv := (Ext.divide_signed .q (s.read x) (s.read y)).trans
      (ite_eq_right (by rw [← BitVec.neg_one_eq_allOnes]; exact fun h => h.elim hy0 hov))
    cases rem <;> simp only [selDiv, Bool.false_eq_true, ite_false, ite_true] at he ⊢ <;>
    rw [runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl,
      runSeq_cons_of (Ext.exec_cxd _ _ _) (by intro h; cases h) rfl,
      runSeq_cons_of (exec_div_ok .q true y _ m (q := (s.read x).sdiv (s.read y))
        (r := (s.read x).srem (s.read y))
        (by simp [State.read_write_other _ _ _ _ hy'.1, State.read_write_other _ _ _ _ hy'.2.2.1]; exact hdiv))
        (by intro h; cases h) rfl,
      runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl] <;>
    refine ⟨_, rfl, ?_, ?_⟩ <;>
    first
    | (simp_all; done)
    | (intro r hr hrd
       have := (not_scratch_iff r).mp hr
       simp [State.read_write_other _ _ _ _ hrd, State.read_write_other _ _ _ _ this.1,
        State.read_write_other _ _ _ _ this.2.2.1])

theorem run_selDiv_d (s : State) (m : Memory) (signed rem : Bool) (d x y : Reg) (hy : ¬ Scratch y)
    {z : BitVec 32} (he : Lir.divOp signed rem (Lir.lo32 (s.read x)) (Lir.lo32 (s.read y)) = some z) :
    ∃ s', runSeq (selDiv .d signed rem d x y) s m = some (s', m) ∧ s'.read d = Lir.of32 z ∧
      Keeps s s' d := by
  have hy' := (not_scratch_iff y).mp hy
  unfold Lir.divOp at he
  have hy0 : Lir.lo32 (s.read y) ≠ 0 := by intro h; simp [h] at he
  rw [ite_eq_right hy0] at he
  cases signed
  · simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at he
    have hdiv := (Ext.divide_unsigned .d (Lir.lo32 (s.read x)) (Lir.lo32 (s.read y))).trans
      (ite_eq_right hy0)
    cases rem <;> simp only [selDiv, Bool.false_eq_true, ite_false, ite_true] at he ⊢ <;>
    rw [runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl,
      runSeq_cons_of (Ext.exec_movI_reg _ _ _ _ _) (by intro h; cases h) rfl,
      runSeq_cons_of (exec_div_ok .d false y _ m (q := Lir.lo32 (s.read x) / Lir.lo32 (s.read y))
        (r := Lir.lo32 (s.read x) % Lir.lo32 (s.read y))
        (by simp [State.read_write_other _ _ _ _ hy'.1, State.read_write_other _ _ _ _ hy'.2.2.1]; exact hdiv))
        (by intro h; cases h) rfl,
      runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl] <;>
    refine ⟨_, rfl, ?_, ?_⟩ <;>
    first
    | (simp_all [Lir.of32]; done)
    | (intro r hr hrd
       have := (not_scratch_iff r).mp hr
       simp [State.read_write_other _ _ _ _ hrd, State.read_write_other _ _ _ _ this.1,
        State.read_write_other _ _ _ _ this.2.2.1])
  · have hov : ¬ (Lir.lo32 (s.read x) = BitVec.intMin 32 ∧ Lir.lo32 (s.read y) = -1) := by
      intro h; simp [h] at he
    rw [ite_eq_right hov] at he
    simp only [Option.some.injEq, ite_true] at he
    have hdiv := (Ext.divide_signed .d (Lir.lo32 (s.read x)) (Lir.lo32 (s.read y))).trans
      (ite_eq_right (by rw [← BitVec.neg_one_eq_allOnes]; exact fun h => h.elim hy0 hov))
    cases rem <;> simp only [selDiv, Bool.false_eq_true, ite_false, ite_true] at he ⊢ <;>
    rw [runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl,
      runSeq_cons_of (Ext.exec_cxd _ _ _) (by intro h; cases h) rfl,
      runSeq_cons_of (exec_div_ok .d true y _ m (q := (Lir.lo32 (s.read x)).sdiv (Lir.lo32 (s.read y)))
        (r := (Lir.lo32 (s.read x)).srem (Lir.lo32 (s.read y)))
        (by simp [State.read_write_other _ _ _ _ hy'.1, State.read_write_other _ _ _ _ hy'.2.2.1]; exact hdiv))
        (by intro h; cases h) rfl,
      runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl] <;>
    refine ⟨_, rfl, ?_, ?_⟩ <;>
    first
    | (simp_all [Lir.of32]; done)
    | (intro r hr hrd
       have := (not_scratch_iff r).mp hr
       simp [State.read_write_other _ _ _ _ hrd, State.read_write_other _ _ _ _ this.1,
        State.read_write_other _ _ _ _ this.2.2.1])

theorem ofLir_afterCmp {w : Nat} (c : Lir.Cond) (x y : BitVec (w + 1)) :
    Ext.Cond.afterCmp x y (Ext.Cond.ofLir c) = c.eval x y := by
  cases c <;>
    simp [Ext.Cond.afterCmp, Ext.Cond.ofLir, Lir.Cond.eval, BitVec.slt, BitVec.sle, BitVec.ult,
      BitVec.ule] <;> apply Bool.eq_iff_iff.mpr <;> simp [bne]

theorem run_setcc_movzx (s : State) (m : Memory) (c : Ext.Cond) (d : Reg) (f : Flags) (ip : Word)
    {v : Bool} (hv : c.eval f = some v) :
    ∃ s', runSeq [.setcc c (.reg .rax), .movx false .q .b d (.reg .rax)]
        { s with flags := f, rip := ip } m = some (s', m) ∧
      s'.read d = Lir.ofBool v ∧ Keeps s s' d := by
  rw [runSeq_cons_of (Ext.exec_setcc_reg _ _ _ _ _ hv) (by intro h; cases h) rfl,
    runSeq_cons_of (Ext.exec_movx_reg _ _ _ _ _ _ _) (by intro h; cases h) rfl]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [read_rip, Bool.false_eq_true, ite_false]
    rw [show Ext.Narrow.b.bits = 8 from rfl, Ext.writeByte_read_low]
    simp only [Ext.Sz.write, State.read_write_same]
    cases v <;> rfl
  · intro r hr hrd
    have := (not_scratch_iff r).mp hr
    simp only [read_rip, Ext.Sz.write, State.read_write_other _ _ _ _ hrd,
      Ext.writeByte_read_other _ _ _ _ this.1]
    rfl

theorem run_selCmp_q (s : State) (m : Memory) (c : Lir.Cond) (d x y : Reg) :
    ∃ s', runSeq (selCmp .q (Ext.Cond.ofLir c) d x y) s m = some (s', m) ∧
      s'.read d = Lir.ofBool (c.eval (s.read x) (s.read y)) ∧ Keeps s s' d := by
  unfold selCmp
  rw [runSeq_cons_of (Ext.exec_cmp_reg _ _ _ _ _) (by intro h; cases h) rfl]
  obtain ⟨s', h1, h2, h3⟩ := run_setcc_movzx s m _ d _ _ (Ext.eval_after_cmp_q _ _ _)
  exact ⟨s', h1, h2.trans (congrArg Lir.ofBool (ofLir_afterCmp (w := 63) c _ _)), h3⟩

theorem run_selCmp_d (s : State) (m : Memory) (c : Lir.Cond) (d x y : Reg) :
    ∃ s', runSeq (selCmp .d (Ext.Cond.ofLir c) d x y) s m = some (s', m) ∧
      s'.read d = Lir.ofBool (c.eval (Lir.lo32 (s.read x)) (Lir.lo32 (s.read y))) ∧ Keeps s s' d := by
  unfold selCmp
  rw [runSeq_cons_of (Ext.exec_cmp_reg _ _ _ _ _) (by intro h; cases h) rfl]
  obtain ⟨s', h1, h2, h3⟩ := run_setcc_movzx s m _ d _ _ (Ext.eval_after_cmp_d _ _ _)
  exact ⟨s', h1, h2.trans (congrArg Lir.ofBool (ofLir_afterCmp (w := 31) c _ _)), h3⟩

/-! ## High half of the product

`mulhuCore` computes the high half of the unsigned 128-bit product from the
four products of the 32-bit halves (`mulhu_gen`); `mulhsFix` turns it into the
high half of the signed product (`mulHigh_true`). -/

theorem mulhu_gen (N x y : Nat) (hN : 0 < N) :
    (x * y) / (N * N) = (x / N) * (y / N) + ((x / N) * (y % N)) / N +
      ((x % N) * (y / N)) / N +
      (((x % N) * (y % N)) / N + ((x / N) * (y % N)) % N +
        ((x % N) * (y / N)) % N) / N := by
  have hx := (Nat.div_add_mod' x N).symm
  have hy := (Nat.div_add_mod' y N).symm
  generalize x / N = a at *
  generalize x % N = b at *
  generalize y / N = c at *
  generalize y % N = e at *
  subst hx hy
  have hp := (Nat.div_add_mod' (a * e) N).symm
  have hq := (Nat.div_add_mod' (b * c) N).symm
  have hr := (Nat.div_add_mod' (b * e) N).symm
  have hr0 : b * e % N < N := Nat.mod_lt _ hN
  generalize (a * e) / N = p1 at *
  generalize (a * e) % N = p0 at *
  generalize (b * c) / N = q1 at *
  generalize (b * c) % N = q0 at *
  generalize (b * e) / N = r1 at *
  generalize (b * e) % N = r0 at *
  have ht := (Nat.div_add_mod' (r1 + p0 + q0) N).symm
  have ht0 : (r1 + p0 + q0) % N < N := Nat.mod_lt _ hN
  generalize (r1 + p0 + q0) / N = t1 at *
  generalize (r1 + p0 + q0) % N = t0 at *
  have key : (a * N + b) * (c * N + e) = (a * c + p1 + q1 + t1) * (N * N) + (t0 * N + r0) := by
    have e1 : (a * N + b) * (c * N + e) = a * c * (N * N) + (a * e + b * c) * N + b * e := by ring
    rw [e1, hp, hq, hr]
    have e2 : (p1 * N + p0 + (q1 * N + q0)) * N + (r1 * N + r0) =
        (p1 + q1) * (N * N) + (r1 + p0 + q0) * N + r0 := by ring
    rw [add_assoc (a * c * (N * N)), e2, ht]
    ring
  rw [key, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.mul_pos hN hN)]
  have : t0 * N + r0 < N * N := by nlinarith
  rw [Nat.div_eq_of_lt this]
  omega

def mulhuVal (x y : Word) : Word :=
  let a := x >>> 32
  let b := (x.setWidth 32).setWidth 64
  let c := y >>> 32
  let e := (y.setWidth 32).setWidth 64
  (a * e) >>> 32 + (b * c) >>> 32 +
    (((b * e) >>> 32 + ((a * e).setWidth 32).setWidth 64 + ((b * c).setWidth 32).setWidth 64) >>> 32) +
    a * c

theorem toNat_hi32 (x : Word) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_lo32 (x : Word) : ((x.setWidth 32).setWidth 64).toNat = x.toNat % 2 ^ 32 := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

theorem toNat_mul_small {x y : Word} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt]
  calc x.toNat * y.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hx hy
    _ = 2 ^ 64 := by norm_num

theorem mulhuVal_toNat (x y : Word) :
    (mulhuVal x y).toNat = x.toNat * y.toNat / 2 ^ 64 := by
  have hX := x.isLt
  have hY := y.isLt
  have hA : x.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  have hB : x.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hC : y.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  have hE : y.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hae : ((x >>> 32) * (y.setWidth 32).setWidth 64).toNat = (x.toNat / 2 ^ 32) * (y.toNat % 2 ^ 32) := by
    rw [toNat_mul_small (by rw [toNat_hi32]; exact hA) (by rw [toNat_lo32]; exact hE), toNat_hi32, toNat_lo32]
  have hbc : ((x.setWidth 32).setWidth 64 * (y >>> 32)).toNat = (x.toNat % 2 ^ 32) * (y.toNat / 2 ^ 32) := by
    rw [toNat_mul_small (by rw [toNat_lo32]; exact hB) (by rw [toNat_hi32]; exact hC), toNat_hi32, toNat_lo32]
  have hbe : ((x.setWidth 32).setWidth 64 * (y.setWidth 32).setWidth 64).toNat =
      (x.toNat % 2 ^ 32) * (y.toNat % 2 ^ 32) := by
    rw [toNat_mul_small (by rw [toNat_lo32]; exact hB) (by rw [toNat_lo32]; exact hE), toNat_lo32, toNat_lo32]
  have hac : ((x >>> 32) * (y >>> 32)).toNat = (x.toNat / 2 ^ 32) * (y.toNat / 2 ^ 32) := by
    rw [toNat_mul_small (by rw [toNat_hi32]; exact hA) (by rw [toNat_hi32]; exact hC), toNat_hi32, toNat_hi32]
  have key := mulhu_gen (2 ^ 32) x.toNat y.toNat (by decide)
  rw [show (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 by norm_num] at key
  have hxy : x.toNat * y.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hX hY
      _ = 2 ^ 64 * 2 ^ 64 := rfl
  rw [key] at hxy ⊢
  simp only [mulhuVal, BitVec.toNat_add, toNat_hi32, toNat_lo32, hae, hbc, hbe, hac]
  generalize x.toNat / 2 ^ 32 = A at *
  generalize x.toNat % 2 ^ 32 = B at *
  generalize y.toNat / 2 ^ 32 = C at *
  generalize y.toNat % 2 ^ 32 = E at *
  have p1 : A * E < 2 ^ 64 := by nlinarith
  have p2 : B * C < 2 ^ 64 := by nlinarith
  have p3 : B * E < 2 ^ 64 := by nlinarith
  have p4 : A * C ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have p4' : A * C ≤ 2 ^ 64 - 2 ^ 33 + 1 := le_trans p4 (by norm_num)
  generalize A * E = P1 at *
  generalize B * C = P2 at *
  generalize B * E = P3 at *
  generalize A * C = P4 at *
  omega

theorem mulHigh_false_toNat (x y : Word) : (Lir.mulHigh false x y).toNat = x.toNat * y.toNat / 2 ^ 64 := by
  have hX := x.isLt
  have hY := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ 128 := by
    calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hX hY
      _ = 2 ^ 128 := by norm_num
  simp only [Lir.mulHigh, Bool.false_eq_true, ite_false, BitVec.extractLsb'_toNat, BitVec.toNat_mul,
    BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (lt_trans hX (by norm_num : (2:Nat)^64 < 2^128)),
    Nat.mod_eq_of_lt (lt_trans hY (by norm_num : (2:Nat)^64 < 2^128)), Nat.mod_eq_of_lt hxy]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  calc x.toNat * y.toNat < 2 ^ 128 := hxy
    _ = 2 ^ 64 * 2 ^ 64 := by norm_num

theorem mulhuVal_eq (x y : Word) : mulhuVal x y = Lir.mulHigh false x y :=
  BitVec.eq_of_toNat_eq (by rw [mulhuVal_toNat, mulHigh_false_toNat])

theorem signed_toInt (x : Word) : x.toInt = x.toNat - (if x.msb then 2 ^ 64 else 0) := by
  rw [BitVec.toInt_eq_msb_cond]
  split <;> simp

theorem mulHigh_true (x y : Word) :
    Lir.mulHigh true x y =
      Lir.mulHigh false x y - (if x.msb then y else 0) - (if y.msb then x else 0) := by
  apply BitVec.eq_of_toNat_eq
  have hX := x.isLt
  have hY := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ 128 := by
    calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hX hY
      _ = 2 ^ 128 := by norm_num
  rw [BitVec.toNat_sub, BitVec.toNat_sub, mulHigh_false_toNat]
  simp only [Lir.mulHigh, ite_true, BitVec.extractLsb'_toNat, BitVec.toNat_mul,
    BitVec.toNat_signExtend, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (lt_trans hX (by norm_num : (2:Nat)^64 < 2^128)),
    Nat.mod_eq_of_lt (lt_trans hY (by norm_num : (2:Nat)^64 < 2^128))]
  have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
  cases x.msb <;> cases y.msb <;> simp only [ite_true, ite_false, Bool.false_eq_true, Nat.add_zero,
    h0, Nat.add_mul, Nat.mul_add] <;>
    generalize x.toNat * y.toNat = P at * <;> omega

theorem exec_movd_self (s : State) (m : Memory) (r : Reg) :
    Ext.exec (.mov .d (.reg r) r) s m =
      .ok { s.write r (((s.read r).setWidth 32).setWidth 64) with
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.mov .d (.reg r) r).length } m := rfl

theorem exec_imul_q (s : State) (m : Memory) (dst src : Reg) :
    Ext.exec (.imul .q dst (.reg src)) s m =
      .ok { s.write dst (s.read dst * s.read src) with
        flags := Ext.imulFlags (s.read dst) (s.read src)
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.imul .q dst (.reg src)).length } m := rfl

theorem exec_shr32_q (s : State) (m : Memory) (dst : Reg) :
    Ext.exec (.shift .q .shr (.reg dst) (.imm 32)) s m =
      .ok { s.write dst (s.read dst >>> 32) with
        flags := Ext.ShiftOp.flags .shr (s.read dst) 32 s.flags
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.shift .q .shr (.reg dst) (.imm 32)).length } m := rfl


theorem sshiftRight63 (x : Word) : x.sshiftRight 63 = if x.msb then BitVec.allOnes 64 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  have hm : x.msb = x.getLsbD 63 := BitVec.msb_eq_getLsbD_last x
  have h64 : decide (64 ≤ i) = false := by simp; omega
  rw [h64]
  by_cases h0 : i = 0
  · subst h0
    cases h : x.msb
    · simp only [Bool.not_false, Bool.true_and, show 63 + 0 < 64 by decide, ite_true, ite_false,
        Bool.false_eq_true]
      rw [← hm, h]
      exact (by simp : BitVec.getLsbD (0 : Word) 0 = false).symm
    · simp only [Bool.not_false, Bool.true_and, show 63 + 0 < 64 by decide, ite_true,
        BitVec.getLsbD_allOnes]
      rw [← hm, h]; decide
  · have : ¬ (63 + i < 64) := by omega
    cases h : x.msb
    · simp only [Bool.not_false, Bool.true_and, this, ite_false, Bool.false_eq_true]
      exact (by simp : BitVec.getLsbD (0 : Word) i = false).symm
    · simp only [Bool.not_false, Bool.true_and, this, ite_false, ite_true,
        BitVec.getLsbD_allOnes, hi, decide_true]

theorem sar63_and (x y : Word) : x.sshiftRight 63 &&& y = if x.msb then y else 0 := by
  rw [sshiftRight63]
  cases x.msb
  · simp only [Bool.false_eq_true, ite_false]
    exact BitVec.zero_and
  · simp only [ite_true, BitVec.allOnes_and]

theorem exec_sar63_q (s : State) (m : Memory) (dst : Reg) :
    Ext.exec (.shift .q .sar (.reg dst) (.imm 63)) s m =
      .ok { s.write dst ((s.read dst).sshiftRight 63) with
        flags := Ext.ShiftOp.flags .sar (s.read dst) 63 s.flags
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.shift .q .sar (.reg dst) (.imm 63)).length } m := rfl

theorem run_mulhuCore (s : State) (m : Memory) (x y : Reg) (hx : ¬ Scratch x) (hy : ¬ Scratch y) :
    ∃ s', runSeq (mulhuCore x y) s m = some (s', m) ∧
      s'.read .rax = mulhuVal (s.read x) (s.read y) ∧
      ∀ r, ¬ Scratch r → s'.read r = s.read r := by
  have hx' := (not_scratch_iff x).mp hx
  have hy' := (not_scratch_iff y).mp hy
  simp only [mulhuCore, runSeq, exec_mov_q, exec_movd_self, exec_imul_q, exec_shr32_q,
    exec_alu_q _ _ _ _ _ (show AluOp.add ≠ .cmp by decide)]
  simp only [Ext.Instr.length, ne_eq, reduceCtorEq, not_false_eq_true, ite_true, Option.some.injEq,
    Prod.mk.injEq, and_true, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp [State.read_write_other _ _ _ _ hx'.1, State.read_write_other _ _ _ _ hx'.2.1,
      State.read_write_other _ _ _ _ hx'.2.2.1, State.read_write_other _ _ _ _ hx'.2.2.2,
      State.read_write_other _ _ _ _ hy'.1, State.read_write_other _ _ _ _ hy'.2.1,
      State.read_write_other _ _ _ _ hy'.2.2.1, State.read_write_other _ _ _ _ hy'.2.2.2, mulhuVal,
      Ext.AluOp.resultN]
  · intro r hr
    have := (not_scratch_iff r).mp hr
    simp [State.read_write_other _ _ _ _ this.1,
      State.read_write_other _ _ _ _ this.2.1, State.read_write_other _ _ _ _ this.2.2.1,
      State.read_write_other _ _ _ _ this.2.2.2]

theorem run_mulhsFix (s : State) (m : Memory) (x y : Reg) (hx : ¬ Scratch x) (hy : ¬ Scratch y) :
    ∃ s', runSeq (mulhsFix x y) s m = some (s', m) ∧
      s'.read .rax = s.read .rax - (if (s.read x).msb then s.read y else 0) -
        (if (s.read y).msb then s.read x else 0) ∧
      ∀ r, ¬ Scratch r → s'.read r = s.read r := by
  have hx' := (not_scratch_iff x).mp hx
  have hy' := (not_scratch_iff y).mp hy
  simp only [mulhsFix, runSeq, exec_mov_q, exec_sar63_q,
    exec_alu_q _ _ _ _ _ (show AluOp.and ≠ .cmp by decide),
    exec_alu_q _ _ _ _ _ (show AluOp.sub ≠ .cmp by decide)]
  simp only [Ext.Instr.length, ne_eq, reduceCtorEq, not_false_eq_true, ite_true, Option.some.injEq,
    Prod.mk.injEq, and_true, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp [State.read_write_other _ _ _ _ hx'.2.2.2, State.read_write_other _ _ _ _ hy'.2.2.2,
      State.read_write_other _ _ _ _ hx'.1, State.read_write_other _ _ _ _ hy'.1,
      State.read_write_other _ _ _ _ (show Reg.rax ≠ .r11 by decide),
      Ext.AluOp.resultN, sar63_and]
  · intro r hr
    have := (not_scratch_iff r).mp hr
    simp [State.read_write_other _ _ _ _ this.1, State.read_write_other _ _ _ _ this.2.2.2]

theorem alu_case (s : State) (m : Memory) (o : AluOp) (ho : o ≠ .cmp) (d x y : Reg) (hy : ¬ Scratch y)
    {z : Word} (he : Ext.AluOp.resultN o (s.read x) (s.read y) = z) :
    ∃ s', runSeq (selAlu o d x y) s m = some (s', m) ∧ s'.read d = z ∧ Keeps s s' d := by
  obtain ⟨s', h1, h2, h3⟩ := run_selAlu s m o ho d x y hy
  exact ⟨s', h1, h2.trans he, h3⟩

theorem run_selBinop (s : State) (m : Memory) (op : Lir.Binop)
    (d x y : Reg) (hx : ¬ Scratch x) (hy : ¬ Scratch y) {z : Word}
    (he : op.eval (s.read x) (s.read y) = some z) :
    ∃ s', runSeq (selBinop op d x y) s m = some (s', m) ∧ s'.read d = z ∧ Keeps s s' d := by
  cases op
  case mulhu =>
    obtain ⟨s₁, h₁, v₁, k₁⟩ := run_mulhuCore s m x y hx hy
    simp only [Lir.Binop.eval, Option.some.injEq] at he
    refine ⟨_, by rw [selBinop, runSeq_append_of h₁,
      runSeq_cons_of (exec_mov_q _ _ _ _) (by intro h; cases h) rfl]; rfl, ?_, ?_⟩
    · simp only [read_rip, State.read_write_same]
      rw [v₁, mulhuVal_eq, he]
    · intro r hr hrd; simp [State.read_write_other _ _ _ _ hrd, k₁ r hr]
  case mulhs =>
    obtain ⟨s₁, h₁, v₁, k₁⟩ := run_mulhuCore s m x y hx hy
    obtain ⟨s₂, h₂, v₂, k₂⟩ := run_mulhsFix s₁ m x y hx hy
    simp only [Lir.Binop.eval, Option.some.injEq] at he
    refine ⟨_, by rw [selBinop, List.append_assoc, runSeq_append_of h₁, runSeq_append_of h₂,
      runSeq_cons_of (exec_mov_q _ _ _ _) (by intro h; cases h) rfl]; rfl, ?_, ?_⟩
    · simp only [read_rip, State.read_write_same]
      rw [v₂, v₁, k₁ x hx, k₁ y hy, ← he, mulHigh_true, mulhuVal_eq]
    · intro r hr hrd; simp [State.read_write_other _ _ _ _ hrd, k₂ r hr, k₁ r hr]
  case mul =>
    obtain ⟨s', h1, h2, h3⟩ := run_selMul s m d x y hy
    simp only [Lir.Binop.eval, Option.some.injEq] at he
    exact ⟨s', h1, by rw [h2, ← he], h3⟩
  case cmp c =>
    obtain ⟨s', h1, h2, h3⟩ := run_selCmp_q s m c d x y
    simp only [Lir.Binop.eval, Option.some.injEq] at he
    exact ⟨s', h1, by rw [h2, ← he], h3⟩
  case cmp32 c =>
    obtain ⟨s', h1, h2, h3⟩ := run_selCmp_d s m c d x y
    simp only [Lir.Binop.eval, Option.some.injEq] at he
    exact ⟨s', h1, by rw [h2, ← he], h3⟩
  case add => exact alu_case s m .add (by decide) d x y hy (by simp only [Lir.Binop.eval, Option.some.injEq] at he; exact he)
  case sub => exact alu_case s m .sub (by decide) d x y hy (by simp only [Lir.Binop.eval, Option.some.injEq] at he; exact he)
  case and => exact alu_case s m .and (by decide) d x y hy (by simp only [Lir.Binop.eval, Option.some.injEq] at he; exact he)
  case or => exact alu_case s m .or (by decide) d x y hy (by simp only [Lir.Binop.eval, Option.some.injEq] at he; exact he)
  case xor => exact alu_case s m .xor (by decide) d x y hy (by simp only [Lir.Binop.eval, Option.some.injEq] at he; exact he)
  case shl | shrs | shru | rotl | rotr | shl32 | shrs32 | shru32 | rotl32 | rotr32 =>
    obtain ⟨s', h1, h2, h3⟩ := run_selShift s m _ _ d x y hx
    simp only [Lir.Binop.eval, Option.some.injEq] at he
    exact ⟨s', h1, by rw [h2, ← he]; simp [Ext.ShiftOp.result, Lir.of32, Lir.lo32] ; all_goals rfl, h3⟩
  case divs | divu | rems | remu =>
    obtain ⟨s', h1, h2, h3⟩ := run_selDiv_q s m _ _ d x y hy he
    exact ⟨s', h1, h2, h3⟩
  case divs32 | divu32 | rems32 | remu32 =>
    simp only [Lir.Binop.eval, Option.map_eq_some_iff] at he
    obtain ⟨z', he', rfl⟩ := he
    obtain ⟨s', h1, h2, h3⟩ := run_selDiv_d s m _ _ d x y hy he'
    exact ⟨s', h1, h2, h3⟩

/-! ## Bit counts

The LZCNT, TZCNT and POPCNT counts of the model are `BitVec.clz`, `ctz` and
`cpop`. -/

theorem countP_range_eq {w : Nat} (x : BitVec w) : ∀ k, (List.range k).countP (fun i => x.getLsbD i) = x.cpopNatRec k 0
  | 0 => by simp [BitVec.cpopNatRec]
  | k + 1 => by
    rw [List.range_succ, List.countP_append, countP_range_eq x k]
    simp only [BitVec.cpopNatRec, Nat.zero_add]
    rw [BitVec.cpopNatRec_eq (acc := (x.getLsbD k).toNat)]
    cases h : x.getLsbD k <;> simp [h]

theorem cpop_eq {w : Nat} (x : BitVec w) : x.cpop = BitVec.ofNat w (Ext.popcntN x) := by
  unfold BitVec.cpop Ext.popcntN
  rw [countP_range_eq]

def firstFrom {w : Nat} (x : BitVec w) (n : Nat) : Nat :=
  ((List.range (n + 1)).find? fun j => x.getLsbD (n - j)).getD (n + 1)

theorem firstFrom_zero {w : Nat} (x : BitVec w) : firstFrom x 0 = if x.getLsbD 0 then 0 else 1 := by
  cases h : x.getLsbD 0 <;> simp [firstFrom, h]

theorem firstFrom_succ {w : Nat} (x : BitVec w) (n : Nat) :
    firstFrom x (n + 1) = if x.getLsbD (n + 1) then 0 else firstFrom x n + 1 := by
  unfold firstFrom
  rw [List.range_succ_eq_map]
  cases h : x.getLsbD (n + 1)
  · simp only [List.find?_cons, Nat.sub_zero, h, List.find?_map]
    simp only [Bool.false_eq_true, ite_false]
    have : ((fun j => x.getLsbD (n + 1 - j)) ∘ Nat.succ) = fun j => x.getLsbD (n - j) := by
      funext j; simp [Nat.succ_sub_succ]
    rw [this]
    cases (List.range (n + 1)).find? (fun j => x.getLsbD (n - j)) <;> simp
  · simp [h]

theorem clzAuxRec_eq {w : Nat} (x : BitVec w) : ∀ n, n < w →
    x.clzAuxRec n = BitVec.ofNat w (w - 1 - n + firstFrom x n)
  | 0, hw => by
    rw [firstFrom_zero]
    cases h : x.getLsbD 0
    · simp [BitVec.clzAuxRec, h]; congr 1; omega
    · simp [BitVec.clzAuxRec, h]
  | n + 1, hw => by
    rw [firstFrom_succ]
    cases h : x.getLsbD (n + 1)
    · simp only [BitVec.clzAuxRec, h, Bool.false_eq_true, ite_false]
      rw [clzAuxRec_eq x n (by omega)]
      congr 1; omega
    · simp [BitVec.clzAuxRec, h]

theorem clz_eq {w : Nat} (x : BitVec w) (hw : 0 < w) : x.clz = BitVec.ofNat w (Ext.lzcntN x) := by
  rw [BitVec.clz_eq_clzAuxRec]
  unfold Ext.lzcntN
  rw [clzAuxRec_eq x (w - 1) (by omega)]
  congr 1
  unfold firstFrom
  rw [show w - 1 + 1 = w by omega]
  omega

theorem find?_congr' {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.find?_cons, h a (by simp)]
    rw [find?_congr' (fun x hx => h x (by simp [hx]))]

theorem ctz_eq {w : Nat} (x : BitVec w) (hw : 0 < w) : x.ctz = BitVec.ofNat w (Ext.tzcntN x) := by
  rw [BitVec.ctz_eq_reverse_clz, clz_eq _ hw]
  congr 1
  unfold Ext.lzcntN Ext.tzcntN
  congr 1
  apply find?_congr'
  intro i hi
  rw [List.mem_range] at hi
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  simp only [show w - 1 - i < w by omega, decide_true, Bool.true_and]
  congr 1; omega

theorem exec_bitcount_q (s : State) (m : Memory) (op : Ext.BitCountOp) (dst src : Reg) :
    Ext.exec (.bitcount op .q dst (.reg src)) s m =
      .ok { s.write dst (BitVec.ofNat 64 (op.count (s.read src))) with
        flags := op.flags (s.read src)
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.bitcount op .q dst (.reg src)).length } m := by
  rw [Ext.exec_bitcount_reg]; rfl

theorem exec_bitcount_d (s : State) (m : Memory) (op : Ext.BitCountOp) (dst src : Reg) :
    Ext.exec (.bitcount op .d dst (.reg src)) s m =
      .ok { s.write dst ((BitVec.ofNat 32 (op.count ((s.read src).setWidth 32))).setWidth 64) with
        flags := op.flags ((s.read src).setWidth 32)
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.bitcount op .d dst (.reg src)).length } m := by
  rw [Ext.exec_bitcount_reg]; rfl

theorem keeps_write (s : State) (d : Reg) (v : Word) (ip : Word) : Keeps s { s.write d v with rip := ip } d := by
  intro r hr hrd; simp [State.read_write_other _ _ _ _ hrd]

theorem run_selUnop (s : State) (m : Memory) (op : Lir.Unop) (d x : Reg) :
    ∃ s', runSeq (selUnop op d x) s m = some (s', m) ∧ s'.read d = op.eval (s.read x) ∧
      Keeps s s' d := by
  cases op
  case eqz =>
    simp only [selUnop]
    rw [runSeq_cons_of (Ext.exec_cmpI_reg _ _ _ _ _) (by intro h; cases h) rfl]
    obtain ⟨s', h1, h2, h3⟩ := run_setcc_movzx s m .e d _ _ (Ext.eval_after_cmp_q _ _ _)
    refine ⟨s', h1, ?_, h3⟩
    rw [h2]
    simp [Ext.Cond.afterCmp, Lir.Unop.eval, Ext.Sz.read]
  case sext8 =>
    simp only [selUnop]
    rw [runSeq_cons_of (Ext.exec_movx_reg _ _ _ _ _ _ _) (by intro h; cases h) rfl]
    exact ⟨_, rfl, by simp [Ext.Sz.write, Lir.Unop.eval]; rfl, by
      intro r hr hrd; simp [Ext.Sz.write, State.read_write_other _ _ _ _ hrd]⟩
  case sext16 =>
    simp only [selUnop]
    rw [runSeq_cons_of (Ext.exec_movx_reg _ _ _ _ _ _ _) (by intro h; cases h) rfl]
    exact ⟨_, rfl, by simp [Ext.Sz.write, Lir.Unop.eval]; rfl, by
      intro r hr hrd; simp [Ext.Sz.write, State.read_write_other _ _ _ _ hrd]⟩
  case zext8 =>
    simp only [selUnop]
    rw [runSeq_cons_of (Ext.exec_movx_reg _ _ _ _ _ _ _) (by intro h; cases h) rfl]
    exact ⟨_, rfl, by simp [Ext.Sz.write, Lir.Unop.eval]; rfl, by
      intro r hr hrd; simp [Ext.Sz.write, State.read_write_other _ _ _ _ hrd]⟩
  case zext16 =>
    simp only [selUnop]
    rw [runSeq_cons_of (Ext.exec_movx_reg _ _ _ _ _ _ _) (by intro h; cases h) rfl]
    exact ⟨_, rfl, by simp [Ext.Sz.write, Lir.Unop.eval]; rfl, by
      intro r hr hrd; simp [Ext.Sz.write, State.read_write_other _ _ _ _ hrd]⟩
  case sext32 =>
    simp only [selUnop]
    rw [runSeq_cons_of (Ext.exec_movsxd_reg _ _ _ _) (by intro h; cases h) rfl]
    exact ⟨_, rfl, by simp [Lir.Unop.eval], keeps_write _ _ _ _⟩
  case zext32 =>
    simp only [selUnop]
    rw [runSeq_cons_of (Ext.exec_mov_reg _ _ _ _ _) (by intro h; cases h) rfl]
    exact ⟨_, rfl, by simp [Lir.Unop.eval, Lir.of32, Lir.lo32], by
      intro r hr hrd; simp [State.read_write_other _ _ _ _ hrd]⟩
  all_goals simp only [selUnop]
  all_goals first
    | rw [runSeq_cons_of (exec_bitcount_q _ _ _ _ _) (by intro h; cases h) rfl]
    | rw [runSeq_cons_of (exec_bitcount_d _ _ _ _ _) (by intro h; cases h) rfl]
  all_goals refine ⟨_, rfl, ?_, fun r hr hrd => by simp [State.read_write_other _ _ _ _ hrd]⟩
  all_goals simp only [read_flags_rip, State.read_write_same, Lir.Unop.eval, Ext.BitCountOp.count,
    Lir.of32, Lir.lo32]
  · exact (clz_eq _ (by decide)).symm
  · exact (ctz_eq _ (by decide)).symm
  · exact (cpop_eq _).symm
  · rw [clz_eq _ (by decide)]
  · rw [ctz_eq _ (by decide)]
  · rw [cpop_eq]

/-! ## Memory operations -/

theorem signExtend_ofNat32 {d : Nat} (hd : d < 2 ^ 31) :
    (BitVec.ofNat 32 d).signExtend 64 = BitVec.ofNat 64 d := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]
    rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem spMem_addr (s : State) (next : Word) {B d : Nat} (hB : s.read .rsp = BitVec.ofNat 64 B)
    (hd : d < 2 ^ 31) : (spMem d).addr s next = BitVec.ofNat 64 (B + d) := by
  simp only [Ext.Mem.addr, spMem, Ext.Mem.ofReg, Ext.Base.value_reg, hB, Option.map_none,
    Option.getD_none, signExtend_ofNat32 hd, BitVec.add_zero, BitVec.ofNat_add]

theorem linMem_addr (s : State) (next : Word) {base : Nat} {b off : Word}
    (h15 : s.read .r15 = BitVec.ofNat 64 base) (h11 : s.read .r11 = off + b) :
    linMem.addr s next = BitVec.ofNat 64 base + (off + b) := by
  simp [Ext.Mem.addr, linMem, Ext.Mem.ofReg, h15, Ext.Index.value, h11]

theorem lin_addr_eq {base a off : Nat} (b : Word) (hb : b.toNat = a) (h : base + (a + off) < 2 ^ 64) :
    BitVec.ofNat 64 base + (BitVec.ofNat 64 off + b) = BitVec.ofNat 64 (base + (a + off)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hb]
  have : base < 2 ^ 64 := by omega
  have : off < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt (a := base) (by omega), Nat.mod_eq_of_lt (a := off) (by omega)]
  rw [Nat.mod_eq_of_lt (a := off + a) (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem exec_movx_mem (sx : Bool) (sz : Ext.Sz) (n : Ext.Narrow) (d : Reg) (mm : Ext.Mem) (s : State)
    (m : Memory) {v : Word}
    (h : Ext.loadN m (mm.addr s
      (s.rip + BitVec.ofNat 64 (Ext.Instr.movx sx sz n d (.mem mm)).length)) n.bytes = some v) :
    Ext.exec (.movx sx sz n d (.mem mm)) s m =
      .ok { sz.write s d (if sx then (v.setWidth n.bits).signExtend sz.bits
          else (v.setWidth n.bits).setWidth sz.bits) with
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.movx sx sz n d (.mem mm)).length } m := by
  simp [Ext.exec, Ext.readNarrow, h, Ext.retire]

theorem exec_movsxd_mem (d : Reg) (mm : Ext.Mem) (s : State) (m : Memory) {v : Word}
    (h : Ext.loadN m (mm.addr s
      (s.rip + BitVec.ofNat 64 (Ext.Instr.movsxd d (.mem mm)).length)) 4 = some v) :
    Ext.exec (.movsxd d (.mem mm)) s m =
      .ok { s.write d ((v.setWidth 32).signExtend 64) with
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.movsxd d (.mem mm)).length } m := by
  simp [Ext.exec, Ext.readRM, h, Ext.retire, Ext.Sz.bytes]

theorem exec_load_ok (sz : Ext.Sz) (d : Reg) (mm : Ext.Mem) (s : State) (m : Memory) {v : Word}
    (h : Ext.loadN m (mm.addr s
      (s.rip + BitVec.ofNat 64 (Ext.Instr.load sz d mm).length)) sz.bytes = some v) :
    Ext.exec (.load sz d mm) s m =
      .ok { sz.write s d (v.setWidth sz.bits) with
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.load sz d mm).length } m := by
  rw [Ext.exec_load, h]

theorem setWidth_of_lt {k : Nat} (v : Word) (h : v.toNat < 2 ^ k) :
    (v.setWidth k).setWidth 64 = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt v.isLt]

theorem run_selLoad {S : Space} {n : Nat} (hv : S.Valid n) (s : State) (m : Memory)
    (hreg : m.regions = S.regions n) {lm : Lir.Memory} (hmem : MemRel S lm m) {a : Nat}
    (haddr : ∀ next, linMem.addr s next = BitVec.ofNat 64 (S.memBase + a)) (w : Lir.Width) (e : Lir.Ext) (d : Reg)
    {z : Word} (hl : lm.load w e a = some z) :
    ∃ s', runSeq [selLoad w e d] s m = some (s', m) ∧ s'.read d = z ∧
      ∀ r, r ≠ d → s'.read r = s.read r := by
  unfold Lir.Memory.load at hl
  split at hl
  · rename_i hin
    simp only [Option.some.injEq] at hl
    subst hl
    have ld : ∀ (next : Word) (k : Nat), k ≤ 8 → a + k ≤ lm.size →
        Ext.loadN m (linMem.addr s next) k = some (Lir.readLE lm.bytes a k) := by
      intro next k hk hin'
      rw [haddr]; exact loadN_lin hv hreg hmem hk hin'
    unfold Lir.Memory.InBounds at hin
    cases w <;> cases e <;> simp only [selLoad, Lir.Width.bytes] at hin ⊢
    · rw [runSeq_cons_of (exec_movx_mem _ _ _ _ _ _ _ (ld _ 1 (by omega) hin)) (by intro h; cases h) rfl]
      refine ⟨_, rfl, ?_, fun r hr => by simp [Ext.Sz.write, State.read_write_other _ _ _ _ hr]⟩
      simp only [read_rip, Ext.Sz.write, State.read_write_same, Bool.false_eq_true, ite_false,
        Lir.extend]
      have := readLE_lt lm.bytes (k := 1) (by omega) a
      rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
      exact setWidth_of_lt _ this
    · rw [runSeq_cons_of (exec_movx_mem _ _ _ _ _ _ _ (ld _ 1 (by omega) hin)) (by intro h; cases h) rfl]
      refine ⟨_, rfl, ?_, fun r hr => by simp [Ext.Sz.write, State.read_write_other _ _ _ _ hr]⟩
      simp [Ext.Sz.write, Lir.extend]; rfl
    · rw [runSeq_cons_of (exec_movx_mem _ _ _ _ _ _ _ (ld _ 2 (by omega) hin)) (by intro h; cases h) rfl]
      refine ⟨_, rfl, ?_, fun r hr => by simp [Ext.Sz.write, State.read_write_other _ _ _ _ hr]⟩
      simp only [read_rip, Ext.Sz.write, State.read_write_same, Bool.false_eq_true, ite_false,
        Lir.extend]
      have := readLE_lt lm.bytes (k := 2) (by omega) a
      rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
      exact setWidth_of_lt _ this
    · rw [runSeq_cons_of (exec_movx_mem _ _ _ _ _ _ _ (ld _ 2 (by omega) hin)) (by intro h; cases h) rfl]
      refine ⟨_, rfl, ?_, fun r hr => by simp [Ext.Sz.write, State.read_write_other _ _ _ _ hr]⟩
      simp [Ext.Sz.write, Lir.extend]; rfl
    · rw [runSeq_cons_of (exec_load_ok _ _ _ _ _ (ld _ 4 (by omega) hin)) (by intro h; cases h) rfl]
      refine ⟨_, rfl, ?_, fun r hr => by simp [Ext.Sz.write, State.read_write_other _ _ _ _ hr]⟩
      simp only [read_rip, Ext.Sz.write, State.read_write_same, Lir.extend]
      exact setWidth_of_lt _ (readLE_lt lm.bytes (k := 4) (by omega) a)
    · rw [runSeq_cons_of (exec_movsxd_mem _ _ _ _ (ld _ 4 (by omega) hin)) (by intro h; cases h) rfl]
      refine ⟨_, rfl, ?_, fun r hr => by simp [State.read_write_other _ _ _ _ hr]⟩
      simp [Lir.extend]; rfl
    · rw [runSeq_cons_of (exec_load_ok _ _ _ _ _ (ld _ 8 (by omega) hin)) (by intro h; cases h) rfl]
      refine ⟨_, rfl, ?_, fun r hr => by simp [Ext.Sz.write, State.read_write_other _ _ _ _ hr]⟩
      simp [Ext.Sz.write, Lir.extend]
    · rw [runSeq_cons_of (exec_load_ok _ _ _ _ _ (ld _ 8 (by omega) hin)) (by intro h; cases h) rfl]
      refine ⟨_, rfl, ?_, fun r hr => by simp [Ext.Sz.write, State.read_write_other _ _ _ _ hr]⟩
      simp [Ext.Sz.write, Lir.extend, Lir.Width.bytes, BitVec.signExtend_eq]
  · cases hl

theorem exec_store_ok (sz : Ext.Sz) (mm : Ext.Mem) (src : Reg) (s : State) (m : Memory) {m' : Memory}
    (h : Ext.storeN m (mm.addr s
      (s.rip + BitVec.ofNat 64 (Ext.Instr.mov sz (.mem mm) src).length)) sz.bytes
        ((sz.read s src).setWidth 64) = some m') :
    Ext.exec (.mov sz (.mem mm) src) s m =
      .ok { s with rip := s.rip + BitVec.ofNat 64 (Ext.Instr.mov sz (.mem mm) src).length } m' := by
  rw [Ext.exec_store, h]

theorem exec_storeNarrow_ok (n : Ext.Narrow) (mm : Ext.Mem) (src : Reg) (s : State) (m : Memory)
    {m' : Memory}
    (h : Ext.storeN m (mm.addr s
      (s.rip + BitVec.ofNat 64 (Ext.Instr.store n (.mem mm) src).length)) n.bytes (s.read src) = some m') :
    Ext.exec (.store n (.mem mm) src) s m =
      .ok { s with rip := s.rip + BitVec.ofNat 64 (Ext.Instr.store n (.mem mm) src).length } m' := by
  rw [Ext.exec_storeNarrow, h]

theorem wordByte_setWidth32 (v : Word) {j : Nat} (hj : j < 4) :
    Machine.LittleEndian.wordByte ((v.setWidth 32).setWidth 64) j = Machine.LittleEndian.wordByte v j := by
  ext i hi
  simp only [Machine.LittleEndian.wordByte, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth]
  have : 8 * j + i < 32 := by omega
  simp [this]
  omega

theorem run_selStore {S : Space} {n : Nat} (hv : S.Valid n) (s : State) (m : Memory)
    (hreg : m.regions = S.regions n) {lm : Lir.Memory} (hmem : MemRel S lm m) {a : Nat}
    (haddr : ∀ next, linMem.addr s next = BitVec.ofNat 64 (S.memBase + a)) (w : Lir.Width) (src : Reg)
    {lm' : Lir.Memory} (hs : lm.store w a (s.read src) = some lm') :
    ∃ s' m', runSeq [selStore w src] s m = some (s', m') ∧ (∀ r, s'.read r = s.read r) ∧
      MemRel S lm' m' ∧ (∀ x, ¬ S.InMem x → m'.bytes.get? x = m.bytes.get? x) := by
  unfold Lir.Memory.store at hs
  split at hs
  · rename_i hin
    simp only [Option.some.injEq] at hs
    subst hs
    unfold Lir.Memory.InBounds at hin
    have hb : S.memBase + a < 2 ^ 64 := by have := hv.mem_end; have := hmem.1; omega
    cases w <;> simp only [selStore, Lir.Width.bytes] at hin ⊢
    · obtain ⟨m', hm'⟩ := storeN_lin_some hv hreg hmem (k := 1) hin (s.read src)
      rw [runSeq_cons_of (exec_storeNarrow_ok _ _ _ _ _ (by rw [haddr]; exact hm')) (by intro h; cases h) rfl]
      exact ⟨_, _, rfl, fun r => rfl, memRel_store hv hmem hin hm' (fun j _ => rfl),
        store_outside hmem hin hb hm'⟩
    · obtain ⟨m', hm'⟩ := storeN_lin_some hv hreg hmem (k := 2) hin (s.read src)
      rw [runSeq_cons_of (exec_storeNarrow_ok _ _ _ _ _ (by rw [haddr]; exact hm')) (by intro h; cases h) rfl]
      exact ⟨_, _, rfl, fun r => rfl, memRel_store hv hmem hin hm' (fun j _ => rfl),
        store_outside hmem hin hb hm'⟩
    · obtain ⟨m', hm'⟩ := storeN_lin_some hv hreg hmem (k := 4) hin (((s.read src).setWidth 32).setWidth 64)
      rw [runSeq_cons_of (exec_store_ok _ _ _ _ _ (by rw [haddr]; exact hm')) (by intro h; cases h) rfl]
      exact ⟨_, _, rfl, fun r => rfl, memRel_store hv hmem hin hm' (fun j hj => wordByte_setWidth32 _ hj),
        store_outside hmem hin hb hm'⟩
    · obtain ⟨m', hm'⟩ := storeN_lin_some hv hreg hmem (k := 8) hin (s.read src)
      rw [runSeq_cons_of (exec_store_ok _ _ _ _ _ (by rw [haddr]; simp only [Ext.Sz.read_q]; exact hm')) (by intro h; cases h) rfl]
      exact ⟨_, _, rfl, fun r => rfl, memRel_store hv hmem hin hm' (fun j _ => rfl),
        store_outside hmem hin hb hm'⟩
  · cases hs
theorem run_addrSeq (s : State) (m : Memory) (base : Reg) (off : Nat) (hb : base ≠ .r11) :
    ∃ s', runSeq (addrSeq base off) s m = some (s', m) ∧
      s'.read .r11 = BitVec.ofNat 64 off + s.read base ∧ ∀ r, r ≠ .r11 → s'.read r = s.read r := by
  unfold addrSeq
  rw [runSeq_cons_of (Ext.exec_movabs _ _ _ _) (by intro h; cases h) rfl,
    runSeq_cons_of (Ext.exec_alu_reg _ _ _ _ _ _ (by decide)) (by intro h; cases h) rfl]
  refine ⟨_, rfl, ?_, fun r hr => ?_⟩
  · simp [State.read_write_other _ _ _ _ hb, Ext.AluOp.resultN]; rfl
  · simp [State.read_write_other _ _ _ _ hr]

/-- The code of a Lir load from the linear memory. -/
theorem run_loadOp {S : Space} {n : Nat} (hv : S.Valid n) (s : State) (m : Memory)
    (hreg : m.regions = S.regions n) {lm : Lir.Memory} (hmem : MemRel S lm m)
    (h15 : s.read .r15 = BitVec.ofNat 64 S.memBase) (w : Lir.Width) (e : Lir.Ext) (d base : Reg)
    (off : Nat) (hb : ¬ Scratch base) {z : Word}
    (hl : lm.load w e ((s.read base).toNat + off) = some z) :
    ∃ s', runSeq (addrSeq base off ++ [selLoad w e d]) s m = some (s', m) ∧ s'.read d = z ∧
      Keeps s s' d := by
  have hb' := (not_scratch_iff base).mp hb
  have hin : (s.read base).toNat + off + w.bytes ≤ lm.size := by
    by_contra h
    simp [Lir.Memory.load, Lir.Memory.InBounds, h] at hl
  obtain ⟨s₁, h₁, r11, keep₁⟩ := run_addrSeq s m base off hb'.2.2.2
  have haddr : ∀ next, linMem.addr s₁ next =
      BitVec.ofNat 64 (S.memBase + ((s.read base).toNat + off)) := by
    intro next
    rw [linMem_addr s₁ next (by rw [keep₁ _ (by decide), h15]) r11]
    have := hv.mem_end; have := hmem.1
    have : 0 < w.bytes := by cases w <;> decide
    rw [lin_addr_eq _ rfl (by omega)]
  obtain ⟨s₂, h₂, hd, keep₂⟩ := run_selLoad hv s₁ m hreg hmem haddr w e d hl
  refine ⟨s₂, by rw [runSeq_append_of h₁, h₂], hd, fun r hr hrd => ?_⟩
  rw [keep₂ r hrd, keep₁ r ((not_scratch_iff r).mp hr).2.2.2]

/-- The code of a Lir store to the linear memory. -/
theorem run_storeOp {S : Space} {n : Nat} (hv : S.Valid n) (s : State) (m : Memory)
    (hreg : m.regions = S.regions n) {lm : Lir.Memory} (hmem : MemRel S lm m)
    (h15 : s.read .r15 = BitVec.ofNat 64 S.memBase) (w : Lir.Width) (base src : Reg)
    (off : Nat) (hb : ¬ Scratch base) (hs : ¬ Scratch src) {lm' : Lir.Memory}
    (hst : lm.store w ((s.read base).toNat + off) (s.read src) = some lm') :
    ∃ s' m', runSeq (addrSeq base off ++ [selStore w src]) s m = some (s', m') ∧
      (∀ r, ¬ Scratch r → s'.read r = s.read r) ∧ MemRel S lm' m' ∧
      (∀ x, ¬ S.InMem x → m'.bytes.get? x = m.bytes.get? x) := by
  have hb' := (not_scratch_iff base).mp hb
  have hs' := (not_scratch_iff src).mp hs
  have hin : (s.read base).toNat + off + w.bytes ≤ lm.size := by
    by_contra h
    simp [Lir.Memory.store, Lir.Memory.InBounds, h] at hst
  obtain ⟨s₁, h₁, r11, keep₁⟩ := run_addrSeq s m base off hb'.2.2.2
  have haddr : ∀ next, linMem.addr s₁ next =
      BitVec.ofNat 64 (S.memBase + ((s.read base).toNat + off)) := by
    intro next
    rw [linMem_addr s₁ next (by rw [keep₁ _ (by decide), h15]) r11]
    have := hv.mem_end; have := hmem.1
    have : 0 < w.bytes := by cases w <;> decide
    rw [lin_addr_eq _ rfl (by omega)]
  rw [← keep₁ src hs'.2.2.2] at hst
  obtain ⟨s₂, m₂, h₂, keep₂, hrel, hout⟩ := run_selStore hv s₁ m hreg hmem haddr w src hst
  refine ⟨s₂, m₂, by rw [runSeq_append_of h₁, h₂], fun r hr => ?_, hrel, hout⟩
  rw [keep₂ r, keep₁ r ((not_scratch_iff r).mp hr).2.2.2]

/-! ## Stack words -/

theorem exec_ldQ_sp (s : State) (m : Memory) (dst : Reg) {B d : Nat} {v : Word}
    (hB : s.read .rsp = BitVec.ofNat 64 B) (hd : d < 2 ^ 31) (hsum : B + d < 2 ^ 64)
    (hw : WordAt m (B + d) v) (hp : m.Permitted .read (B + d) 8) :
    Ext.exec (.load .q dst (spMem d)) s m =
      .ok { s.write dst v with
        rip := s.rip + BitVec.ofNat 64 (Ext.Instr.load .q dst (spMem d)).length } m := by
  rw [exec_load_ok .q dst (spMem d) s m (v := v)]
  · simp
  · rw [spMem_addr s _ hB hd]; exact loadN_of_wordAt hsum hw hp

theorem exec_stQ_sp (s : State) (m : Memory) (src : Reg) {B d : Nat} {m' : Memory}
    (hB : s.read .rsp = BitVec.ofNat 64 B) (hd : d < 2 ^ 31)
    (h : Ext.storeN m (BitVec.ofNat 64 (B + d)) 8 (s.read src) = some m') :
    Ext.exec (.mov .q (.mem (spMem d)) src) s m =
      .ok { s with rip := s.rip + BitVec.ofNat 64 (Ext.Instr.mov .q (.mem (spMem d)) src).length }
        m' :=
  exec_store_ok .q (spMem d) src s m
    (by rw [spMem_addr s _ hB hd]; simp only [Ext.Sz.read_q]; exact h)

end Silmaril.X86.Backend

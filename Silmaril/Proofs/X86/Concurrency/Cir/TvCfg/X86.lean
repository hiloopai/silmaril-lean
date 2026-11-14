module

public import Silmaril.X86.Concurrency.Cir.TvCfg.Defs

/-!
# CFG translation validation: one x86 instruction

`kind_sound`: for each instruction form of the checker's table
(`TvCfg.kindOf`), every branch of the symbolic step `stepSym` is described by `KSem`:

* an `op` form is one `Csl.TStep` of the CIR statement (with any mode), with the same memory
  actions, the same registers after, and `rip` advanced;
* a flag form leaves the registers alone and sets the zero flag to the truth value of the
  checker's expression;
* `nop`/`pause`/`jmp` leave the registers alone and move `rip`;
* `je`/`jne` read a defined zero flag and go to the target or fall through accordingly.

The byte lemmas (`leBytes_eq`, `natBytes_mod`, `ldVal_valBytes`) are copied from the proof
module (`Silmaril/Proofs/X86/Concurrency/Cir/Tv.lean`), which this topic does not import.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvCfg

open Silmaril.X86 (State)
open Silmaril.X86.Ext (Sz leBytes leValue)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (stepSym memStep storeStep rmwStep valBytes ldVal writeOk readOk)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.Tv (XThread XMem binOf)
open Silmaril.X86.Concurrency.Cir.Csl (TStep)
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-! ## What one step does -/

/-- **The meaning of a checker kind** for one x86 step from `s` (instruction length `n`) with
actions `acts` to `s'`. -/
def KSem (k : Kind) (n : Nat) (s : State) (acts : List XAct) (s' : State) : Prop :=
  match k with
  | .op st => ∀ a : Stmt, a.demode = st → ∃ (o : Option Lab) (rs' : Regs),
      TStep a (regsOf s) o .skip rs' ∧ acts = o.toList.flatMap Lab.acts ∧
      s'.rip = s.rip + BitVec.ofNat 64 n ∧ regsOf s' = rs'
  | .flag z => acts = [] ∧ regsOf s' = regsOf s ∧ s'.rip = s.rip + BitVec.ofNat 64 n ∧
      s'.flags.zero = some (truthy (z.eval (regsOf s)))
  | .skip => acts = [] ∧ regsOf s' = regsOf s ∧ s'.rip = s.rip + BitVec.ofNat 64 n
  | .jmp rel => acts = [] ∧ regsOf s' = regsOf s ∧
      s'.rip = s.rip + BitVec.ofNat 64 n + rel.signExtend 64
  | .jcc ne rel => acts = [] ∧ regsOf s' = regsOf s ∧ ∃ b, s.flags.zero = some b ∧
      s'.rip = if b != ne then s.rip + BitVec.ofNat 64 n + rel.signExtend 64
        else s.rip + BitVec.ofNat 64 n

/-! ## Registers -/

theorem regsOf_write (s : State) (r : Reg) (v : Word) :
    regsOf (s.write r v) = (regsOf s).set r v := by
  funext q
  simp only [regsOf, Regs.set]
  exact State.read_write s r q v

theorem regsOf_dwrite (s : State) (r : Reg) (v : BitVec 32) :
    regsOf (Sz.d.write s r v) = (regsOf s).set r (v.setWidth 64) := regsOf_write s r _

/-! ## Bits and bytes -/

@[simp] theorem dbytes : Sz.d.bytes = 4 := rfl

theorem mask_toNat (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 0xffffffff).toNat = x.toNat % 2 ^ 32 := by
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  have : (0xffffffff : Nat) % 2 ^ 64 = 2 ^ 32 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem mask_eq (x : BitVec 64) :
    x &&& BitVec.ofNat 64 0xffffffff = (x.setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; rw [mask_toNat]; simp; omega

theorem mask32_eval (e : Expr) (rs : Regs) :
    (mask32 e).eval rs = ((e.eval rs).setWidth 32).setWidth 64 := by
  simp only [mask32, Expr.eval, BinOp.eval]; exact mask_eq _

theorem shl_succ (x : BitVec 64) (k : Nat) : x <<< (k + 1) = (x <<< k) + (x <<< k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two, Nat.add_mod]

theorem idxE_eval (r : Reg) (rs : Regs) : ∀ k, (idxE r k).eval rs = rs r <<< k
  | 0 => by simp [idxE, Expr.eval]
  | k + 1 => by rw [shl_succ, ← idxE_eval r rs k]; rfl

theorem addrX_eval {a : XMem} {e : Expr} (h : addrX a = some e) (s : State) (next : Word) :
    e.eval (regsOf s) = a.addr s next := by
  obtain ⟨base, index, disp, hr⟩ := a
  cases base <;> simp only [addrX, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    cases index <;>
    simp [Expr.eval, BinOp.eval, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Base.value,
      idxE_eval, Silmaril.X86.Ext.Index.value, regsOf]

theorem leBytes_eq (w : BitVec 64) (k : Nat) : leBytes w k = natBytes w.toNat k := by
  apply List.ext_getElem
  · simp [natBytes]
  · intro j h₁ h₂
    simp only [leBytes, List.getElem_ofFn, natBytes, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp [Silmaril.Machine.LittleEndian.wordByte, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, pow_mul]

theorem natBytes_mod (x k : Nat) : natBytes (x % 2 ^ (8 * k)) k = natBytes x k := by
  apply List.ext_getElem
  · simp [natBytes]
  · intro j h₁ h₂
    simp only [natBytes, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have hk : 2 ^ (8 * k) = 256 ^ j * 256 ^ (k - j) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      simp [natBytes] at h₁
      omega
    rw [hk, Nat.mod_mul_right_div_self]
    simp [natBytes] at h₁
    exact Nat.mod_mod_of_dvd _ (dvd_pow_self 256 (by omega))

theorem ldVal_valBytes (v : Nat) (k : Nat) :
    ldVal (valBytes v k) = BitVec.ofNat 64 (v % 2 ^ (8 * k)) := by
  simp only [ldVal, valBytes, Silmaril.X86.Ext.leValue_leBytes, BitVec.toNat_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rcases Nat.lt_or_ge k 8 with hk | hk
  · rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8 * k ≤ 64))]
  · have h1 : v % 2 ^ 64 < 2 ^ (8 * k) :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.mod_eq_of_lt h1, Nat.mod_mod, Nat.mod_mod_of_dvd v (Nat.pow_dvd_pow 2 (by omega : 64 ≤ 8 * k))]

/-- The bytes of a 4-byte read of `v` are those of `v mod 2^32`. -/
theorem valBytes4 (v : Nat) : valBytes v 4 = natBytes (v % 2 ^ 32) 4 := by
  rw [valBytes, leBytes_eq, BitVec.toNat_ofNat]
  rw [← natBytes_mod (v % 2 ^ 64) 4, ← natBytes_mod (v % 2 ^ 32) 4]
  congr 1
  rw [Nat.mod_mod_of_dvd v (by decide : 2 ^ (8 * 4) ∣ 2 ^ 64)]
  simp

/-- The 32-bit value of a 4-byte read of `v`. -/
theorem ldv32 (v : Nat) : (ldVal (valBytes v 4)).setWidth 32 = BitVec.ofNat 32 (v % 2 ^ 32) := by
  rw [ldVal_valBytes]
  apply BitVec.eq_of_toNat_eq
  simp

/-- A 32-bit value written to a register is the CIR value of its `toNat`. -/
theorem sw64 (x : BitVec 32) : x.setWidth 64 = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq; simp

theorem leBytes4 (x : BitVec 32) : leBytes (x.setWidth 64) 4 = natBytes x.toNat 4 := by
  rw [leBytes_eq]; simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem lt32 (v : Nat) : v % 2 ^ 32 < 2 ^ (8 * 4) := Nat.mod_lt _ (by decide)

/-- The bytes `lock xadd` writes, for a read of `v`. -/
theorem xadd_bytes (v : Nat) (s : State) (src : Reg) :
    leBytes (((ldVal (valBytes v Sz.d.bytes)).setWidth Sz.d.bits + Sz.d.read s src).setWidth 64)
      Sz.d.bytes = natBytes ((v % 2 ^ 32 + (s.read src).toNat) % 2 ^ (8 * 4)) 4 := by
  show leBytes (((ldVal (valBytes v 4)).setWidth 32 + (s.read src).setWidth 32).setWidth 64) 4 = _
  rw [ldv32, leBytes4]
  congr 1
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

/-! ## Demoding -/

theorem demode_load {a : Stmt} {d sz fl e} (h : a.demode = .load d .rlx sz fl e) :
    ∃ m, a = .load d m sz fl e := by
  cases a <;> simp_all [Stmt.demode]

theorem demode_store {a : Stmt} {sz fl e v} (h : a.demode = .store .rlx sz fl e v) :
    ∃ m, a = .store m sz fl e v := by
  cases a <;> simp_all [Stmt.demode]

theorem demode_rmw {a : Stmt} {d sz op e arg} (h : a.demode = .rmw d .rlx sz op e arg) :
    ∃ m, a = .rmw d m sz op e arg := by
  cases a <;> simp_all [Stmt.demode]

theorem demode_assign {a : Stmt} {d e} (h : a.demode = .assign d e) : a = .assign d e := by
  cases a <;> simp_all [Stmt.demode]

@[simp] theorem regsOf_mk (x : State) (r : Word) (f : Silmaril.X86.Flags) (b : Word) :
    regsOf { regs := x.regs, rip := r, flags := f, fsBase := b } = regsOf x := rfl

theorem stepSym_mem' {t : XThread} {dom : List Nat} {s : State} {i : Atomic9.Instr} {n : Nat}
    (hf : t.fetch s = some (i, n))
    (hni : (MemEvent.atomic9Accesses i s n).all Litmus.Event.inert = false) :
    stepSym t dom s = memStep t.regions dom i s n := by
  simp [stepSym, hf, hni]

/-! ## Flags and ALU results -/

theorem truthy_eq (a b : Word) : truthy (BinOp.eval .eq a b) = decide (a = b) := by
  by_cases h : a = b <;> simp [truthy, BinOp.eval, h]
theorem zcmp (x y : BitVec 32) :
    Silmaril.X86.Ext.isZeroN (x - y) = decide (x.setWidth 64 = y.setWidth 64) := by
  unfold Silmaril.X86.Ext.isZeroN
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
  constructor <;> intro h <;> bv_omega
theorem ztest (x y : BitVec 32) :
    Silmaril.X86.Ext.isZeroN (x &&& y) = decide (x.setWidth 64 &&& y.setWidth 64 = 0#64) := by
  unfold Silmaril.X86.Ext.isZeroN
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
  have e : x.setWidth 64 &&& y.setWidth 64 = (x &&& y).setWidth 64 := by
    ext i hi; simp
  rw [e]
  constructor <;> intro h <;> bv_omega
theorem ztest' (a b : Word) :
    Silmaril.X86.Ext.isZeroN (a.setWidth 32 &&& b.setWidth 32) =
      decide (((BinOp.and.eval a b).setWidth 32).setWidth 64 = 0#64) := by
  have e : (BinOp.and.eval a b).setWidth 32 = a.setWidth 32 &&& b.setWidth 32 := by
    ext i hi; simp [BinOp.eval]
  rw [e, ztest]
  congr 2

theorem ztestA (x : BitVec 64) (imm : BitVec 8) :
    Silmaril.X86.Ext.isZeroN (x.setWidth 8 &&& imm) =
      decide (BinOp.and.eval x (imm.setWidth 64) = 0#64) := by
  unfold Silmaril.X86.Ext.isZeroN BinOp.eval
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
  have e : x &&& imm.setWidth 64 = (x.setWidth 8 &&& imm).setWidth 64 := by
    ext i hi
    by_cases h8 : i < 8
    · simp [h8, BitVec.getLsbD_eq_getElem hi]
    · simp [h8, BitVec.getLsbD_of_ge imm i (by omega)]
  rw [e]
  constructor <;> intro h <;> bv_omega
theorem alu_val (op : Silmaril.X86.AluOp) (o : BinOp) (hb : binOf op = some o) (x y : Word) :
    (Silmaril.X86.Ext.AluOp.resultN op (x.setWidth 32) (y.setWidth 32)).setWidth 64 =
      ((o.eval x y).setWidth 32).setWidth 64 := by
  congr 1
  cases op <;> simp [binOf] at hb <;> subst hb <;> simp only [BinOp.eval, Silmaril.X86.Ext.AluOp.resultN]
  all_goals first
    | bv_omega
    | (ext i hi; simp)

/-! ## One instruction -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
/-- **One instruction**: every branch of the symbolic step of an instruction of the checker's
table is described by its kind's `KSem`. -/
theorem kind_sound {t : XThread} {dom : List Nat} {s : State} {i : Atomic9.Instr} {n : Nat}
    {k : Kind} (hk : kindOf i = some k) (hf : t.fetch s = some (i, n))
    {outs : List (List XAct × State)} (hs : stepSym t dom s = some outs)
    {acts : List XAct} {s' : State} (ho : (acts, s') ∈ outs) : KSem k n s acts s' := by
  unfold kindOf at hk
  split at hk
  · -- movI32
    rename_i d imm
    cases hk
    simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      Silmaril.X86.Ext.retire] at hs
    subst hs
    simp only [List.mem_singleton, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    intro a ha
    rw [demode_assign ha]
    exact ⟨none, _, .assign, rfl, rfl, (regsOf_write s d _).trans (congrArg _ (BitVec.eq_of_toNat_eq (by simp [Expr.eval])))⟩
  · -- mov r, r
    rename_i d src
    cases hk
    simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM] at hs
    subst hs
    simp only [List.mem_singleton, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    intro a ha
    rw [demode_assign ha]
    exact ⟨none, _, .assign, rfl, rfl, (regsOf_write s d _).trans (by simp [mask32_eval, Expr.eval, Sz.read, regsOf])⟩
  · -- lea
    rename_i d m
    cases hm : addrX m with
    | none => simp [hm] at hk
    | some e =>
      simp only [hm, Option.map_some, Option.some.injEq] at hk
      subst hk
      simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec,
      Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep, Option.map] at hs
      subst hs
      simp only [List.mem_singleton, Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl⟩ := ho
      intro a ha
      rw [demode_assign ha]
      refine ⟨none, _, .assign, rfl, rfl, (regsOf_write s d _).trans ?_⟩
      simp [mask32_eval, addrX_eval hm s (s.rip + BitVec.ofNat 64 n)]
  · -- alu r, r
    rename_i op d src
    split at hk
    · rename_i hop
      subst hop
      cases hk
      simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec,
      Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep, Option.map] at hs
      subst hs
      simp only [List.mem_singleton, Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl⟩ := ho
      refine ⟨rfl, rfl, rfl, ?_⟩
      simp [Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN, Sz.read, regsOf, Expr.eval,
        mask32_eval, truthy_eq, zcmp]
    · cases hb : binOf op with
      | none => simp [hb] at hk
      | some o =>
        simp only [hb, Option.map_some, Option.some.injEq] at hk
        subst hk
        rename_i hop
        simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec,
      Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep, Option.map] at hs
        simp only [hop, ite_false] at hs
        cases hs
        simp only [List.mem_singleton, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        intro a ha
        rw [demode_assign ha]
        refine ⟨none, _, .assign, rfl, rfl, (regsOf_write s d _).trans ?_⟩
        simp only [mask32_eval, Expr.eval]
        exact congrArg ((regsOf s).set d) (alu_val op o hb (s.read d) (s.read src))
  · -- aluI8 r, imm
    rename_i op d imm
    split at hk
    · rename_i hop
      subst hop
      cases hk
      simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec,
      Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep, Option.map] at hs
      subst hs
      simp only [List.mem_singleton, Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl⟩ := ho
      refine ⟨rfl, rfl, rfl, ?_⟩
      simp [Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN, Sz.read, regsOf, Expr.eval,
        mask32_eval, truthy_eq, zcmp]
    · cases hb : binOf op with
      | none => simp [hb] at hk
      | some o =>
        simp only [hb, Option.map_some, Option.some.injEq] at hk
        subst hk
        rename_i hop
        simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec,
      Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep, Option.map] at hs
        simp only [hop, ite_false] at hs
        cases hs
        simp only [List.mem_singleton, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        intro a ha
        rw [demode_assign ha]
        refine ⟨none, _, .assign, rfl, rfl, (regsOf_write s d _).trans ?_⟩
        simp only [mask32_eval, Expr.eval]
        have hy : (BitVec.ofNat 64 (BitVec.signExtend 32 imm).toNat).setWidth 32 =
            BitVec.signExtend 32 imm := by
          apply BitVec.eq_of_toNat_eq; simp
        have := alu_val op o hb (s.read d) (BitVec.ofNat 64 (BitVec.signExtend 32 imm).toNat)
        rw [hy] at this
        exact congrArg ((regsOf s).set d) this
  · -- test r, r
    rename_i d src
    cases hk
    simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec,
      Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep, Option.map] at hs
    subst hs
    simp only [List.mem_singleton, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    refine ⟨rfl, rfl, rfl, ?_⟩
    simp [Silmaril.X86.Ext.logicFlagsN, Sz.read, regsOf, Expr.eval, mask32_eval, truthy_eq]
    exact ztest' _ _
  · -- test al, imm8
    rename_i imm
    cases hk
    simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec,
      Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.aluStep, Option.map] at hs
    subst hs
    simp only [List.mem_singleton, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    refine ⟨rfl, rfl, rfl, ?_⟩
    simp [Silmaril.X86.Ext.logicFlagsN, regsOf, Expr.eval, mask32_eval, truthy_eq, ztestA]
  · -- mov [m], r
    rename_i m src
    cases hm : addrX m with
    | none => simp [hm] at hk
    | some e =>
      simp only [hm, Option.map_some, Option.some.injEq] at hk
      subst hk
      rw [stepSym_mem' hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, storeStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_singleton, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        intro a ha
        obtain ⟨md, rfl⟩ := demode_store ha
        refine ⟨_, _, .store, ?_, rfl, rfl⟩
        simp [Lab.acts, stAct, flavOf, addrX_eval hm s (s.rip + BitVec.ofNat 64 n), Expr.eval,
          Sz.read, leBytes4, regsOf, natBytes_mod]
      · cases hs
  · -- mov [m], imm
    rename_i m imm
    cases hm : addrX m with
    | none => simp [hm] at hk
    | some e =>
      simp only [hm, Option.map_some, Option.some.injEq] at hk
      subst hk
      rw [stepSym_mem' hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, storeStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_singleton, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        intro a ha
        obtain ⟨md, rfl⟩ := demode_store ha
        refine ⟨_, _, .store, ?_, rfl, rfl⟩
        simp [Lab.acts, stAct, flavOf, addrX_eval hm s (s.rip + BitVec.ofNat 64 n), Expr.eval,
          leBytes4, Nat.mod_eq_of_lt imm.isLt]
      · cases hs
  · -- mov r, [m]
    rename_i d m
    cases hm : addrX m with
    | none => simp [hm] at hk
    | some e =>
      simp only [hm, Option.map_some, Option.some.injEq] at hk
      subst hk
      rw [stepSym_mem' hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_map] at ho
        obtain ⟨v, -, hv⟩ := ho
        simp only [Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        intro a ha
        obtain ⟨md, rfl⟩ := demode_load ha
        refine ⟨_, _, .load (v := v % 2 ^ 32) (lt32 v), ?_, rfl, ?_⟩
        · simp [Lab.acts, ldAct, flavOf, addrX_eval hm s (s.rip + BitVec.ofNat 64 n), valBytes4]
        · refine (regsOf_write s d _).trans ?_
          show (regsOf s).set _ ((BitVec.setWidth 32 (ldVal (valBytes v 4))).setWidth 64) = _
          rw [ldv32]; congr 1; apply BitVec.eq_of_toNat_eq; simp
      · cases hs
  · -- xchg [m], r
    rename_i m src
    cases hm : addrX m with
    | none => simp [hm] at hk
    | some e =>
      simp only [hm, Option.map_some, Option.some.injEq] at hk
      subst hk
      rw [stepSym_mem' hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, rmwStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_map] at ho
        obtain ⟨v, -, hv⟩ := ho
        simp only [Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        intro a ha
        obtain ⟨md, rfl⟩ := demode_rmw ha
        refine ⟨_, _, .rmw (old := v % 2 ^ 32) (lt32 v), ?_, rfl, ?_⟩
        · simp [Lab.acts, rmwAct, addrX_eval hm s (s.rip + BitVec.ofNat 64 n), valBytes4,
            RmwOp.result, Expr.eval, Sz.read, leBytes4, regsOf]
        · refine (regsOf_write s src _).trans ?_
          show (regsOf s).set _ ((BitVec.setWidth 32 (ldVal (valBytes v 4))).setWidth 64) = _
          rw [ldv32]; congr 1; apply BitVec.eq_of_toNat_eq; simp
      · cases hs
  · -- lock xadd [m], r
    rename_i m src
    cases hm : addrX m with
    | none => simp [hm] at hk
    | some e =>
      simp only [hm, Option.map_some, Option.some.injEq] at hk
      subst hk
      rw [stepSym_mem' hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, rmwStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_map] at ho
        obtain ⟨v, -, hv⟩ := ho
        simp only [Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        intro a ha
        obtain ⟨md, rfl⟩ := demode_rmw ha
        refine ⟨_, _, .rmw (old := v % 2 ^ 32) (lt32 v), ?_, rfl, ?_⟩
        · rw [xadd_bytes]
          simp [Lab.acts, rmwAct, addrX_eval hm s (s.rip + BitVec.ofNat 64 n), valBytes4,
            RmwOp.result, Expr.eval, regsOf]
        · refine (regsOf_write s src _).trans ?_
          show (regsOf s).set _ ((BitVec.setWidth 32 (ldVal (valBytes v 4))).setWidth 64) = _
          rw [ldv32]; congr 1; apply BitVec.eq_of_toNat_eq; simp
      · cases hs
  · -- nop
    cases hk
    simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Atomic9.execNew, Ext9.exec,
      Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
      MemEvent.atomic9NewAccesses] at hs
    subst hs
    simp only [List.mem_singleton, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    exact ⟨rfl, rfl, rfl⟩
  · -- pause
    cases hk
    simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Atomic9.execNew, Ext9.exec,
      Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
      MemEvent.atomic9NewAccesses] at hs
    subst hs
    simp only [List.mem_singleton, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    exact ⟨rfl, rfl, rfl⟩
  · -- jmp
    rename_i rel
    cases hk
    simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Atomic9.execNew, Ext9.exec,
      Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
      MemEvent.atomic9NewAccesses] at hs
    subst hs
    simp only [List.mem_singleton, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    exact ⟨rfl, rfl, rfl⟩
  · -- je
    rename_i rel
    cases hk
    cases hz : s.flags.zero with
    | none =>
      simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Atomic9.execNew, Ext9.exec,
      Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
      MemEvent.atomic9NewAccesses] at hs
      simp [Silmaril.X86.Ext.Cond.eval, hz] at hs
    | some b =>
      simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Atomic9.execNew, Ext9.exec,
      Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
      MemEvent.atomic9NewAccesses] at hs
      simp only [Silmaril.X86.Ext.Cond.eval, hz] at hs
      cases b <;> simp at hs <;> subst hs <;> simp only [List.mem_singleton, Prod.mk.injEq] at ho <;>
        obtain ⟨rfl, rfl⟩ := ho <;> exact ⟨rfl, rfl, _, hz, by simp⟩
  · -- jne
    rename_i rel
    cases hk
    cases hz : s.flags.zero with
    | none =>
      simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Atomic9.execNew, Ext9.exec,
      Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
      MemEvent.atomic9NewAccesses] at hs
      simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot, hz] at hs
    | some b =>
      simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Atomic9.execNew, Ext9.exec,
      Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
      MemEvent.atomic9NewAccesses] at hs
      simp only [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot, Option.map, hz] at hs
      cases b <;> simp at hs <;> subst hs <;> simp only [List.mem_singleton, Prod.mk.injEq] at ho <;>
        obtain ⟨rfl, rfl⟩ := ho <;> exact ⟨rfl, rfl, _, hz, by simp⟩
  · cases hk

end Silmaril.Proofs.X86.Concurrency.Cir.TvCfg

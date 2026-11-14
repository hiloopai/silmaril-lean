module

public import Silmaril.X86.Concurrency.Cir.Rc.Tv.Defs

/-!
# Proofs: the refcount translation validator is sound

* `op_sound`: every branch of the symbolic x86 step of an instruction the checker accepts is one
  `Csl.TStep` of its CIR statement, with the same memory actions, the registers outside the
  clobber set equal, and the zero-flag fact the checker records;
* `je_sound`: a `je rel8` reads a defined zero flag and jumps or falls through;
* `walk_sound`: the simulation along an x86 run.

The byte and register lemmas are **restated** from `Proofs/…/TvCfg/X86.lean` and
`Proofs/…/Tv.lean` (other topics' proofs modules, not imported).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc.TvP

open Silmaril.X86 (State)
open Silmaril.X86.Ext (Sz leBytes leValue)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (stepSym memStep storeStep rmwStep valBytes ldVal writeOk readOk)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Rc
open Silmaril.X86.Concurrency.Cir.Rc.Tv
open Silmaril.X86.Concurrency.Cir.TvCfg (addrX idxE regsOf XStep XRun TRun jtarget)
open Silmaril.X86.Concurrency.Cir.Tv (XThread XMem binOf fetchAt)
open Silmaril.X86.Concurrency.Cir.Csl (TStep)
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-! ## Restated helpers -/

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
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.mod_eq_of_lt h1, Nat.mod_mod,
      Nat.mod_mod_of_dvd v (Nat.pow_dvd_pow 2 (by omega : 64 ≤ 8 * k))]

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

theorem demode_load {a : Stmt} {d sz fl e} (h : a.demode = .load d .rlx sz fl e) :
    ∃ m, a = .load d m sz fl e := by
  cases a <;> simp_all [Stmt.demode]

theorem demode_store {a : Stmt} {sz fl e v} (h : a.demode = .store .rlx sz fl e v) :
    ∃ m, a = .store m sz fl e v := by
  cases a <;> simp_all [Stmt.demode]

theorem demode_rmw {a : Stmt} {d sz op e arg} (h : a.demode = .rmw d .rlx sz op e arg) :
    ∃ m, a = .rmw d m sz op e arg := by
  cases a <;> simp_all [Stmt.demode]

theorem stepSym_mem' {t : XThread} {dom : List Nat} {s : State} {i : Atomic9.Instr} {n : Nat}
    (hf : t.fetch s = some (i, n))
    (hni : (MemEvent.atomic9Accesses i s n).all Litmus.Event.inert = false) :
    stepSym t dom s = memStep t.regions dom i s n := by
  simp [stepSym, hf, hni]

theorem w_add (x y : BitVec 32) : (x.setWidth 64 + y.setWidth 64).setWidth 32 = x + y := by bv_omega
theorem w_sub (x y : BitVec 32) : (x.setWidth 64 - y.setWidth 64).setWidth 32 = x - y := by bv_omega
theorem w_and (x y : BitVec 32) : (x.setWidth 64 &&& y.setWidth 64).setWidth 32 = x &&& y := by
  ext i hi; simp
theorem w_or (x y : BitVec 32) : (x.setWidth 64 ||| y.setWidth 64).setWidth 32 = x ||| y := by
  ext i hi; simp
theorem w_xor (x y : BitVec 32) : (x.setWidth 64 ^^^ y.setWidth 64).setWidth 32 = x ^^^ y := by
  ext i hi; simp
theorem w64 (f : BitVec 64 → BitVec 64 → BitVec 64) (x y : BitVec 64) :
    f (x.setWidth 64) (y.setWidth 64) = f x y := by simp

/-- A locked ALU operation computed at 64 bits and cut to the operand size is the x86 result. -/
theorem aluI_val (op : Silmaril.X86.AluOp) (o : BinOp) (hb : binOf op = some o) (sz : Sz)
    (x y : BitVec sz.bits) :
    (o.eval (x.setWidth 64) (y.setWidth 64)).setWidth sz.bits =
      Silmaril.X86.Ext.AluOp.resultN op x y := by
  cases op <;> simp [binOf] at hb <;> subst hb <;> cases sz <;>
    simp only [BinOp.eval, Silmaril.X86.Ext.AluOp.resultN]
  all_goals first
    | exact w_add x y | exact w_sub x y | exact w_and x y | exact w_or x y | exact w_xor x y
    | exact w64 (· + ·) x y | exact w64 (· - ·) x y | exact w64 (· &&& ·) x y
    | exact w64 (· ||| ·) x y | exact w64 (· ^^^ ·) x y

/-! ## Registers outside the clobber set -/

/-- CIR registers `rs` stand for the core `s` outside the clobber set `K`. -/
def Rel (K : List Reg) (rs : Regs) (s : State) : Prop := ∀ r, r ∉ K → regsOf s r = rs r

theorem eval_congr {e : Expr} {rs rs' : Regs} (h : ∀ r ∈ e.regs, rs r = rs' r) :
    e.eval rs = e.eval rs' := by
  induction e with
  | lit v => rfl
  | reg r => exact h r (by simp [Expr.regs])
  | bin o a b iha ihb =>
    simp only [Expr.eval]
    rw [iha (fun r hr => h r (by simp [Expr.regs, hr])),
      ihb (fun r hr => h r (by simp [Expr.regs, hr]))]

theorem addrK_eval {K : List Reg} {a : XMem} {e : Expr} (h : addrK K a = some e) {s : State}
    {rs : Regs} (hR : Rel K rs s) (next : Word) : e.eval rs = a.addr s next := by
  unfold addrK at h
  split at h
  · rename_i e₀ hx
    split at h
    · rename_i hall
      cases h
      rw [← addrX_eval hx s next]
      refine eval_congr fun r hr => (hR r ?_).symm
      have := List.all_eq_true.mp hall r hr
      simpa using this
    · cases h
  · cases h

theorem Rel.set_in {K : List Reg} {rs : Regs} {s : State} (h : Rel K rs s) {d : Reg} (hd : d ∈ K)
    (v : Word) : Rel K (rs.set d v) s := by
  intro r hr
  have : r ≠ d := fun e => hr (e ▸ hd)
  simp [Regs.set, this, h r hr]

theorem Rel.write {K : List Reg} {rs : Regs} {s : State} (h : Rel K rs s) (d : Reg) (v : Word) :
    Rel K (rs.set d v) (s.write d v) := by
  intro r hr
  rw [regsOf_write]
  by_cases e : r = d
  · subst e; simp [Regs.set]
  · simp [Regs.set, e, h r hr]

theorem truthy_eq (a b : Word) : truthy (BinOp.eval .eq a b) = decide (a = b) := by
  by_cases h : a = b <;> simp [truthy, BinOp.eval, h]

/-! ## One instruction -/

theorem flagsN_zero (op : Silmaril.X86.AluOp) (x y : BitVec 32) :
    (Silmaril.X86.Ext.AluOp.flagsN op x y).zero =
      some (Silmaril.X86.Ext.isZeroN (Silmaril.X86.Ext.AluOp.resultN op x y)) := by
  cases op <;> rfl

theorem leBytes4' (x : BitVec Sz.d.bits) : leBytes (x.setWidth 64) 4 = natBytes x.toNat 4 :=
  leBytes4 x

/-- The 64-bit CIR computation of a 32-bit locked ALU op, cut to 32 bits, is the x86 result. -/
theorem alu32 {op : Silmaril.X86.AluOp} {o : BinOp} (hb : binOf op = some o) {old : Nat}
    (h32 : old < 2 ^ 32) (imm : BitVec 32) :
    (o.eval (BitVec.ofNat 64 old) (BitVec.ofNat 64 imm.toNat)).setWidth 32 =
      Silmaril.X86.Ext.AluOp.resultN op (BitVec.ofNat 32 old) imm := by
  have k : (o.eval ((BitVec.ofNat 32 old).setWidth 64) (imm.setWidth 64)).setWidth 32 =
      Silmaril.X86.Ext.AluOp.resultN op (BitVec.ofNat 32 old) imm :=
    aluI_val op o hb .d (BitVec.ofNat 32 old) imm
  have e1 : (BitVec.ofNat 32 old).setWidth 64 = BitVec.ofNat 64 old := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  have e2 : imm.setWidth 64 = BitVec.ofNat 64 imm.toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [e1, e2] at k; exact k

/-- The zero-flag expression of a locked ALU op is the x86 zero flag. -/
theorem zf_val {op : Silmaril.X86.AluOp} {o : BinOp} (hb : binOf op = some o) (old : Nat)
    (h32 : old < 2 ^ 32) (imm : BitVec 32) (d : Reg) (rs : Regs) :
    Silmaril.X86.Ext.isZeroN (Silmaril.X86.Ext.AluOp.resultN op (BitVec.ofNat 32 old) imm) =
      truthy ((zfOf o d imm.toNat).eval (rs.set d (BitVec.ofNat 64 old))) := by
  have key := alu32 hb h32 imm
  have hd : (rs.set d (BitVec.ofNat 64 old)) d = BitVec.ofNat 64 old := by simp [Regs.set]
  simp only [zfOf, Expr.eval, hd, truthy_eq]
  have hm : BinOp.and.eval (o.eval (BitVec.ofNat 64 old) (BitVec.ofNat 64 imm.toNat))
      (BitVec.ofNat 64 0xffffffff) =
      ((o.eval (BitVec.ofNat 64 old) (BitVec.ofNat 64 imm.toNat)).setWidth 32).setWidth 64 :=
    mask_eq _
  rw [hm, key]
  unfold Silmaril.X86.Ext.isZeroN
  by_cases hz : Silmaril.X86.Ext.AluOp.resultN op (BitVec.ofNat 32 old) imm = 0#32
  · rw [hz]; simp
  · have : (Silmaril.X86.Ext.AluOp.resultN op (BitVec.ofNat 32 old) imm).setWidth 64 ≠ 0#64 := by
      intro e; apply hz; apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_setWidth] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))] at this
      simpa using this
    simp [hz, this]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
/-- **One instruction is sound**: every branch of the symbolic step of an instruction the
checker accepts is one CIR step of its statement, with the same actions, the relation kept
outside the clobber set, and the checker's zero-flag fact. -/
theorem op_sound {t : XThread} {dom : List Nat} {K : List Reg} {i : Atomic9.Instr} {st : Stmt}
    {zf' : Option Expr} (hc : chkOp K i st = some zf') {s : State} {n : Nat}
    (hf : t.fetch s = some (i, n)) {outs : List (List XAct × State)}
    (hs : stepSym t dom s = some outs) {acts : List XAct} {s' : State} (ho : (acts, s') ∈ outs)
    {rs : Regs} (hR : Rel K rs s) :
    ∃ (lab : Lab) (rs' : Regs), TStep st rs (some lab) .skip rs' ∧ acts = lab.acts ∧
      s'.rip = s.rip + BitVec.ofNat 64 n ∧ Rel K rs' s' ∧
      (∀ z, zf' = some z → s'.flags.zero = some (truthy (z.eval rs'))) := by
  unfold chkOp at hc
  split at hc
  · -- `lock op [m], imm`
    rename_i op a imm d o e c heq
    split at hc
    · rename_i hcond
      obtain ⟨hdK, ha, hb, rfl⟩ := hcond
      cases hc
      obtain ⟨md, rfl⟩ := demode_rmw heq
      have hop : op ≠ .cmp := by rintro rfl; simp [binOf] at hb
      rw [stepSym_mem' hf (by simp [hop, MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, hop, ite_false, rmwStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_map] at ho
        obtain ⟨v, -, hv⟩ := ho
        simp only [Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        have hx :
            (ldVal (valBytes v Sz.d.bytes)).setWidth Sz.d.bits = BitVec.ofNat 32 (v % 2 ^ 32) :=
          ldv32 v
        have key : (o.eval (BitVec.ofNat 64 (v % 2 ^ 32)) (BitVec.ofNat 64 imm.toNat)).toNat %
            2 ^ (8 * 4) = (Silmaril.X86.Ext.AluOp.resultN op (BitVec.ofNat 32 (v % 2 ^ 32))
              imm).toNat := by
          rw [← alu32 hb (Nat.mod_lt _ (by decide)) imm]; simp [BitVec.toNat_setWidth]
        have hse : imm.signExtend Sz.d.bits = imm := BitVec.signExtend_eq imm
        refine ⟨_, _, .rmw (old := v % 2 ^ 32) (lt32 v), ?_, rfl, Rel.set_in hR hdK _, ?_⟩
        · rw [hx, hse, dbytes]
          erw [leBytes4]
          simp only [Lab.acts, rmwAct, addrK_eval ha hR (s.rip + BitVec.ofNat 64 n), valBytes4,
            RmwOp.result, Expr.eval, key]
          rfl
        · intro z hz
          obtain rfl := Option.some.inj hz.symm
          rw [hx, hse]
          exact (flagsN_zero op _ imm).trans
            (congrArg some (zf_val hb (v % 2 ^ 32) (Nat.mod_lt _ (by decide)) imm d rs))
      · cases hs
    · cases hc
  · -- `mov r, [m]`
    rename_i dst a d e heq
    split at hc
    · rename_i hcond
      obtain ⟨rfl, ha⟩ := hcond
      cases hc
      obtain ⟨md, rfl⟩ := demode_load heq
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
        refine ⟨_, _, .load (v := v % 2 ^ 32) (lt32 v), ?_, rfl, ?_, fun z h => by cases h⟩
        · simp [Lab.acts, ldAct, flavOf, addrK_eval ha hR (s.rip + BitVec.ofNat 64 n), valBytes4]
        · have hw :
              (ldVal (valBytes v Sz.d.bytes)).setWidth Sz.d.bits = BitVec.ofNat 32 (v % 2 ^ 32)
              := ldv32 v
          intro r hr
          have := Rel.write hR d (BitVec.ofNat 64 (v % 2 ^ 32)) r hr
          rw [← this]
          show regsOf (Sz.d.write s d ((ldVal (valBytes v Sz.d.bytes)).setWidth Sz.d.bits)) r = _
          rw [hw, regsOf_dwrite, regsOf_write]
          congr 2
          apply BitVec.eq_of_toNat_eq; simp
      · cases hs
    · cases hc
  · -- `mov [m], r`
    rename_i a src e r heq
    split at hc
    · rename_i hcond
      obtain ⟨rfl, hsK, ha⟩ := hcond
      cases hc
      obtain ⟨md, rfl⟩ := demode_store heq
      rw [stepSym_mem' hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
        Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
      simp only [memStep, storeStep] at hs
      split at hs
      · cases hs
        simp only [List.mem_singleton, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        refine ⟨_, _, .store, ?_, rfl, fun q hq => hR q hq, fun z h => by cases h⟩
        have hsrc : rs r = s.read r := (hR r hsK).symm
        simp [Lab.acts, stAct, flavOf, addrK_eval ha hR (s.rip + BitVec.ofNat 64 n), Expr.eval,
          Sz.read, leBytes4, regsOf, natBytes_mod, hsrc]
      · cases hs
    · cases hc
  · cases hc

set_option linter.unusedSimpArgs false in
/-- **`je rel8`**: no actions, the registers unchanged, and a defined zero flag decides between
the target and the next instruction. -/
theorem je_sound {t : XThread} {dom : List Nat} {s : State} {rel : BitVec 8} {n : Nat}
    (hf : t.fetch s = some (.open9 (.ext8 (.base (.jcc8 .e rel))), n))
    {outs : List (List XAct × State)} (hs : stepSym t dom s = some outs) {acts : List XAct}
    {s' : State} (ho : (acts, s') ∈ outs) :
    acts = [] ∧ regsOf s' = regsOf s ∧ ∃ b, s.flags.zero = some b ∧
      s'.rip = if b then s.rip + BitVec.ofNat 64 n + rel.signExtend 64
        else s.rip + BitVec.ofNat 64 n := by
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
      obtain ⟨rfl, rfl⟩ := ho <;> exact ⟨rfl, rfl, _, rfl, by simp⟩

/-! ## Positions -/

theorem fetch_of_fetchAt {t : XThread} {o : Nat} {i : Atomic9.Instr} {n : Nat}
    (hf : fetchAt t o = some (i, n)) {s : State} (hrip : s.rip = t.base + BitVec.ofNat 64 o)
    (ho : o < 2 ^ 64) : t.fetch s = some (i, n) := by
  have h : (s.rip - t.base).toNat = o := by
    have e : t.base + BitVec.ofNat 64 o - t.base = BitVec.ofNat 64 o := by bv_omega
    rw [hrip, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  unfold Silmaril.X86.Litmus.Thread.fetch
  rw [h]
  exact hf

theorem fetchAt_le {t : XThread} {o : Nat} {i : Atomic9.Instr} {n : Nat}
    (h : fetchAt t o = some (i, n)) : o + n ≤ t.code.length := by
  unfold fetchAt at h
  split at h
  · split at h
    · cases h; rename_i hc; exact hc.1
    · cases h
  · cases h

/-- Nothing is fetched at or beyond the end of the code. -/
theorem fetch_beyond {t : XThread} {s : State} {p : Nat}
    (hrip : s.rip = t.base + BitVec.ofNat 64 p) (hp : p < 2 ^ 64) (hle : t.code.length ≤ p) :
    t.fetch s = none := by
  have h : (s.rip - t.base).toNat = p := by
    have e : t.base + BitVec.ofNat 64 p - t.base = BitVec.ofNat 64 p := by bv_omega
    rw [hrip, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  unfold Silmaril.X86.Litmus.Thread.fetch
  rw [h]
  simp only [List.drop_eq_nil_of_le hle, List.take_nil]
  rw [show Silmaril.X86.Atomic9.decode [] = none from rfl]

theorem base_inj {b : Word} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : b + BitVec.ofNat 64 x = b + BitVec.ofNat 64 y) : x = y := by
  have h' : BitVec.ofNat 64 x = BitVec.ofNat 64 y := by
    have := congrArg (· - b) h
    simpa using this
  have := congrArg BitVec.toNat h'
  simp at this
  omega

theorem base_add {b : Word} (x n : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 n = b + BitVec.ofNat 64 (x + n) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

theorem base_jtarget {b : Word} (o n : Nat) (rel : BitVec 8) :
    b + BitVec.ofNat 64 o + BitVec.ofNat 64 n + rel.signExtend 64 =
      b + BitVec.ofNat 64 (jtarget o n rel) := by
  rw [base_add, BitVec.add_assoc]
  congr 1
  unfold jtarget
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

theorem jtarget_lt (o n : Nat) (rel : BitVec 8) : jtarget o n rel < 2 ^ 64 := by
  unfold jtarget; exact BitVec.isLt _

/-! ## Blocks -/

theorem block_cons (s : Stmt) (l : List Stmt) :
    Stmt.block (s :: l) = if l = [] then s else .seq s (Stmt.block l) := by
  cases l <;> rfl

theorem trun_trans {a : Stmt} {rs : Regs} {l₁ : List Lab} {b : Stmt} {rs₁ : Regs}
    (h₁ : TRun a rs l₁ b rs₁) {l₂ : List Lab} {c : Stmt} {rs₂ : Regs}
    (h₂ : TRun b rs₁ l₂ c rs₂) : TRun a rs (l₁ ++ l₂) c rs₂ := by
  induction h₁ with
  | refl => exact h₂
  | tau h _ ih => exact .tau h (ih h₂)
  | lab h _ ih => exact .lab h (ih h₂)

/-- One labelled step of the head of a block, then the rest. -/
theorem trun_head {s : Stmt} {l : List Stmt} {rs : Regs} {lab : Lab} {rs₁ : Regs}
    (h : TStep s rs (some lab) .skip rs₁) :
    TRun (Stmt.block (s :: l)) rs [lab] (Stmt.block l) rs₁ := by
  rw [block_cons]
  split
  · rename_i hl; subst hl; exact .lab h .refl
  · exact .lab (.seq h) (.tau .seqSkip .refl)

/-- The exit item: taken, the block is at the cold path; not taken, at the rest. -/
theorem trun_exit {c : Expr} {slow : Stmt} {l : List Stmt} {rs : Regs} :
    (truthy (c.eval rs) = true → ∃ σ, TRun (Stmt.block (.ite c slow .skip :: l)) rs [] σ rs ∧
      (σ = slow ∨ ∃ k, σ = .seq slow k)) ∧
    (truthy (c.eval rs) = false →
      TRun (Stmt.block (.ite c slow .skip :: l)) rs [] (Stmt.block l) rs)
    := by
  rw [block_cons]
  constructor
  · intro ht
    split
    · exact ⟨slow, .tau (.iteT ht) .refl, Or.inl rfl⟩
    · exact ⟨.seq slow (Stmt.block l), .tau (.seq (.iteT ht)) .refl, Or.inr ⟨_, rfl⟩⟩
  · intro hf
    split
    · rename_i hl; subst hl; exact .tau (.iteF hf) .refl
    · exact .tau (.seq (.iteF hf)) (.tau .seqSkip .refl)

/-! ## The walk -/

/-- What the simulation gives at the end of an x86 run. -/
def Sim (t : XThread) (K : List Reg) (slow : Stmt) (σ0 : Stmt) (rs0 : Regs)
    (acc : List (List XAct)) (s' : State) : Prop :=
  ∃ σ rs', ∃ los : List (Option Lab), TRun σ0 rs0 (los.filterMap id) σ rs' ∧
    List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧ Rel K rs' s' ∧
    (s'.rip = t.endRip → σ = .skip) ∧
    (∀ p, p < 2 ^ 64 → t.code.length < p → s'.rip = t.base + BitVec.ofNat 64 p →
      σ = slow ∨ ∃ k, σ = .seq slow k)

/-- A run that has stopped is simulated by the empty CIR run, when its position is an offset
in the code (or the end). -/
theorem sim_nil {t : XThread} {K : List Reg} {slow σ0 : Stmt} {rs : Regs} {s : State} {o : Nat}
    (hlen : t.code.length < 2 ^ 64) (hrip : s.rip = t.base + BitVec.ofNat 64 o)
    (ho : o ≤ t.code.length) (hend : o = t.code.length → σ0 = .skip) (hR : Rel K rs s) :
    Sim t K slow σ0 rs [] s := by
  refine ⟨σ0, rs, [], .refl, .nil, hR, fun h => hend ?_, fun p hp hlp h => ?_⟩
  · rw [hrip, Silmaril.X86.Litmus.Thread.endRip] at h
    exact base_inj (by omega) hlen h
  · rw [hrip] at h
    have := base_inj (by omega) hp h
    omega

theorem walk_sim {t : XThread} {K : List Reg} {slow : Stmt} (hlen : t.code.length < 2 ^ 64) :
    ∀ (its : List RItem) (o : Nat) (zf : Option Expr) (ex : List Nat),
      walk t K zf o its = some ex →
      ∀ {s : State} {acc : List (List XAct)} {s' : State},
        s.rip = t.base + BitVec.ofNat 64 o → XRun t s acc s' → ∀ rs : Regs, Rel K rs s →
        (∀ z, zf = some z → s.flags.zero = some (truthy (z.eval rs))) →
        Sim t K slow (Stmt.block (its.map (RItem.stmt slow))) rs acc s' := by
  intro its
  induction its with
  | nil =>
    intro o zf ex hw s acc s' hrip hr rs hR _
    simp only [walk] at hw
    split at hw
    · rename_i ho
      subst ho
      cases hr with
      | nil => exact sim_nil hlen hrip (Nat.le_refl _) (fun _ => rfl) hR
      | cons h _ =>
        obtain ⟨dom, outs, hs, -⟩ := h
        simp [stepSym, fetch_beyond hrip hlen (Nat.le_refl _)] at hs
    · cases hw
  | cons it its ih =>
    intro o zf ex hw s acc s' hrip hr rs hR hzf
    simp only [walk] at hw
    split at hw
    · cases hw
    · rename_i i n hfa
      have hon := fetchAt_le hfa
      split at hw
      · rename_i hn
        have hf := fetch_of_fetchAt hfa hrip (by omega)
        cases hr with
        | nil =>
          exact sim_nil hlen hrip (by omega) (fun h => by omega) hR
        | cons hx tl =>
          rename_i acts s1 rest
          obtain ⟨dom, outs, hs, ho⟩ := hx
          cases it with
          | op st =>
            simp only at hw
            split at hw
            · rename_i zf' hc
              obtain ⟨lab, rs1, hst, hacts, hrip1, hR1, hzf1⟩ := op_sound hc hf hs ho hR
              have hrip1' : s1.rip = t.base + BitVec.ofNat 64 (o + n) := by
                rw [hrip1, hrip, base_add]
              obtain ⟨σ, rs', los, hrun, hfa2, hR', hend, hex⟩ :=
                ih (o + n) zf' ex hw hrip1' tl rs1 hR1 hzf1
              refine ⟨σ, rs', some lab :: los, ?_, .cons (by simp [hacts]) hfa2, hR', hend, hex⟩
              exact trun_trans (l₁ := [lab]) (trun_head hst) hrun
            · cases hw
          | exit c =>
            simp only at hw
            split at hw
            · rename_i rel
              split at hw
              · rename_i hcond
                obtain ⟨rfl, hgt⟩ := hcond
                obtain ⟨ex', hw', -⟩ := Option.map_eq_some_iff.mp hw
                obtain ⟨hacts, hregs, b, hb, hrip1⟩ := je_sound hf hs ho
                have hbt : b = truthy (c.eval rs) := by
                  have := hzf c rfl; rw [hb] at this; exact Option.some.inj this
                subst hacts
                have hR1 : Rel K rs s1 := fun r hr' => by rw [hregs]; exact hR r hr'
                cases b with
                | true =>
                  -- taken: the run is at the cold path and stops
                  have hrip1' : s1.rip = t.base + BitVec.ofNat 64 (jtarget o n rel) := by
                    rw [hrip1]; simp only [↓reduceIte]; rw [hrip, base_jtarget]
                  obtain ⟨σ, hσ, hslow⟩ := (trun_exit (slow := slow)
                    (l := its.map (RItem.stmt slow))).1 hbt.symm
                  cases tl with
                  | nil =>
                    refine ⟨σ, rs, [none], hσ, .cons (by simp) .nil, hR1, fun h => ?_,
                      fun _ _ _ _ => hslow⟩
                    rw [hrip1', Silmaril.X86.Litmus.Thread.endRip] at h
                    have := base_inj (jtarget_lt o n rel) hlen h
                    omega
                  | cons h _ =>
                    obtain ⟨dom', outs', hs', -⟩ := h
                    simp [stepSym, fetch_beyond hrip1' (jtarget_lt o n rel) (by omega)] at hs'
                | false =>
                  -- not taken: fall through
                  have hrip1' : s1.rip = t.base + BitVec.ofNat 64 (o + n) := by
                    rw [hrip1]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hrip, base_add]
                  have hrun0 := (trun_exit (slow := slow) (l := its.map (RItem.stmt slow))).2
                    hbt.symm
                  obtain ⟨σ, rs', los, hrun, hfa2, hR', hend, hex⟩ :=
                    ih (o + n) none ex' hw' hrip1' tl rs hR1 (fun z h => by cases h)
                  exact ⟨σ, rs', none :: los, trun_trans (l₁ := []) hrun0 hrun,
                    .cons (by simp) hfa2, hR', hend, hex⟩
              · cases hw
            · cases hw
      · cases hw

/-- **The checker is sound** (proof). -/
theorem rcTv_sound {t : XThread} {c : RCert} {ex : List Nat} (h : rcTv t c = some ex)
    (slow : Stmt) {s0 s : State} (h0 : s0.rip = t.base) {acc : List (List XAct)}
    (hr : XRun t s0 acc s) : Sim t c.K slow (c.body slow) (regsOf s0) acc s := by
  unfold rcTv at h
  split at h
  · rename_i hlen
    exact walk_sim hlen c.items 0 none ex h (by simp [h0]) hr (regsOf s0) (fun _ _ => rfl)
      (fun _ h => by cases h)
  · cases h

theorem flatten_of_forall₂ {acc : List (List XAct)} {los : List (Option Lab)}
    (h : List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los) :
    acc.flatten = (los.filterMap id).flatMap Lab.acts := by
  induction h with
  | nil => rfl
  | @cons a o l₁ l₂ hx _ ih =>
    rw [List.flatten_cons, ih, hx]
    cases o <;> simp

theorem walk_code {t t' : XThread} (h : t.code = t'.code) (K : List Reg) :
    ∀ (its : List RItem) (zf : Option Expr) (o : Nat), walk t K zf o its = walk t' K zf o its := by
  have hf : ∀ o, fetchAt t o = fetchAt t' o := fun o => by simp [fetchAt, h]
  intro its
  induction its with
  | nil => intro zf o; simp [walk, h]
  | cons it its ih =>
    intro zf o
    simp only [walk, hf o, h]
    split
    · rfl
    · split
      · cases it with
        | op st => simp only; split <;> simp [ih]
        | exit c => simp only; split <;> simp [ih]
      · rfl

theorem rcTv_code {t t' : XThread} (h : t.code = t'.code) (c : RCert) : rcTv t c = rcTv t' c := by
  unfold rcTv; rw [h, walk_code h]

end Silmaril.Proofs.X86.Concurrency.Cir.Rc.TvP

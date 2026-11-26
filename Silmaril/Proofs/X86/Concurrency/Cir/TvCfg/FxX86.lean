module

public import Silmaril.X86.Concurrency.Cir.TvCfg.Fx.Defs
public import Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.X86

/-!
# The translation validation: the new x86 instructions

Each lemma describes every branch of the symbolic step `stepSym` for
one new form of the checker's table (`TvCfg.Fx.fxKindOf`), in the style of `kind_sound`:

* `cas_sound`: `lock cmpxchg [m], r32` is one CIR `rmw rax _ 4 (cas rax)` step with the same
  actions. When `rax < 2^32` the registers are equal after it (x86 keeps `rax` on success, CIR
  writes the old value, which is then `rax`), and the zero flag is "the old value was `rax`";
* `lockSub_sound`: `lock sub [m], imm` is one CIR `rmw d _ 4 (sub imm)` step with the same
  actions. x86 changes no register, CIR changes `d`, and the zero flag is "the new value is `0`";
* `mov64_sound`: `mov d, src` (64 bits) is `assign d src`;
* `ret_none`: `stepSym` has no step for `ret` (it pops the stack, which is not a litmus access).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvCfg

open Silmaril.X86 (State)
open Silmaril.X86.Ext (Sz leBytes leValue)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (stepSym memStep storeStep rmwStep valBytes ldVal writeOk readOk)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx
open Silmaril.X86.Concurrency.Cir.Tv (XThread XMem binOf)
open Silmaril.X86.Concurrency.Cir.Csl (TStep)
open Silmaril.X86.MemoryModel.Litmus (XAct)

theorem demode_rmw' {a : Stmt} {d sz op e arg} (h : a.demode = .rmw d .rlx sz op e arg) :
    ∃ m, a = .rmw d m sz op e arg := by
  cases a <;> simp_all [Stmt.demode]

theorem ofNat_toNat_lt {x : Word} (h : x.toNat < 2 ^ 32) : x.toNat % 2 ^ 32 = x.toNat :=
  Nat.mod_eq_of_lt h

/-- `lock cmpxchg [m], src` (32 bits). -/
theorem cas_sound {t : XThread} {dom : List Nat} {s : State} {m : XMem} {src : Reg} {n : Nat}
    {a : Expr} (ha : addrX m = some a)
    (hf : t.fetch s = some (.new (.cmpxchg .d true (.mem m) src), n))
    {outs : List (List XAct × State)} (hs : stepSym t dom s = some outs)
    {acts : List XAct} {s' : State} (ho : (acts, s') ∈ outs) (hax : (s.read .rax).toNat < 2 ^ 32)
    {a' : Stmt} (hd : a'.demode = casStmt a src) :
    ∃ (o : Option Lab) (rs' : Regs), TStep a' (regsOf s) o .skip rs' ∧
      acts = o.toList.flatMap Lab.acts ∧ s'.rip = s.rip + BitVec.ofNat 64 n ∧ regsOf s' = rs' ∧
      s'.flags.zero = some (truthy ((casZ (s.read .rax)).eval rs')) := by
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
    obtain ⟨md, rfl⟩ := demode_rmw' hd
    have hx : (ldVal (valBytes v Sz.d.bytes)).setWidth Sz.d.bits = BitVec.ofNat 32 (v % 2 ^ 32) :=
      ldv32 v
    have hacc : Sz.d.read s .rax = BitVec.ofNat 32 (s.read .rax).toNat := by
      apply BitVec.eq_of_toNat_eq; simp [Sz.read]
    have hv32 : v % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have hiff : (Sz.d.read s .rax = (ldVal (valBytes v Sz.d.bytes)).setWidth Sz.d.bits) ↔
        (s.read .rax).toNat = v % 2 ^ 32 := by
      rw [hx, hacc]
      constructor
      · intro h; have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rwa [Nat.mod_eq_of_lt hax, Nat.mod_eq_of_lt hv32] at this
      · intro h; rw [h]
    have hcz : truthy ((casZ (s.read .rax)).eval
        ((regsOf s).set .rax (BitVec.ofNat 64 (v % 2 ^ 32)))) =
        decide ((s.read .rax).toNat = v % 2 ^ 32) := by
      simp only [casZ, Expr.eval, truthy_eq, Regs.set, ite_true]
      rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
      constructor
      · intro h; have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (Nat.lt_trans hv32 (by decide)),
          Nat.mod_eq_of_lt (Nat.lt_trans hax (by decide))] at this
        exact this.symm
      · intro h; rw [h]
    have hzf : ∀ {w : Nat} (x y : BitVec w), (Silmaril.X86.Ext.subFlagsN x y).zero =
        some (decide (x = y)) := by
      intro w x y
      simp only [Silmaril.X86.Ext.subFlagsN, Option.some.injEq]
      unfold Silmaril.X86.Ext.isZeroN
      rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq]
      constructor
      · intro h; have := congrArg (· + y) h; simpa using this
      · intro h; subst h; simp
    have hold : (BitVec.ofNat 32 (v % 2 ^ 32)).toNat = v % 2 ^ 32 := by simp
    refine ⟨_, _, .rmw (old := v % 2 ^ 32) (lt32 v), ?_, rfl, ?_, ?_⟩
    · split
      · rename_i h
        have hr : v % 4294967296 = (s.read .rax).toNat % 4294967296 := by
          rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, ofNat_toNat_lt hax, (hiff.mp h)]
        simp [Lab.acts, rmwAct, addrX_eval ha s (s.rip + BitVec.ofNat 64 n), valBytes4,
          RmwOp.result, Expr.eval, regsOf, leBytes4, Sz.read, hr]
      · rename_i h
        have hr : ¬ v % 4294967296 = (s.read .rax).toNat % 4294967296 := by
          rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, ofNat_toNat_lt hax]
          exact fun e => h (hiff.mpr e.symm)
        rw [hx]
        simp [Lab.acts, rmwAct, addrX_eval ha s (s.rip + BitVec.ofNat 64 n), valBytes4,
          RmwOp.result, Expr.eval, regsOf, leBytes4, hr]
    · split
      · rename_i h
        funext r
        simp only [regsOf, Regs.set]
        split
        · rename_i hr; subst hr
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ofNat]
          rw [← hiff.mp h, Nat.mod_eq_of_lt (Nat.lt_trans hax (by decide))]
          rfl
        · rfl
      · show regsOf (Sz.d.write s .rax _) = _
        refine (regsOf_dwrite s .rax _).trans ?_
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [ldVal_valBytes]
    · rw [hcz]
      split
      · rename_i h
        show (Silmaril.X86.Ext.subFlagsN _ _).zero = _
        rw [hzf, decide_eq_true h, decide_eq_true (hiff.mp h)]
      · rename_i h
        show (Silmaril.X86.Ext.subFlagsN _ _).zero = _
        rw [hzf, decide_eq_false h, decide_eq_false (fun e => h (hiff.mpr e))]
  · cases hs

/-- The actions of `lock sub` with old value `v` are those of the CIR label. -/
theorem subacts (v : Nat) (imm : BitVec 32) (rs : Regs) (A : Word) (md : Mode) :
    [(⟨⟨.rmw, A.toNat, 4, true⟩, .plain, valBytes v 4,
      leBytes ((Silmaril.X86.Ext.AluOp.resultN (n := 32) .sub (BitVec.ofNat 32 (v % 2 ^ 32))
        (imm.signExtend 32)).setWidth 64) 4⟩ : XAct)] =
      (some (Lab.rmw md A.toNat 4 (v % 2 ^ 32) (RmwOp.result rs 4 (v % 2 ^ 32)
        ((Expr.lit (subImm imm)).eval rs) (.op .sub)))).toList.flatMap Lab.acts := by
  simp only [Option.toList, List.flatMap_cons, List.flatMap_nil, List.append_nil, Lab.acts,
    rmwAct, valBytes4, leBytes4, List.cons.injEq, and_true]
  congr 2
  simp only [Silmaril.X86.Ext.AluOp.resultN, RmwOp.result, Expr.eval, BinOp.eval, subImm,
    BitVec.signExtend_eq, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := imm.isLt
  omega

/-- The zero flag of `lock sub` with old value `v` (32 bits) and immediate `imm`. -/
theorem subflag (v : Nat) (imm : BitVec 32) (rs : Regs) (d : Reg) :
    (Silmaril.X86.Ext.AluOp.flagsN (n := 32) .sub (BitVec.ofNat 32 (v % 2 ^ 32))
      (imm.signExtend 32)).zero =
      some (truthy ((subZ d imm).eval (rs.set d (BitVec.ofNat 64 (v % 2 ^ 32))))) := by
  simp only [Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.subFlagsN, Option.some.injEq]
  simp only [subZ, Expr.eval, BinOp.eval, truthy, Regs.set, ite_true, mask32, subImm,
    Silmaril.X86.Ext.isZeroN, BitVec.signExtend_eq]
  have key : (BitVec.ofNat 64 (v % 2 ^ 32) - BitVec.ofNat 64 imm.toNat &&& 4294967295#64 =
      0#64) ↔ (BitVec.ofNat 32 (v % 2 ^ 32) - imm = 0#32) := by
    have := imm.isLt
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      rw [mask_toNat] at h'
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
      omega
    · intro h
      have h' := congrArg BitVec.toNat h
      apply BitVec.eq_of_toNat_eq
      rw [mask_toNat]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
      omega
  by_cases hz : BitVec.ofNat 32 (v % 2 ^ 32) - imm = 0#32
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (key.mpr hz)), hz]; decide
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hz (key.mp h)))]
    simpa using hz

/-- `lock sub [m], imm` (32 bits): every register is kept on x86; CIR writes the old value to
the scratch register `d`. -/
theorem lockSub_sound {t : XThread} {dom : List Nat} {s : State} {m : XMem} {imm : BitVec 32}
    {n : Nat} {a : Expr} (ha : addrX m = some a)
    (hf : t.fetch s = some (.new (.lockAluI .d .sub m imm), n))
    {outs : List (List XAct × State)} (hs : stepSym t dom s = some outs)
    {acts : List XAct} {s' : State} (ho : (acts, s') ∈ outs) {d : Reg} {a' : Stmt}
    (hd : a'.demode = .rmw d .rlx 4 (.op .sub) a (.lit (subImm imm))) :
    ∃ (o : Option Lab) (rs' : Regs), TStep a' (regsOf s) o .skip rs' ∧
      acts = o.toList.flatMap Lab.acts ∧ s'.rip = s.rip + BitVec.ofNat 64 n ∧
      regsOf s' = regsOf s ∧ (∀ r, r ≠ d → rs' r = regsOf s r) ∧
      s'.flags.zero = some (truthy ((subZ d imm).eval rs')) := by
  rw [stepSym_mem' hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
    MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
    MemEvent.atomic9NewAccesses, Atomic9.tag, Atomic9.RM.isMem, MemEvent.aluKind,
    Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])] at hs
  simp only [memStep, rmwStep, reduceCtorEq, ite_false] at hs
  split at hs
  · cases hs
    simp only [List.mem_map] at ho
    obtain ⟨v, -, hv⟩ := ho
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    obtain ⟨md, rfl⟩ := demode_rmw' hd
    have hx : (ldVal (valBytes v Sz.d.bytes)).setWidth Sz.d.bits = BitVec.ofNat 32 (v % 2 ^ 32) :=
      ldv32 v
    refine ⟨_, _, .rmw (old := v % 2 ^ 32) (lt32 v), ?_, rfl, rfl, ?_, ?_⟩
    · simp only [hx]
      rw [← addrX_eval ha s (s.rip + BitVec.ofNat 64 n)]
      exact subacts v imm _ _ md
    · intro r hr; simp [Regs.set, hr]
    · simp only [hx]
      exact subflag v imm _ d
  · cases hs

/-- `mov d, src` (64 bits). -/
theorem mov64_sound {t : XThread} {dom : List Nat} {s : State} {d src : Reg} {n : Nat}
    (hf : t.fetch s = some (.open9 (.ext8 (.base (.mov .q (.reg d) src))), n))
    {outs : List (List XAct × State)} (hs : stepSym t dom s = some outs)
    {acts : List XAct} {s' : State} (ho : (acts, s') ∈ outs) :
    acts = [] ∧ s'.rip = s.rip + BitVec.ofNat 64 n ∧
      regsOf s' = (regsOf s).set d ((Expr.reg src).eval (regsOf s)) := by
  simp [stepSym, hf, MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
    MemEvent.extAccesses, MemEvent.rmEv, Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec,
    Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM] at hs
  subst hs
  simp only [List.mem_singleton, Prod.mk.injEq] at ho
  obtain ⟨rfl, rfl⟩ := ho
  refine ⟨rfl, rfl, ?_⟩
  refine (regsOf_write s d _).trans ?_
  simp [Expr.eval, Sz.read, regsOf]

/-- `ret` has no symbolic step. -/
theorem ret_none {t : XThread} {dom : List Nat} {s : State} {n : Nat}
    (hf : t.fetch s = some (.open9 (.ext8 (.base .ret)), n)) : stepSym t dom s = none := by
  rw [stepSym_mem' hf (by simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses,
    MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.popEv, Litmus.Event.inert,
    MemEvent.Kind.reads, MemEvent.Kind.writes])]
  rfl

end Silmaril.Proofs.X86.Concurrency.Cir.TvCfg

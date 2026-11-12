module

public import Silmaril.X86.Bir9.X.Defs
public import Silmaril.Proofs.X86.Bir9.Block
public import Silmaril.Proofs.X86.Bir9.Simp

/-! # Bir9X: soundness of the extended lifter

One lemma per new symbolic shape, in Bir9's `StepRel` form, then the block theorem:

* `execNew_alu_eq`, `execNew_aluI_eq`, `execNew_aluA_eq`, `execNew_test_eq`: on a low-byte
  register or memory operand, the `Ext8` ALU and TEST forms compute what Bir9's `XInstr.alu8`
  and `XInstr.test8` compute, so `Bir9.symStep_sound_x` applies;
* `sAluR8_sound`: `op r8, r/m8`;
* `sRMW8_sound`, `sShift8_sound`: byte read-modify-write, and the shifts by a constant;
* `sCarry_sound`: ADC/SBB (`Ext9.carryStep`), including the stop on an undefined CF;
* `symStepX_sound`, `symGoX_sound`, `symExecX_sound`, `liftBlockX_sound`.
-/

@[expose] public section

namespace Silmaril.Raw.X86.Bir9X

open Silmaril.X86 (Reg Word State Flags AluOp Byte)
open Silmaril.X86.Ext
open Silmaril.X86.Bir9
open Silmaril.X86.Bir9X
open Silmaril.Process (Memory)

variable {σ : SState} {env : Env} {s : State} {mem : Memory}

/-! ## Byte operands -/

theorem rm8_read {op : Silmaril.X86.Ext8.RM8} {o : RM} (h : rm8 op = some o) (s : State)
    (mem : Memory) (next : Word) : op.read s mem next = readNarrow .b o s mem next := by
  cases op with
  | reg b =>
    cases b with
    | low r => simp only [rm8, Option.some.injEq] at h; subst h; rfl
    | high r => simp [rm8] at h
  | mem m => simp only [rm8, Option.some.injEq] at h; subst h; rfl

theorem rm8_write {op : Silmaril.X86.Ext8.RM8} {o : RM} (h : rm8 op = some o) (v : BitVec 8)
    (s : State) (mem : Memory) (next : Word) :
    op.write v s mem next = writeNarrow .b o v s mem next := by
  cases op with
  | reg b =>
    cases b with
    | low r => simp only [rm8, Option.some.injEq] at h; subst h; rfl
    | high r => simp [rm8] at h
  | mem m => simp only [rm8, Option.some.injEq] at h; subst h; rfl

theorem alu8_eq {op : AluOp} {dst : Silmaril.X86.Ext8.RM8} {o : RM} (h : rm8 dst = some o)
    (y : BitVec 8) (s : State) (mem : Memory) (next : Word) :
    Silmaril.X86.Ext8.alu8 op dst y s mem next =
      match readNarrow .b o s mem next with
      | none => none
      | some x =>
        if op = .cmp then some ({ s with flags := AluOp.flagsN op x y }, mem)
        else (writeRM8 o (AluOp.resultN op x y) s mem next).map fun r =>
          ({ r.1 with flags := AluOp.flagsN op x y }, r.2) := by
  simp only [Silmaril.X86.Ext8.alu8, rm8_read h, writeRM8_eq]
  cases readNarrow .b o s mem next with
  | none => rfl
  | some x => simp only [rm8_write h]; rfl

/-! ## The ALU and TEST forms, through `XInstr` -/

theorem execNew_alu_eq {op : AluOp} {dst : Silmaril.X86.Ext8.RM8} {o : RM} (h : rm8 dst = some o)
    (r : Reg) (s : State) (mem : Memory) (len : Nat) :
    Silmaril.X86.Ext8.execNew (.alu op dst (.low r)) s mem (s.rip + BitVec.ofNat 64 len) =
      XInstr.exec (.alu8 op o (.reg r)) s mem len := by
  simp only [Silmaril.X86.Ext8.execNew, alu8_eq h, XInstr.exec]
  cases readNarrow .b o s mem (s.rip + BitVec.ofNat 64 len) with
  | none => rfl
  | some x => dsimp only; split <;> rfl

theorem execNew_aluI_eq {op : AluOp} {dst : Silmaril.X86.Ext8.RM8} {o : RM} (h : rm8 dst = some o)
    (imm : BitVec 8) (s : State) (mem : Memory) (len : Nat) :
    Silmaril.X86.Ext8.execNew (.aluI op dst imm) s mem (s.rip + BitVec.ofNat 64 len) =
      XInstr.exec (.alu8 op o (.imm imm)) s mem len := by
  simp only [Silmaril.X86.Ext8.execNew, alu8_eq h, XInstr.exec]
  cases readNarrow .b o s mem (s.rip + BitVec.ofNat 64 len) with
  | none => rfl
  | some x => dsimp only; split <;> rfl

theorem execNew_aluA_eq (op : AluOp) (imm : BitVec 8) (s : State) (mem : Memory) (len : Nat) :
    Silmaril.X86.Ext8.execNew (.aluA op imm) s mem (s.rip + BitVec.ofNat 64 len) =
      XInstr.exec (.alu8 op (.reg .rax) (.imm imm)) s mem len := by
  simp only [Silmaril.X86.Ext8.execNew, alu8_eq (dst := .reg (.low .rax)) rfl, XInstr.exec,
    readNarrow]
  split <;> rfl

theorem execNew_test_eq {dst : Silmaril.X86.Ext8.RM8} {o : RM} (h : rm8 dst = some o)
    (r : Reg) (s : State) (mem : Memory) (len : Nat) :
    Silmaril.X86.Ext8.execNew (.test dst (.low r)) s mem (s.rip + BitVec.ofNat 64 len) =
      XInstr.exec (.test8 o (.reg r)) s mem len := by
  simp only [Silmaril.X86.Ext8.execNew, rm8_read h, XInstr.exec]
  cases readNarrow .b o s mem (s.rip + BitVec.ofNat 64 len) <;> rfl

/-! ## `op r8, r/m8` -/

theorem sAluR8_sound (h : Rel σ env s mem) (len : Nat) (op : AluOp) (d : Reg) {src : RM}
    {src8 : Silmaril.X86.Ext8.RM8} (hsrc : rm8 src8 = some src) :
    StepRel (Silmaril.X86.Ext8.execNew (.aluR op (.low d) src8) s mem (s.rip + BitVec.ofNat 64 len))
      (runStmts (sAluR8 σ len op d src).1 env) (sAluR8 σ len op d src).2 := by
  have hx : Silmaril.X86.Ext8.execNew (.aluR op (.low d) src8) s mem (s.rip + BitVec.ofNat 64 len) =
      match rawRead src s mem (s.rip + BitVec.ofNat 64 len) 1 with
      | none => .dataFault
      | some x => retire (s.rip + BitVec.ofNat 64 len) (some (if op = .cmp then
          { s with flags := AluOp.flagsN op ((s.read d).setWidth 8) (x.setWidth 8) }
          else { s.write d ((s.read d &&& ~~~(0xFF#64)) |||
              (AluOp.resultN op ((s.read d).setWidth 8) (x.setWidth 8)).setWidth 64) with
            flags := AluOp.flagsN op ((s.read d).setWidth 8) (x.setWidth 8) }, mem)) := by
    simp only [Silmaril.X86.Ext8.execNew, rm8_read hsrc, readNarrow_eq,
      show Narrow.b.bytes = 1 from rfl]
    cases rawRead src s mem (s.rip + BitVec.ofNat 64 len) 1 with
    | none => rfl
    | some x =>
      simp only [Option.map_some, Silmaril.X86.Ext8.alu8, Silmaril.X86.Ext8.RM8.read,
        Silmaril.X86.Ext8.BReg.read, Silmaril.X86.Ext8.RM8.write, Silmaril.X86.Ext8.BReg.write,
        writeByte]
      split <;> rfl
  rw [hx]
  have hwd : ∀ n, σ.n ≤ n → (σ.regs d).wf n := fun n hn => h.regs_wf hn d
  by_cases hop : op = .cmp
  · have := sReadF_sound h len src 1 (fun y => .alu 8 op (σ.regs d) y)
      (fun x => AluOp.flagsN op ((s.read d).setWidth 8) (x.setWidth 8))
      (fun e n hn he => ⟨hwd n hn, he⟩)
      (fun env1 x e hx hxe => by subst hxe; simp only [F.den, h.regs_den hx])
    simp only [sAluR8, hop, ite_true] at this ⊢
    exact this
  · have := sReadSetF_sound h len src 1 d
      (fun y => .merge .b (σ.regs d) (.alu 8 op (σ.regs d) y)) (fun y => .alu 8 op (σ.regs d) y)
      (fun x => (s.read d &&& ~~~(0xFF#64)) |||
        (AluOp.resultN op ((s.read d).setWidth 8) (x.setWidth 8)).setWidth 64)
      (fun x => AluOp.flagsN op ((s.read d).setWidth 8) (x.setWidth 8))
      (fun e n hn he => ⟨hwd n hn, hwd n hn, he⟩)
      (fun e n hn he => ⟨hwd n hn, he⟩)
      (fun env1 x e hx hxe => by
        subst hxe
        simp only [E.den, h.regs_den hx, narrowMask, Narrow.bits,
          setWidth_64_setWidth (w := 8) (by decide)])
      (fun env1 x e hx hxe => by subst hxe; simp only [F.den, h.regs_den hx])
    simp only [sAluR8, hop, ite_false] at this ⊢
    exact this

/-! ## Byte read-modify-write and the shifts -/

theorem sRMW8_sound (h : Rel σ env s mem) (len : Nat) (dst : RM) (val : E → E) (fl : E → F)
    (V : BitVec 8 → BitVec 8) (FL : BitVec 8 → Flags)
    (hval : ∀ e n, σ.n ≤ n → e.wf n → (val e).wf n)
    (hfl : ∀ e n, σ.n ≤ n → e.wf n → (fl e).wf n)
    (hV : ∀ env1 e, env.Ext env1 → V ((e.den env1).setWidth 8) = ((val e).den env1).setWidth 8)
    (hFL : ∀ env1 e, env.Ext env1 → FL ((e.den env1).setWidth 8) = (fl e).den env1) :
    StepRel (match rawRead dst s mem (s.rip + BitVec.ofNat 64 len) 1 with
        | none => .dataFault
        | some x => retire (s.rip + BitVec.ofNat 64 len)
            ((writeNarrow .b dst (V (x.setWidth 8)) s mem (s.rip + BitVec.ofNat 64 len)).map fun r =>
              ({ r.1 with flags := FL (x.setWidth 8) }, r.2)))
      (runStmts (sRMW8 σ len dst val fl).1 env) (sRMW8 σ len dst val fl).2 := by
  have hnx := nxOf_den h len
  cases hr : rawRead dst s mem (s.rip + BitVec.ofNat 64 len) 1 with
  | none => simp only [sRMW8]; rw [runStmts_append, sRead_none h hnx hr]; rfl
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    simp only [sRMW8]
    apply StepRel.prepend hrun
    have hw := sWriteN_sound hok.rel (hok.nx h len) (hok.nxw h len) .b dst
      (e := val (sRead σ (nxOf σ len) 1 dst).2.1) (hval _ _ (hok.mono h) hok.wf)
    have hflw : (fl (sRead σ (nxOf σ len) 1 dst).2.1).wf env1.vals.length := by
      rw [hok.rel.len]; exact hfl _ _ (hok.mono h) hok.wf
    have := (hw.flags _ hflw).retire (hok.nx h len) (by rw [hok.rel.len]; exact hok.nxw h len)
    have e1 : V (xw.setWidth 8) = ((val (sRead σ (nxOf σ len) 1 dst).2.1).den env1).setWidth 8 := by
      rw [hx]; exact hV env1 _ hok.ext
    have e2 : FL (xw.setWidth 8) = (fl (sRead σ (nxOf σ len) 1 dst).2.1).den env1 := by
      rw [hx]; exact hFL env1 _ hok.ext
    rw [e1, e2]
    exact this

theorem countConst_raw {cnt : Count} {c : Nat} (h : countConst cnt = some c) (s : State) :
    (cnt.raw s).toNat % 32 = c := by
  cases cnt <;> simp only [countConst, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem shiftCount_den {c : Nat} (hc : c < 8) :
    ((BitVec.ofNat 64 c).setWidth 8).toNat % 8 = c := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sShift8_sound (h : Rel σ env s mem) (len : Nat) (op : ShiftOp) {dst : RM}
    {dst8 : Silmaril.X86.Ext8.RM8} (hdst : rm8 dst8 = some dst) {cnt : Count} {c : Nat}
    (hc : countConst cnt = some c) (h0 : 0 < c) (h8 : c < 8) :
    StepRel (Silmaril.X86.Ext8.execNew (.shift op dst8 cnt) s mem (s.rip + BitVec.ofNat 64 len))
      (runStmts (sShift8 σ len op dst c).1 env) (sShift8 σ len op dst c).2 := by
  have hx : Silmaril.X86.Ext8.execNew (.shift op dst8 cnt) s mem (s.rip + BitVec.ofNat 64 len) =
      match rawRead dst s mem (s.rip + BitVec.ofNat 64 len) 1 with
      | none => .dataFault
      | some x => retire (s.rip + BitVec.ofNat 64 len)
          ((writeNarrow .b dst (op.result (x.setWidth 8) c) s mem (s.rip + BitVec.ofNat 64 len)).map
            fun r => ({ r.1 with flags := op.flags (x.setWidth 8) c s.flags }, r.2)) := by
    simp only [Silmaril.X86.Ext8.execNew, countConst_raw hc, rm8_read hdst, readNarrow_eq,
      show Narrow.b.bytes = 1 from rfl, Nat.pos_iff_ne_zero.mp h0, ite_false]
    cases rawRead dst s mem (s.rip + BitVec.ofNat 64 len) 1 with
    | none => rfl
    | some x =>
      simp only [Option.map_some, rm8_write hdst, Silmaril.X86.Ext8.shift8Flags, h8, ite_true]
      rfl
  rw [hx]
  exact sRMW8_sound h len dst _ _ (fun x => op.result x c) (fun x => op.flags x c s.flags)
    (fun e n _ he => ⟨he, trivial⟩) (fun e n hn he => ⟨he, trivial, h.flags_wf hn⟩)
    (fun env1 e _ => by
      simp only [E.den, shiftCount_den h8, setWidth_64_setWidth (w := 8) (by decide)])
    (fun env1 e hx => by simp only [F.den, E.den, shiftCount_den h8, h.flags_den hx])

/-! ## ADC and SBB -/

theorem sCarry_sound (h : Rel σ env s mem) (len : Nat) (sz : Sz) (sub : Bool) (dst : RM) {y : E}
    (hy : y.wf σ.n) {yv : BitVec sz.bits} (hyv : yv = (y.den env).setWidth sz.bits) :
    StepRel (Silmaril.X86.Ext9.carryStep sz sub dst yv s mem (s.rip + BitVec.ofNat 64 len))
      (runStmts (sCarry σ len sz sub dst y).1 env) (sCarry σ len sz sub dst y).2 := by
  have hnx := nxOf_den h len
  simp only [Silmaril.X86.Ext9.carryStep, readRM_eq]
  cases hr : rawRead dst s mem (s.rip + BitVec.ofNat 64 len) sz.bytes with
  | none =>
    simp only [Option.map_none, sCarry]
    rw [List.append_assoc, runStmts_append, sRead_none h hnx hr]; rfl
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    simp only [Option.map_some, sCarry]
    rw [List.append_assoc]
    apply StepRel.prepend hrun
    have hcf : (sRead σ (nxOf σ len) sz.bytes dst).2.2.flags = σ.flags := hok.flags
    cases hc : s.flags.carry with
    | none =>
      have hb : Cond.eval s.flags .b = none := hc
      have := sCond_none hok.rel hb
      rw [hcf] at this
      rw [runStmts_append, this]; rfl
    | some cb =>
      have hb : Cond.eval s.flags .b = some cb := hc
      have hrun2 := sCond_some hok.rel hb
      rw [hcf] at hrun2
      apply StepRel.prepend hrun2
      -- the state after the condition
      have hp := hok.rel.push (if cb then 1#64 else 0#64)
      have hx2 := env1.ext_push (if cb then 1#64 else 0#64)
      set σ1 := (sRead σ (nxOf σ len) sz.bytes dst).2.2 with hσ1
      set ex := (sRead σ (nxOf σ len) sz.bytes dst).2.1 with hex
      set env2 := env1.push (if cb then 1#64 else 0#64) with henv2
      have hlen1 : env1.vals.length = σ1.n := hok.rel.len
      have hcv : (E.v σ1.n).den env2 = if cb then 1#64 else 0#64 := cond_den cb _ env1 hlen1
      have hexw : ex.wf σ1.fresh.n := E.wf_mono (Nat.le_succ _) hok.wf
      have hyw : y.wf σ1.fresh.n := E.wf_mono (Nat.le_succ _) (hok.wf_of h hy)
      have hcw : (E.v σ1.n).wf σ1.fresh.n := by simp [E.wf, SState.fresh]
      have hexd : ex.den env2 = xw := by
        rw [E.den_ext hx2 (by rw [hlen1]; exact hok.wf), ← hx]
      have hyd : y.den env2 = y.den env := by
        rw [E.den_ext (hok.ext.trans hx2) (by rw [h.len]; exact hy)]
      have hcv' : env2.vals.getD σ1.n 0 = if cb then 1#64 else 0#64 := hcv
      have hres : (Silmaril.X86.Ext9.carryResult sub (xw.setWidth sz.bits) yv cb) =
          ((E.xop (.carry sz sub) ex y (.v σ1.n)).den env2).setWidth sz.bits := by
        simp only [E.den, EOp.den, hexd, hyd, hcv', ← hyv]
        rw [setWidth_64_setWidth (Sz.bits_le sz)]
        cases cb <;> rfl
      have hfl : Silmaril.X86.Ext9.carryFlags sub (xw.setWidth sz.bits) yv cb =
          (F.xop (.carry sz sub) ex y (.v σ1.n)).den env2 := by
        simp only [F.den, FOp.den, E.den, hexd, hyd, hcv', ← hyv]
        cases cb <;> rfl
      have hw := sWriteRM_sound hp (nx := nxOf σ len) (next := s.rip + BitVec.ofNat 64 len)
        (by rw [E.den_ext hx2 (by rw [hlen1]; exact hok.nxw h len)]; exact hok.nx h len)
        (E.wf_mono (Nat.le_succ _) (hok.nxw h len)) sz dst
        (e := .xop (.carry sz sub) ex y (.v σ1.n)) ⟨hexw, hyw, hcw⟩
      have hflw : (F.xop (.carry sz sub) ex y (.v σ1.n)).wf env2.vals.length := by
        rw [hp.len]; exact ⟨hexw, hyw, hcw⟩
      have := (hw.flags _ hflw).retire (next := s.rip + BitVec.ofNat 64 len)
        (by rw [E.den_ext hx2 (by rw [hlen1]; exact hok.nxw h len)]; exact hok.nx h len)
        (by rw [hp.len]; exact E.wf_mono (Nat.le_succ _) (hok.nxw h len))
      dsimp only
      rw [hres, hfl]
      exact this

/-! ## One step -/

theorem symStep8_xmm (σ : SState) (i : Silmaril.X86.Ext8.New) (len : Nat) (p : List Stmt × SState)
    (hs : symStep8 σ i len = some p) : p.2.xmm = σ.xmm := by
  cases i with
  | alu op dst src =>
    cases src with
    | high r => simp [symStep8] at hs
    | low r =>
      simp only [symStep8] at hs; split at hs
      · exact symStep_xmm_x σ _ len p hs
      · cases hs
  | aluI op dst imm =>
    simp only [symStep8] at hs; split at hs
    · exact symStep_xmm_x σ _ len p hs
    · cases hs
  | aluA op imm => simp only [symStep8] at hs; exact symStep_xmm_x σ _ len p hs
  | test dst src =>
    cases src with
    | high r => simp [symStep8] at hs
    | low r =>
      simp only [symStep8] at hs; split at hs
      · exact symStep_xmm_x σ _ len p hs
      · cases hs
  | aluR op dst src =>
    cases dst with
    | high r => simp [symStep8] at hs
    | low d =>
      simp only [symStep8] at hs; split at hs
      · cases hs; unfold sAluR8; split <;> simp [sReadF, sReadSetF]
      · cases hs
  | shift op dst cnt =>
    simp only [symStep8] at hs; split at hs
    · split at hs
      · cases hs; simp [sShift8, sRMW8]
      · cases hs
    · cases hs
  | mov | movR | movx | setcc => simp [symStep8] at hs

theorem symStep8_sound {s : XState} (h : XRel σ env s mem) (i : Silmaril.X86.Ext8.New) (len : Nat)
    (p : List Stmt × SState) (hs : symStep8 σ i len = some p) :
    XStepRel ((XL.e8 i).exec s mem len) (runStmts p.1 env) p.2 := by
  refine lift_core_step h ?_ (symStep8_xmm σ i len p hs)
  cases i with
  | alu op dst src =>
    cases src with
    | high r => simp [symStep8] at hs
    | low r =>
      simp only [symStep8] at hs; split at hs
      · rename_i o ho; rw [execNew_alu_eq ho]; exact symStep_sound_x h.core _ len p hs
      · cases hs
  | aluI op dst imm =>
    simp only [symStep8] at hs; split at hs
    · rename_i o ho; rw [execNew_aluI_eq ho]; exact symStep_sound_x h.core _ len p hs
    · cases hs
  | aluA op imm =>
    simp only [symStep8] at hs; rw [execNew_aluA_eq]; exact symStep_sound_x h.core _ len p hs
  | test dst src =>
    cases src with
    | high r => simp [symStep8] at hs
    | low r =>
      simp only [symStep8] at hs; split at hs
      · rename_i o ho; rw [execNew_test_eq ho]; exact symStep_sound_x h.core _ len p hs
      · cases hs
  | aluR op dst src =>
    cases dst with
    | high r => simp [symStep8] at hs
    | low d =>
      simp only [symStep8] at hs; split at hs
      · rename_i o ho; cases hs; exact sAluR8_sound h.core len op d ho
      · cases hs
  | shift op dst cnt =>
    simp only [symStep8] at hs; split at hs
    · rename_i o c ho hc
      split at hs
      · rename_i hcc; cases hs; exact sShift8_sound h.core len op ho hc hcc.1 hcc.2
      · cases hs
    · cases hs
  | mov | movR | movx | setcc => simp [symStep8] at hs

theorem symStepX_sound {s : XState} (h : XRel σ env s mem) (i : XL) (len : Nat) (p : List Stmt × SState)
    (hs : symStepX σ i len = some p) : XStepRel (i.exec s mem len) (runStmts p.1 env) p.2 := by
  cases i with
  | e8 i => exact symStep8_sound h i len p hs
  | base i =>
    cases i with
    | n9 j =>
      cases j with
      | adc sz sub dst src =>
        simp only [symStepX, Option.some.injEq] at hs; subst hs
        refine lift_core_step h ?_ (by simp [sCarry])
        exact sCarry_sound h.core len sz sub dst (h.core.wf.1 src)
          (by simp only [Sz.read, h.core.regs])
      | adcI sz sub dst imm =>
        simp only [symStepX, Option.some.injEq] at hs; subst hs
        refine lift_core_step h ?_ (by simp [sCarry])
        exact sCarry_sound h.core len sz sub dst (y := immSz sz imm) trivial
          (by simp only [immSz, E.den, setWidth_64_setWidth (Sz.bits_le sz)])
      | _ => exact symStep_sound h _ len p (by simp only [symStepX] at hs; exact hs)
    | _ => exact symStep_sound h _ len p (by simp only [symStepX] at hs; exact hs)

/-! ## Blocks -/

theorem symGoX_sound : ∀ (instrs : List (XL × Nat)) (σ : SState) (env : Env) (s : XState)
    (mem : Memory) (p : List Stmt × SState), XRel σ env s mem → symGoX instrs σ = some p →
    XStepRel (execBlockX instrs s mem) (runStmts p.1 env) p.2
  | [], σ, env, s, mem, p, h, hs => by cases hs; exact h
  | (i, len) :: rest, σ, env, s, mem, p, h, hs => by
    simp only [symGoX] at hs
    split at hs
    · cases hs
    rename_i s1 σ1 h1
    split at hs
    · cases hs
    rename_i s2 σ2 h2
    cases hs
    have hstep := symStepX_sound h i len (s1, σ1) h1
    simp only [execBlockX]
    cases hr : i.exec s mem len with
    | ok s' m' =>
      rw [hr] at hstep
      simp only
      cases hrun : runStmts s1 env with
      | error f =>
        rw [hrun] at hstep
        exact absurd hstep (by cases f <;> simp [XStepRel, Fault.toX])
      | ok env1 =>
        rw [hrun] at hstep
        rw [runStmts_append, hrun]
        exact symGoX_sound rest σ1 env1 s' m' (s2, σ2) hstep h2
    | dataFault => rw [hr] at hstep; exact XStepRel.append_err (by simp) hstep
    | divideError => rw [hr] at hstep; exact XStepRel.append_err (by simp) hstep
    | undefinedCondition c => rw [hr] at hstep; exact XStepRel.append_err (by simp) hstep
    | trap => rw [hr] at hstep; exact XStepRel.append_err (by simp) hstep

theorem symExecX_sound {instrs : List (XL × Nat)} {b : Block} (hb : symExecX instrs = some b)
    (s : XState) (mem : Memory) : execBlockX instrs s mem = b.run s mem := by
  simp only [symExecX, Option.map_eq_some_iff] at hb
  obtain ⟨⟨sts, σ⟩, hgo, rfl⟩ := hb
  have h0 : XRel SState.init ⟨s.core, [], mem, s.xmm⟩ s mem :=
    { core := { mem := rfl, len := rfl, regs := fun _ => rfl, flags := rfl, rip := rfl, fs := rfl,
                wf := ⟨fun _ => trivial, trivial, trivial⟩ }
      xmm := fun i => by simp [SState.init, E.den, hi64_append_lo64]
      xwf := fun _ => ⟨trivial, trivial⟩ }
  have hrel := symGoX_sound instrs _ _ s mem _ h0 hgo
  simp only [Block.run, SState.toBlock]
  revert hrel
  cases hx : execBlockX instrs s mem <;> cases hrun : runStmts sts ⟨s.core, [], mem, s.xmm⟩ <;>
    intro hrel <;> simp only [XStepRel] at hrel
  case ok.ok s' m' env' =>
    obtain ⟨⟨hm, -, hregs, hflags, hrip, hfs, -⟩, hxmm, -⟩ := hrel
    subst hm
    congr 1
    obtain ⟨core, xmm⟩ := s'
    simp only [Block.state, XState.mk.injEq]
    constructor
    · cases core
      simp only [State.mk.injEq]
      refine ⟨funext fun r => ?_, hrip, hflags, hfs⟩
      have := SState.toBlock_reg sts σ r
      simp only [SState.toBlock] at this
      rw [this]
      exact hregs r
    · funext i
      have := SState.toBlock_xreg sts σ i
      simp only [SState.toBlock] at this
      rw [this]
      exact hxmm i
  case ok.error f => cases f <;> cases hrel
  all_goals exact hrel

/-- **The extended lifter's certificate.** -/
theorem liftBlockX_sound {instrs : List (XL × Nat)} {b : Block} (h : liftBlockX instrs = some b)
    (s : XState) (mem : Memory) : execBlockX instrs s mem = b.run s mem := by
  simp only [liftBlockX, Option.map_eq_some_iff] at h
  obtain ⟨b0, h0, rfl⟩ := h
  rw [Silmaril.Proofs.X86.Bir9.Block.simp_run, symExecX_sound h0]

end Silmaril.Raw.X86.Bir9X

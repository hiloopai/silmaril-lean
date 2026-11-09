module

public import Silmaril.Proofs.X86.Bir9.Sym

/-!
# Soundness of the operator shapes (division, wide products, bit scans, 16-bit ALU)

One lemma per new symbolic shape of
`Silmaril.X86.Bir9.Defs`, each relating the symbolic shape to the machine computation it
stands for, in the `StepRel` form that `symStep_sound_ext`/`symStep_sound_n9` (`Sound.lean`)
dispatch to:

* `sDiv_sound`: DIV/IDIV (`Ext.exec (.div …)`), including the `#DE` stop;
* `sMul1_sound`: MUL and one-operand IMUL (`RDX:RAX`);
* `sScan_sound`: BSF/BSR, including the zero-source stop `undefinedCondition .e`;
* `sAlu16_sound`: the 16-bit ALU forms (`Ext9.alu16`).
-/

@[expose] public section

namespace Silmaril.X86.Bir9

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord wordOfBytes?)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)

variable {σ : SState} {env : Env} {s : State} {mem : Memory}

theorem sDiv_sound (h : Rel σ env s mem) (len : Nat) (sz : Sz) (sg : Bool) (src : RM) :
    StepRel (match rawRead src s mem (s.rip + BitVec.ofNat 64 len) sz.bytes with
        | none => .dataFault
        | some y =>
          match divide sz sg ((s.read .rdx).setWidth sz.bits) ((s.read .rax).setWidth sz.bits)
              (y.setWidth sz.bits) with
          | none => .divideError
          | some (q, r) => retire (s.rip + BitVec.ofNat 64 len)
              (some ({ (s.write .rax (q.setWidth 64)).write .rdx (r.setWidth 64) with
                flags := undefinedFlags }, mem)))
      (runStmts (sDiv σ len sz sg src).1 env) (sDiv σ len sz sg src).2 := by
  have hnx := nxOf_den h len
  cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) sz.bytes with
  | none => simp only [sDiv]; rw [runStmts_append, sRead_none h hnx hr]; rfl
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    simp only [sDiv]
    apply StepRel.prepend hrun
    have hdx : (σ.regs .rdx).den env1 = s.read .rdx := h.regs_den hok.ext .rdx
    have hax : (σ.regs .rax).den env1 = s.read .rax := h.regs_den hok.ext .rax
    have hwd := hok.wf_of h (h.wf.1 .rdx)
    have hwa := hok.wf_of h (h.wf.1 .rax)
    cases hdv : divide sz sg ((s.read .rdx).setWidth sz.bits) ((s.read .rax).setWidth sz.bits)
        (xw.setWidth sz.bits) with
    | none =>
      apply StepRel.fault (f := .divide)
      simp only [runStmts, Stmt.run, COp.fault, hdx, hax, ← hx, hdv]
    | some qr =>
      obtain ⟨q, r⟩ := qr
      have hrun2 : runStmts [Stmt.chk (.div sz sg) (σ.regs .rdx) (σ.regs .rax)
          (sRead σ (nxOf σ len) sz.bytes src).2.1] env1 = .ok env1 := by
        simp only [runStmts, Stmt.run, COp.fault, hdx, hax, ← hx, hdv]
      rw [hrun2]
      have k1 := hok.rel.setReg' .rax
        (e := .xop (.divq sz sg) (σ.regs .rdx) (σ.regs .rax) (sRead σ (nxOf σ len) sz.bytes src).2.1)
        ⟨hwd, hwa, hok.wf⟩ (v := q.setWidth 64)
        (by simp only [E.den, EOp.den, hdx, hax, ← hx, hdv])
      have k2 := k1.setReg' .rdx
        (e := .xop (.divr sz sg) (σ.regs .rdx) (σ.regs .rax) (sRead σ (nxOf σ len) sz.bytes src).2.1)
        ⟨hwd, hwa, hok.wf⟩ (v := r.setWidth 64)
        (by simp only [E.den, EOp.den, hdx, hax, ← hx, hdv])
      have k3 := k2.setFlags' (f := .undef) trivial (fl := undefinedFlags) rfl
      exact (ORel.pure k3).retire (hok.nx h len) (by rw [hok.rel.len]; exact hok.nxw h len)

theorem sMul1_sound (h : Rel σ env s mem) (len : Nat) (signed : Bool) (sz : Sz) (src : RM)
    (LO HI : Word → Word) (FL : Word → Flags)
    (hLO : ∀ x, LO x = (if signed then EOp.imulLo sz else EOp.mulLo sz).den (s.read .rax) x 0)
    (hHI : ∀ x, HI x = (if signed then EOp.imulHi sz else EOp.mulHi sz).den (s.read .rax) x 0)
    (hFL : ∀ x, FL x = (if signed then FOp.imul1 sz else FOp.mul sz).den (s.read .rax) x 0) :
    StepRel (match rawRead src s mem (s.rip + BitVec.ofNat 64 len) sz.bytes with
        | none => .dataFault
        | some x => retire (s.rip + BitVec.ofNat 64 len)
            (some ({ (s.write .rax (LO x)).write .rdx (HI x) with flags := FL x }, mem)))
      (runStmts (sMul1 σ len signed sz src).1 env) (sMul1 σ len signed sz src).2 := by
  have hnx := nxOf_den h len
  cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) sz.bytes with
  | none => simp only [sMul1]; rw [runStmts_append, sRead_none h hnx hr]; rfl
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    simp only [sMul1]
    apply StepRel.prepend hrun
    have hax : (σ.regs .rax).den env1 = s.read .rax := h.regs_den hok.ext .rax
    have hwa := hok.wf_of h (h.wf.1 .rax)
    have k1 := hok.rel.setReg' .rax
      (e := .xop (if signed then .imulLo sz else .mulLo sz) (σ.regs .rax)
        (sRead σ (nxOf σ len) sz.bytes src).2.1 (.imm 0))
      ⟨hwa, hok.wf, trivial⟩ (v := LO xw) (by simp only [E.den, hax, ← hx, hLO])
    have k2 := k1.setReg' .rdx
      (e := .xop (if signed then .imulHi sz else .mulHi sz) (σ.regs .rax)
        (sRead σ (nxOf σ len) sz.bytes src).2.1 (.imm 0))
      ⟨hwa, hok.wf, trivial⟩ (v := HI xw) (by simp only [E.den, hax, ← hx, hHI])
    have k3 := k2.setFlags'
      (f := .xop (if signed then .imul1 sz else .mul sz) (σ.regs .rax)
        (sRead σ (nxOf σ len) sz.bytes src).2.1 (.imm 0))
      ⟨hwa, hok.wf, trivial⟩ (fl := FL xw) (by simp only [F.den, E.den, hax, ← hx, hFL])
    exact finish_pure h hok len k3

theorem sScan_sound (h : Rel σ env s mem) (len : Nat) (rev : Bool) (sz : Sz) (dst : Reg)
    (src : RM) :
    StepRel (match rawRead src s mem (s.rip + BitVec.ofNat 64 len) sz.bytes with
        | none => .dataFault
        | some x =>
          if x.setWidth sz.bits = 0#sz.bits then .undefinedCondition .e
          else retire (s.rip + BitVec.ofNat 64 len)
            (some ({ s.write dst ((if rev then EOp.bsr sz else EOp.bsf sz).den x 0 0) with
              flags := Silmaril.X86.Ext9.scanFlags }, mem)))
      (runStmts (sScan σ len rev sz dst src).1 env) (sScan σ len rev sz dst src).2 := by
  have hnx := nxOf_den h len
  cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) sz.bytes with
  | none => simp only [sScan]; rw [runStmts_append, sRead_none h hnx hr]; rfl
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    simp only [sScan]
    apply StepRel.prepend hrun
    by_cases hz : xw.setWidth sz.bits = 0#sz.bits
    · simp only [hz, ite_true]
      apply StepRel.fault (f := .undef .e)
      simp only [runStmts, Stmt.run, COp.fault, ← hx, hz, ite_true]
    · simp only [hz, ite_false]
      have hrun2 : runStmts [Stmt.chk (.nz sz) (sRead σ (nxOf σ len) sz.bytes src).2.1
          (.imm 0) (.imm 0)] env1 = .ok env1 := by
        simp only [runStmts, Stmt.run, COp.fault, ← hx, hz, ite_false]
      rw [hrun2]
      have k1 := hok.rel.setReg' dst
        (e := .xop (if rev then .bsr sz else .bsf sz) (sRead σ (nxOf σ len) sz.bytes src).2.1
          (.imm 0) (.imm 0))
        ⟨hok.wf, trivial, trivial⟩ (v := (if rev then EOp.bsr sz else EOp.bsf sz).den xw 0 0)
        (by simp only [E.den, ← hx])
      have k2 := k1.setFlags' (f := .xop .scan (.imm 0) (.imm 0) (.imm 0)) ⟨trivial, trivial, trivial⟩
        (fl := Silmaril.X86.Ext9.scanFlags) rfl
      exact (ORel.pure k2).retire (hok.nx h len) (by rw [hok.rel.len]; exact hok.nxw h len)

theorem sAlu16_sound (h : Rel σ env s mem) (len : Nat) (op : AluOp) (dst : RM) {y : E}
    (hy : y.wf σ.n) {Y : BitVec 16} (hY : (y.den env).setWidth 16 = Y) :
    StepRel (retire (s.rip + BitVec.ofNat 64 len)
        (Silmaril.X86.Ext9.alu16 op dst Y s mem (s.rip + BitVec.ofNat 64 len)))
      (runStmts (sAlu16 σ len op dst y).1 env) (sAlu16 σ len op dst y).2 := by
  have hnx := nxOf_den h len
  simp only [Silmaril.X86.Ext9.alu16, readNarrow_eq, show Narrow.w.bytes = 2 from rfl]
  cases hr : rawRead dst s mem (s.rip + BitVec.ofNat 64 len) 2 with
  | none =>
    by_cases hop : op = .cmp <;> simp only [sAlu16, hop, ite_true, ite_false] <;>
      (simp only [Option.map_none]; rw [runStmts_append, sRead_none h hnx hr]; rfl)
  | some xw =>
    obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
    have hyd : (y.den env1).setWidth 16 = Y := by rw [hok.den_eq h hy]; exact hY
    have hyw : y.wf (sRead σ (nxOf σ len) 2 dst).2.2.n := hok.wf_of h hy
    have hfl : AluOp.flagsN op (xw.setWidth Narrow.w.bits) Y =
        (F.alu 16 op (sRead σ (nxOf σ len) 2 dst).2.1 y).den env1 := by
      simp only [F.den, ← hx, hyd]; rfl
    have hflw : (F.alu 16 op (sRead σ (nxOf σ len) 2 dst).2.1 y).wf env1.vals.length := by
      rw [hok.rel.len]; exact ⟨hok.wf, hyw⟩
    by_cases hop : op = .cmp
    · simp only [sAlu16, hop, ite_true, Option.map_some]
      apply StepRel.prepend hrun
      exact finish_pure h hok len
        (hok.rel.setFlags' (by rw [← hok.rel.len]; exact hflw) (hop ▸ hfl))
    · simp only [sAlu16, hop, ite_false, Option.map_some]
      apply StepRel.prepend hrun
      have hv : AluOp.resultN op (xw.setWidth Narrow.w.bits) Y =
          ((E.alu 16 op (sRead σ (nxOf σ len) 2 dst).2.1 y).den env1).setWidth Narrow.w.bits := by
        simp only [E.den, ← hx, hyd]; exact (setWidth_64_setWidth (w := 16) (by decide) _).symm
      have hw := sWriteN_sound hok.rel (hok.nx h len) (hok.nxw h len) .w dst
        (e := .alu 16 op (sRead σ (nxOf σ len) 2 dst).2.1 y) ⟨hok.wf, hyw⟩
      have := (hw.flags _ hflw).retire (hok.nx h len) (by rw [hok.rel.len]; exact hok.nxw h len)
      rw [← hv, ← hfl] at this
      exact this

end Silmaril.X86.Bir9

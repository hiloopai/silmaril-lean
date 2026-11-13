-- Imported from an earlier development
-- Source: Silmaril/X86/Lift/BirSound.lean; sha256=347a282597747690f46220d8fde2b456fbcdc797658f58b8486d9c9bca6d350c
-- Reproduce with tools/mor/examples/import_x86_lift.rs; declaration namespaces retained.
module

public import Silmaril.Raw.Machine.X86.Lift.BirSym

/-!
# Soundness of `symStep`, and the block theorem

`symStep_sound`: one symbolic step is related to one machine step, for every
instruction `symStep` accepts. `symExec_sound`: a whole straight-line block.
-/

@[expose] public section

namespace Silmaril.X86.Lift.Bir

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord wordOfBytes?)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

variable {σ : SState} {env : Env} {s : State} {mem : Memory}

set_option maxHeartbeats 1000000 in
theorem symStep_sound_ext (h : Rel σ env s mem) (i : Ext.Instr) (len : Nat) (p : List Stmt × SState)
    (hs : symStep σ (.ext i) len = some p) :
    StepRel (Ext.exec i s mem len) (runStmts p.1 env) p.2 := by
  have hnx := nxOf_den h len
  cases i with
  | mov sz dst src =>
    cases hs
    exact sMov_sound h len sz dst (h.wf.1 src) (by simp only [Sz.read, h.regs])
  | movI sz dst imm =>
    cases hs
    exact sMov_sound h len sz dst (e := .imm ((imm.signExtend sz.bits).setWidth 64)) trivial
      (setWidth_64_setWidth (Sz.bits_le sz) _).symm
  | movI16 dst imm =>
    cases hs
    have hv : imm = ((E.imm (imm.setWidth 64)).den env).setWidth Narrow.w.bits :=
      (setWidth_64_setWidth (w := 16) (by decide) _).symm
    cases dst with
    | reg r => exact sMovN_sound h len .w (.reg r) (e := .imm (imm.setWidth 64)) trivial hv
    | mem m => exact sMovN_sound h len .w (.mem m) (e := .imm (imm.setWidth 64)) trivial hv
  | movI32 dst imm => cases hs; exact sSet_sound h len dst (e := .imm (imm.setWidth 64)) trivial rfl
  | movabs dst imm => cases hs; exact sSet_sound h len dst (e := .imm imm) trivial rfl
  | load sz dst src =>
    cases hs
    have := sReadSet_sound h len (.mem src) sz.bytes dst (.zext sz.bits)
      (fun x => (x.setWidth sz.bits).setWidth 64) (fun _ _ he _ => he)
      (by intro env1 x e _ hx; subst hx; rfl)
    simp only [Ext.exec, readRM_eq]
    cases hr : rawRead (.mem src) s mem (s.rip + BitVec.ofNat 64 len) sz.bytes <;>
      simp only [hr, Option.map_none, Option.map_some] at this ⊢ <;> exact this
  | store n dst src =>
    cases hs
    exact sMovN_sound h len n dst (h.wf.1 src) (by rw [h.regs])
  | movx sx sz n dst src =>
    cases hs
    have := sReadSet_sound h len src n.bytes dst
      (fun e => if sx then .zext sz.bits (.sext n.bits e) else .zext sz.bits (.zext n.bits e))
      (fun x => (if sx then (x.setWidth n.bits).signExtend sz.bits
        else (x.setWidth n.bits).setWidth sz.bits).setWidth 64)
      (by intro e k he _; cases sx <;> simpa [E.wf] using he)
      (by
        intro env1 x e _ hx; subst hx
        cases sx
        · simp [E.den, BitVec.setWidth_setWidth_of_le _ (Sz.bits_le sz)]
        · simp [E.den, setWidth_signExtend_of_le _ (Sz.bits_le sz)])
    simp only [Ext.exec, readNarrow_eq]
    cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) n.bytes <;>
      simp only [hr, Option.map_none, Option.map_some] at this ⊢ <;> exact this
  | movsxd dst src =>
    cases hs
    have := sReadSet_sound h len src 4 dst (.sext 32) (fun x => (x.setWidth 32).signExtend 64)
      (fun _ _ he _ => he) (by intro env1 x e _ hx; subst hx; rfl)
    simp only [Ext.exec, readRM_eq, show Sz.d.bytes = 4 from rfl]
    cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) 4 <;>
      simp only [hr, Option.map_none, Option.map_some] at this ⊢ <;> exact this
  | lea sz dst m =>
    cases hs
    refine sSet_sound h len dst (e := .zext sz.bits (sAddr σ (nxOf σ len) m))
      (sAddr_wf h.wf (nxOf_wfn h len) m) ?_
    simp only [E.den, sAddr_den h hnx m]
  | alu sz op dst src =>
    cases hs
    exact sAlu_sound h len sz op dst (h.wf.1 src) (by simp only [Sz.read, h.regs])
  | aluI sz op dst imm =>
    cases hs
    exact sAlu_sound h len sz op dst (y := .imm ((imm.signExtend sz.bits).setWidth 64)) trivial
      (setWidth_64_setWidth (Sz.bits_le sz) _).symm
  | aluI8 sz op dst imm =>
    cases hs
    exact sAlu_sound h len sz op dst (y := .imm ((imm.signExtend sz.bits).setWidth 64)) trivial
      (setWidth_64_setWidth (Sz.bits_le sz) _).symm
  | aluA sz op imm =>
    cases hs
    exact sAlu_sound h len sz op (.reg .rax) (y := .imm ((imm.signExtend sz.bits).setWidth 64)) trivial
      (setWidth_64_setWidth (Sz.bits_le sz) _).symm
  | aluR sz op dst src =>
    by_cases hop : op = .cmp
    · subst hop
      simp only [symStep, ite_true] at hs
      cases hs
      have := sReadF_sound h len src sz.bytes (fun y => .alu sz.bits .cmp (σ.regs dst) y)
        (fun y => AluOp.flagsN .cmp (Sz.read sz s dst) (y.setWidth sz.bits))
        (by intro e k hk he; exact ⟨h.regs_wf hk dst, he⟩)
        (by intro env1 x e hx hxe; subst hxe; simp only [F.den, Sz.read, h.regs_den hx])
      simp only [Ext.exec, aluStepR, readRM_eq]
      cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) sz.bytes <;>
        simp only [hr, Option.map_none, Option.map_some, ite_true] at this ⊢ <;> exact this
    · simp only [symStep, hop, ite_false] at hs
      cases hs
      have := sReadSetF_sound h len src sz.bytes dst (fun y => .alu sz.bits op (σ.regs dst) y)
        (fun y => .alu sz.bits op (σ.regs dst) y)
        (fun y => (AluOp.resultN op (Sz.read sz s dst) (y.setWidth sz.bits)).setWidth 64)
        (fun y => AluOp.flagsN op (Sz.read sz s dst) (y.setWidth sz.bits))
        (by intro e k hk he; exact ⟨h.regs_wf hk dst, he⟩)
        (by intro e k hk he; exact ⟨h.regs_wf hk dst, he⟩)
        (by intro env1 x e hx hxe; subst hxe; simp only [E.den, Sz.read, h.regs_den hx])
        (by intro env1 x e hx hxe; subst hxe; simp only [F.den, Sz.read, h.regs_den hx])
      simp only [Ext.exec, aluStepR, readRM_eq]
      cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) sz.bytes <;>
        simp only [hr, Option.map_none, Option.map_some, hop, ite_false] at this ⊢ <;> exact this
  | test sz dst src =>
    cases hs
    have := sReadF_sound h len dst sz.bytes (fun x => .test sz.bits x (σ.regs src))
      (fun x => logicFlagsN (x.setWidth sz.bits &&& Sz.read sz s src))
      (by intro e k hk he; exact ⟨he, h.regs_wf hk src⟩)
      (by intro env1 x e hx hxe; subst hxe; simp only [F.den, Sz.read, h.regs_den hx])
    simp only [Ext.exec, readRM_eq]
    cases hr : rawRead dst s mem (s.rip + BitVec.ofNat 64 len) sz.bytes <;>
      simp only [hr, Option.map_none, Option.map_some] at this ⊢ <;> exact this
  | testA sz imm =>
    cases hs
    refine sFlags_sound h len
      (f := .test sz.bits (σ.regs .rax) (.imm ((imm.signExtend sz.bits).setWidth 64)))
      ⟨h.wf.1 .rax, trivial⟩ ?_
    simp only [F.den, E.den, Sz.read, h.regs, setWidth_64_setWidth (Sz.bits_le sz)]
  | incdec sz dec dst =>
    cases hs
    exact sRMWF_sound h len sz dst _ _
      (fun x => if dec then x - 1#sz.bits else x + 1#sz.bits)
      (fun x => if dec then decFlagsN x s.flags else incFlagsN x s.flags)
      (by intro e k _ he; exact ⟨he, trivial⟩)
      (by intro e k hk he; cases dec <;> exact ⟨he, h.flags_wf hk⟩)
      (by
        intro env1 e _
        cases dec <;>
          simp [E.den, AluOp.resultN, setWidth_64_setWidth (Sz.bits_le sz), one_setWidth])
      (by intro env1 e hx; cases dec <;> simp [F.den, h.flags_den hx])
  | bswap sz dst =>
    cases hs
    refine sSet_sound h len dst (e := .bswap sz (σ.regs dst)) (h.wf.1 dst) ?_
    simp only [E.den, Sz.read, h.regs]
  | unary sz op dst =>
    cases op with
    | neg =>
      cases hs
      exact sRMWF_sound h len sz dst _ _ (fun x => 0#sz.bits - x) (fun x => negFlagsN x)
        (fun _ _ _ he => he) (fun _ _ _ he => he)
        (by intro env1 e _; simp [E.den, setWidth_64_setWidth (Sz.bits_le sz)])
        (by intro env1 e _; rfl)
    | not =>
      cases hs
      exact sRMW_sound h len sz dst _ (fun x => ~~~x) (fun _ _ _ he => he)
        (by intro env1 e _; simp [E.den, setWidth_64_setWidth (Sz.bits_le sz)])
  | imul sz dst src =>
    cases hs
    have := sReadSetF_sound h len src sz.bytes dst (.mul sz.bits (σ.regs dst))
      (.imul sz.bits (σ.regs dst))
      (fun y => (Sz.read sz s dst * y.setWidth sz.bits).setWidth 64)
      (fun y => imulFlags (Sz.read sz s dst) (y.setWidth sz.bits))
      (by intro e k hk he; exact ⟨h.regs_wf hk dst, he⟩)
      (by intro e k hk he; exact ⟨h.regs_wf hk dst, he⟩)
      (by intro env1 x e hx hxe; subst hxe; simp only [E.den, Sz.read, h.regs_den hx])
      (by intro env1 x e hx hxe; subst hxe; simp only [F.den, Sz.read, h.regs_den hx])
    simp only [Ext.exec, readRM_eq]
    cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) sz.bytes <;>
      simp only [hr, Option.map_none, Option.map_some] at this ⊢ <;> exact this
  | shift sz op dst count =>
    cases hs
    exact sRMWF_sound h len sz dst _ _
      (fun x => op.result x ((count.raw s).toNat % sz.bits))
      (fun x => op.flags x ((count.raw s).toNat % sz.bits) s.flags)
      (by intro e k hk he; exact ⟨he, countSym_wf h hk count⟩)
      (by intro e k hk he; exact ⟨he, countSym_wf h hk count, h.flags_wf hk⟩)
      (by
        intro env1 e hx
        simp only [E.den, countSym_den h hx, setWidth_64_setWidth (Sz.bits_le sz)])
      (by intro env1 e hx; simp only [F.den, countSym_den h hx, h.flags_den hx])
  | cxd sz =>
    cases hs
    refine sSet_sound h len .rdx (e := .signmask sz.bits (σ.regs .rax)) (h.wf.1 .rax) ?_
    simp only [E.den, Sz.read, h.regs]
  | cxe sz =>
    cases sz with
    | d =>
      cases hs
      refine sSet_sound h len .rax (e := .zext 32 (.sext 16 (σ.regs .rax))) (h.wf.1 .rax) ?_
      simp only [E.den, h.regs, setWidth_signExtend_of_le _ (by decide : 32 ≤ 64)]
      rfl
    | q =>
      cases hs
      refine sSet_sound h len .rax (e := .sext 32 (σ.regs .rax)) (h.wf.1 .rax) ?_
      simp only [E.den, Sz.read, h.regs]
      rfl
  | div sz signed src => cases hs
  | test8 => cases hs
  | testI8 => cases hs
  | testA8 => cases hs
  | cmpI8 => cases hs
  | cmpA8 => cases hs
  | mul => cases hs
  | cmov => cases hs
  | setcc c dst =>
    cases hs
    simp only [Ext.exec, writeRM8_eq]
    cases hc : c.eval s.flags with
    | none => exact StepRel.fault (f := .undef c) (by rw [runStmts_append, sCond_none h hc])
    | some b =>
      have hp := h.push (if b then 1#64 else 0#64)
      have hnx' : (nxOf σ len).den (env.push (if b then 1#64 else 0#64)) =
          s.rip + BitVec.ofNat 64 len := by
        rw [E.den_ext (env.ext_push _) (nxOf_wf h len)]; exact hnx
      have hw := sWriteN_sound hp hnx' (E.wf_mono (Nat.le_succ _) (nxOf_wfn h len)) .b dst
        (e := .v σ.n) (by simp [E.wf, SState.fresh])
      have hv : (if b then 1#8 else 0#8) =
          ((E.v σ.n).den (env.push (if b then 1#64 else 0#64))).setWidth Narrow.b.bits := by
        rw [cond_den b σ.n env h.len]; cases b <;> rfl
      dsimp only
      rw [hv]
      exact StepRel.prepend (sCond_some h hc)
        (hw.retire hnx' (E.wf_mono (by simp [Env.push]) (nxOf_wf h len)))
  | jmp rel =>
    cases hs
    exact h.setRip' (addImm_wf (nxOf_wfn h len) _) (by rw [addImm_den, hnx])
  | jmp8 rel =>
    cases hs
    exact h.setRip' (addImm_wf (nxOf_wfn h len) _) (by rw [addImm_den, hnx])
  | jcc c rel =>
    cases hs
    simp only [Ext.exec]
    cases hc : c.eval s.flags with
    | none => exact StepRel.fault (sCond_none h hc)
    | some b =>
      rw [sCond_some h hc]
      have hp := h.push (if b then 1#64 else 0#64)
      have hx := env.ext_push (if b then 1#64 else 0#64)
      have key := hp.setRip' (e := .sel (.v σ.n) (addImm (nxOf σ len) (rel.signExtend 64)) (nxOf σ len))
        ⟨by simp [SState.fresh, E.wf], E.wf_mono (Nat.le_succ _) (addImm_wf (nxOf_wfn h len) _),
          E.wf_mono (Nat.le_succ _) (nxOf_wfn h len)⟩
        (v := if b then s.rip + BitVec.ofNat 64 len + rel.signExtend 64 else s.rip + BitVec.ofNat 64 len)
        (by
          simp only [E.den, addImm_den, E.den_ext hx (nxOf_wf h len), hnx]
          cases b <;> simp [Env.push, h.len])
      cases b <;> exact key
  | jcc8 c rel =>
    cases hs
    simp only [Ext.exec]
    cases hc : c.eval s.flags with
    | none => exact StepRel.fault (sCond_none h hc)
    | some b =>
      rw [sCond_some h hc]
      have hp := h.push (if b then 1#64 else 0#64)
      have hx := env.ext_push (if b then 1#64 else 0#64)
      have key := hp.setRip' (e := .sel (.v σ.n) (addImm (nxOf σ len) (rel.signExtend 64)) (nxOf σ len))
        ⟨by simp [SState.fresh, E.wf], E.wf_mono (Nat.le_succ _) (addImm_wf (nxOf_wfn h len) _),
          E.wf_mono (Nat.le_succ _) (nxOf_wfn h len)⟩
        (v := if b then s.rip + BitVec.ofNat 64 len + rel.signExtend 64 else s.rip + BitVec.ofNat 64 len)
        (by
          simp only [E.den, addImm_den, E.den_ext hx (nxOf_wf h len), hnx]
          cases b <;> simp [Env.push, h.len])
      cases b <;> exact key
  | call rel =>
    cases hs
    have hP := sPush_sound h (val := nxOf σ len) hnx.symm
    simp only [Ext.exec]
    cases hp : pushWord s mem (s.rip + BitVec.ofNat 64 len) with
    | none => rw [hp] at hP; exact StepRel.fault hP
    | some p =>
      obtain ⟨t, m⟩ := p
      rw [hp] at hP
      obtain ⟨env', hrun, hrel⟩ := hP
      rw [hrun]
      exact hrel.setRip' (addImm_wf (nxOf_wfn h len) _)
        (by rw [addImm_den, E.den_ext (runStmts_ext hrun) (nxOf_wf h len), hnx])
  | ret =>
    cases hs
    simp only [Ext.exec]
    cases hp : popWord s mem with
    | none => exact StepRel.fault (sPop_none h hp)
    | some p =>
      obtain ⟨v, t⟩ := p
      obtain ⟨hrun, hrel, hv⟩ := sPop_some h hp
      rw [hrun]
      exact hrel.setRip' (by simp [E.wf, sPopState, SState.setReg, SState.fresh]) hv
  | push src =>
    cases hs
    exact (sPush_sound h (h.regs src)).retire hnx (nxOf_wf h len)
  | pushRM src =>
    cases hs
    simp only [Ext.exec, readRM_eq, show Sz.q.bytes = 8 from rfl]
    cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) 8 with
    | none => rw [runStmts_append, sRead_none h hnx hr]; rfl
    | some xw =>
      obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
      apply StepRel.prepend hrun
      exact (sPush_sound hok.rel (val := (sRead σ (nxOf σ len) 8 src).2.1)
        (by rw [← hx]; exact BitVec.setWidth_eq _)).retire (hok.nx h len)
        (by rw [hok.rel.len]; exact hok.nxw h len)
  | pop dst =>
    cases hs
    simp only [Ext.exec]
    cases hp : popWord s mem with
    | none => exact StepRel.fault (sPop_none h hp)
    | some p =>
      obtain ⟨v, t⟩ := p
      obtain ⟨hrun, hrel, hv⟩ := sPop_some h hp
      rw [hrun]
      exact (ORel.pure (hrel.setReg' dst (by simp [E.wf, sPopState, SState.setReg, SState.fresh]) hv)).retire
        (by rw [E.den_ext (env.ext_push v) (nxOf_wf h len)]; exact hnx)
        (E.wf_mono (by simp [Env.push]) (nxOf_wf h len))
  | leave =>
    cases hs
    simp only [Ext.exec]
    have ht := h.setReg' .rsp (e := σ.regs .rbp) (h.wf.1 .rbp) (h.regs .rbp)
    cases hp : popWord (s.write .rsp (s.read .rbp)) mem with
    | none => exact StepRel.fault (sPop_none ht hp)
    | some p =>
      obtain ⟨v, t⟩ := p
      obtain ⟨hrun, hrel, hv⟩ := sPop_some ht hp
      have hrun' : runStmts [.pop (σ.regs .rbp)] env = .ok (env.push v) := hrun
      rw [hrun']
      exact (ORel.pure (hrel.setReg' .rbp
          (by simp [E.wf, sPopState, SState.setReg, SState.fresh]) hv)).retire
        (by rw [E.den_ext (env.ext_push v) (nxOf_wf h len)]; exact hnx)
        (E.wf_mono (by simp [Env.push]) (nxOf_wf h len))
  | ud2 => cases hs; exact StepRel.fault (f := .trap) rfl
  | nop n => cases hs; exact pure_sound h len h
  | endbr64 => cases hs; exact pure_sound h len h
  | mov8 dst src =>
    cases hs
    have := sReadSet_sound h len src 1 dst (.merge .b (σ.regs dst))
      (fun x => (s.read dst &&& ~~~(0xFF#64)) ||| (x.setWidth 8).setWidth 64)
      (fun e n he hr => ⟨hr dst, he⟩)
      (by intro env1 x e hx hxe; subst hxe; simp [E.den, narrowMask, h.regs_den hx]; rfl)
    simp only [Ext.exec, readNarrow_eq, show Narrow.b.bytes = 1 from rfl]
    cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) 1 <;>
      simp only [hr, Option.map_none, Option.map_some] at this ⊢ <;> exact this
  | movI8 dst imm =>
    cases hs
    simp only [Ext.exec, writeRM8_eq]
    exact sMovN_sound h len .b dst (e := .imm (imm.setWidth 64)) trivial
      (setWidth_64_setWidth (w := 8) (by decide) _).symm
  | bitcount op sz dst src =>
    cases hs
    have := sReadSetF_sound h len src sz.bytes dst (.bitcount op sz.bits) (.bitcount op sz.bits)
      (fun x => (BitVec.ofNat sz.bits (op.count (x.setWidth sz.bits))).setWidth 64)
      (fun x => op.flags (x.setWidth sz.bits))
      (fun _ _ _ he => he) (fun _ _ _ he => he)
      (by intro env1 x e _ hxe; subst hxe; rfl)
      (by intro env1 x e _ hxe; subst hxe; rfl)
    simp only [Ext.exec, readRM_eq]
    cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) sz.bytes <;>
      simp only [hr, Option.map_none, Option.map_some] at this ⊢ <;> exact this

set_option maxHeartbeats 1000000 in
set_option linter.unusedTactic false in
theorem symStep_sound_x (h : Rel σ env s mem) (i : XInstr) (len : Nat) (p : List Stmt × SState)
    (hs : symStep σ (.x i) len = some p) :
    StepRel (XInstr.exec i s mem len) (runStmts p.1 env) p.2 := by
  have hnx := nxOf_den h len
  cases i with
  | alu8 op dst src =>
    simp only [symStep] at hs
    simp only [XInstr.exec, readNarrow_eq, show Narrow.b.bytes = 1 from rfl]
    cases hr : rawRead dst s mem (s.rip + BitVec.ofNat 64 len) 1 with
    | none =>
      by_cases hop : op = .cmp <;> simp only [hop, ite_true, ite_false] at hs <;> cases hs <;>
        (simp only [Option.map_none]; rw [runStmts_append, sRead_none h hnx hr]; rfl)
    | some xw =>
      obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
      have hyd : ((Src8.sym σ src).den env1).setWidth 8 = src.read s := Src8.sym_den h hok.ext src
      have hfl : AluOp.flagsN op (xw.setWidth Narrow.b.bits) (src.read s) =
          (F.alu 8 op (sRead σ (nxOf σ len) 1 dst).2.1 (Src8.sym σ src)).den env1 := by
        simp only [F.den, ← hx, hyd]; try rfl
      have hyw : (Src8.sym σ src).wf (sRead σ (nxOf σ len) 1 dst).2.2.n :=
        Src8.sym_wf h (hok.mono h) src
      have hflw : (F.alu 8 op (sRead σ (nxOf σ len) 1 dst).2.1 (Src8.sym σ src)).wf
          env1.vals.length := by
        rw [hok.rel.len]; exact ⟨hok.wf, hyw⟩
      by_cases hop : op = .cmp
      · simp only [hop, ite_true] at hs
        cases hs
        simp only [Option.map_some, hop, ite_true]
        apply StepRel.prepend hrun
        exact finish_pure h hok len (hok.rel.setFlags' (by rw [← hok.rel.len]; exact hflw) (hop ▸ hfl))
      · simp only [hop, ite_false] at hs
        cases hs
        simp only [Option.map_some, hop, ite_false, writeRM8_eq]
        apply StepRel.prepend hrun
        have hv : AluOp.resultN op (xw.setWidth Narrow.b.bits) (src.read s) =
            ((E.alu 8 op (sRead σ (nxOf σ len) 1 dst).2.1 (Src8.sym σ src)).den env1).setWidth
              Narrow.b.bits := by
          simp only [E.den, ← hx, hyd]; exact (setWidth_64_setWidth (w := 8) (by decide) _).symm
        have hw := sWriteN_sound hok.rel (hok.nx h len) (hok.nxw h len) .b dst
          (e := .alu 8 op (sRead σ (nxOf σ len) 1 dst).2.1 (Src8.sym σ src)) ⟨hok.wf, hyw⟩
        have := (hw.flags _ hflw).retire (hok.nx h len) (by rw [hok.rel.len]; exact hok.nxw h len)
        rw [← hv, ← hfl] at this
        exact this
  | test8 dst src =>
    cases hs
    have := sReadF_sound h len dst 1 (fun x => .test 8 x (Src8.sym σ src))
      (fun x => logicFlagsN (x.setWidth 8 &&& src.read s))
      (by intro e k hk he; exact ⟨he, Src8.sym_wf h hk src⟩)
      (by intro env1 x e hx hxe; subst hxe; simp only [F.den, Src8.sym_den h hx])
    simp only [XInstr.exec, readNarrow_eq, show Narrow.b.bytes = 1 from rfl]
    cases hr : rawRead dst s mem (s.rip + BitVec.ofNat 64 len) 1 <;>
      simp only [hr, Option.map_none, Option.map_some] at this ⊢ <;> exact this
  | cmov sz c dst src =>
    cases hs
    simp only [XInstr.exec, readRM_eq]
    cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) sz.bytes with
    | none => simp only [Option.map_none]; rw [runStmts_append, sRead_none h hnx hr]; rfl
    | some xw =>
      obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
      simp only [Option.map_some]
      apply StepRel.prepend hrun
      have hcf : (sRead σ (nxOf σ len) sz.bytes src).2.2.flags = σ.flags := hok.flags
      cases hc : c.eval s.flags with
      | none =>
        have := sCond_none hok.rel hc
        rw [hcf] at this
        exact StepRel.fault this
      | some b =>
        have hrun2 := sCond_some hok.rel hc
        rw [hcf] at hrun2
        rw [hrun2]
        have hp := hok.rel.push (if b then 1#64 else 0#64)
        have hx2 := env1.ext_push (if b then 1#64 else 0#64)
        have key := hp.setReg' dst
          (e := .sel (.v (sRead σ (nxOf σ len) sz.bytes src).2.2.n)
            (.zext sz.bits (sRead σ (nxOf σ len) sz.bytes src).2.1) (.zext sz.bits (σ.regs dst)))
          ⟨by simp [E.wf, SState.fresh], E.wf_mono (Nat.le_succ _) hok.wf,
            E.wf_mono (Nat.le_succ _) (hok.wf_of h (h.wf.1 dst))⟩
          (v := ((if b then xw.setWidth sz.bits else Sz.read sz s dst)).setWidth 64)
          (by
            have e1 := E.den_ext hx2 (by rw [hok.rel.len]; exact hok.wf)
            have e2 := E.den_ext hx2 (by rw [hok.rel.len]; exact hok.wf_of h (h.wf.1 dst))
            simp only [E.den, e1, e2, h.regs_den hok.ext dst, ← hx]
            cases b <;> simp [Env.push, hok.rel.len, Sz.read])
        exact (ORel.pure key).retire
          (by rw [E.den_ext (env := env1) hx2 (by rw [hok.rel.len]; exact hok.nxw h len)]
              exact hok.nx h len)
          (E.wf_mono (n := env1.vals.length) (by simp [Env.push]) (by rw [hok.rel.len]; exact hok.nxw h len))
  | bt dst src =>
    cases hs
    refine sFlags_sound h len (f := .bt (σ.regs dst) (σ.regs src) σ.flags)
      ⟨h.wf.1 dst, h.wf.1 src, h.wf.2.1⟩ ?_
    simp only [F.den, h.regs, h.flags]
  | jmpInd src =>
    cases hs
    simp only [XInstr.exec, readRM_eq, show Sz.q.bytes = 8 from rfl]
    cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) 8 with
    | none => simp only [Option.map_none]; rw [runStmts_append, sRead_none h hnx hr]; rfl
    | some xw =>
      obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
      simp only [Option.map_some]
      apply StepRel.prepend hrun
      exact hok.rel.setRip' hok.wf (by rw [← hx]; exact BitVec.setWidth_eq _)
  | callInd src =>
    cases hs
    simp only [XInstr.exec, readRM_eq, show Sz.q.bytes = 8 from rfl]
    cases hr : rawRead src s mem (s.rip + BitVec.ofNat 64 len) 8 with
    | none => simp only [Option.map_none]; rw [runStmts_append, sRead_none h hnx hr]; rfl
    | some xw =>
      obtain ⟨env1, hrun, hok, hx⟩ := sRead_some h hnx hr
      simp only [Option.map_some]
      apply StepRel.prepend hrun
      have hP := sPush_sound hok.rel (val := nxOf σ len) (hok.nx h len).symm
      cases hp : pushWord s mem (s.rip + BitVec.ofNat 64 len) with
      | none => rw [hp] at hP; exact StepRel.fault hP
      | some p =>
        obtain ⟨t, m⟩ := p
        rw [hp] at hP
        obtain ⟨env', hrun', hrel⟩ := hP
        rw [hrun']
        exact hrel.setRip' hok.wf
          (by rw [E.den_ext (runStmts_ext hrun') (by rw [hok.rel.len]; exact hok.wf), ← hx];
              exact BitVec.setWidth_eq _)
  | aluHi op r imm =>
    simp only [symStep] at hs
    have hx : ((s.read r) >>> 8).setWidth 8 = ((hiByte (σ.regs r)).den env).setWidth 8 := by
      rw [hiByte_den, h.regs]
    have hw : (hiByte (σ.regs r)).wf σ.n := ⟨h.wf.1 r, trivial⟩
    have hfl : AluOp.flagsN op (((s.read r) >>> 8).setWidth 8) imm =
        (F.alu 8 op (hiByte (σ.regs r)) (.imm (imm.setWidth 64))).den env := by
      simp only [F.den, ← hx, E.den, setWidth_64_setWidth (w := 8) (by decide)]
    by_cases hop : op = .cmp
    · simp only [hop, ite_true] at hs
      cases hs
      simp only [XInstr.exec, hop, ite_true]
      exact sFlags_sound h len (f := .alu 8 .cmp (hiByte (σ.regs r)) (.imm (imm.setWidth 64)))
        ⟨hw, trivial⟩ (hop ▸ hfl)
    · simp only [hop, ite_false] at hs
      cases hs
      simp only [XInstr.exec, hop, ite_false]
      have hv : (s.read r &&& ~~~(0xFF00#64)) ||| ((AluOp.resultN op (((s.read r) >>> 8).setWidth 8) imm).setWidth 64 <<< 8) =
          (setHiByte (σ.regs r) (.alu 8 op (hiByte (σ.regs r)) (.imm (imm.setWidth 64)))).den env := by
        rw [setHiByte_den]
        simp only [E.den, ← hx, h.regs, setWidth_64_setWidth (w := 8) (by decide)]
      have h1 := h.setReg' r (e := setHiByte (σ.regs r) (.alu 8 op (hiByte (σ.regs r)) (.imm (imm.setWidth 64))))
        ⟨⟨h.wf.1 r, trivial⟩, ⟨hw, trivial⟩⟩ hv
      have hfl' : AluOp.flagsN op (((s.read r) >>> 8).setWidth 8) imm =
          (F.alu 8 op (hiByte (σ.regs r)) (.imm (imm.setWidth 64))).den env := hfl
      exact pure_sound h len
        (h1.setFlags' (f := .alu 8 op (hiByte (σ.regs r)) (.imm (imm.setWidth 64))) ⟨hw, trivial⟩ hfl')
  | testHi r imm =>
    cases hs
    have hx : ((s.read r) >>> 8).setWidth 8 = ((hiByte (σ.regs r)).den env).setWidth 8 := by
      rw [hiByte_den, h.regs]
    refine sFlags_sound h len (f := .test 8 (hiByte (σ.regs r)) (.imm (imm.setWidth 64)))
      ⟨⟨h.wf.1 r, trivial⟩, trivial⟩ ?_
    simp only [F.den, ← hx, E.den, setWidth_64_setWidth (w := 8) (by decide)]

end Silmaril.X86.Lift.Bir

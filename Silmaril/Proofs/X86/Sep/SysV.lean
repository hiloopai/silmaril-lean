module

public import Silmaril.X86.Sep.SysV.Defs
public import Silmaril.X86.Sep.Spec.Thms
public import Silmaril.Proofs.X86.Sep.Call

/-!
# Proofs: the System V template, specs from runs, and the call rule

* `sysVEntry_dom_*`: the template owns `rip`, the flags and every register that is not
  callee-saved;
* `sysVEntry_reval`: re-valued in a returned state, the entry template is the exit template;
* `satWith_of_runs`: **a System V spec from returning runs** on any segment-VC machine;
* `call_rule`: **the call rule**, from the `call rel32` triple (lifted from `Open.isa`), the
  callee's spec and the frame rule;
* `sub_mono`: refinement of specs.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepSysV

open Silmaril.X86 (State MState Word Byte Reg Insn sysv64)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.Proofs.X86.Sep (sep_reval_le regAny_reval_exact regAny_dom
  sep_dom_left sep_dom_right regAny_reval emp_reval none_of_disjoint call_step)

variable {σ : Type} {I : Isa σ}

/-! ## Registers -/

theorem regsWith_dom : ∀ {rs : List Reg} {vs : List Word} {h : Frag}, regsWith rs vs h →
    ∀ r ∈ rs, (h (.reg r)).isSome
  | [], _, _, _, r, hr => absurd hr List.not_mem_nil
  | q :: rs, v :: vs, h, hp, r, hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact sep_dom_left hp (fun _ hx => regPt_dom hx)
    · exact sep_dom_right hp (fun _ hy => regsWith_dom hy r hr)
  | q :: rs, [], h, hp, r, hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact sep_dom_left hp (fun _ hx => regAny_dom hx)
    · exact sep_dom_right hp (fun _ hy => regsWith_dom hy r hr)

theorem regsWith_regsAny : ∀ (rs : List Reg) (vs : List Word), regsWith rs vs ⊢ₛ regsAny rs
  | [], _ => fun h hp => by cases ‹List Word› <;> exact hp
  | r :: rs, v :: vs => sep_mono (fun _ hp => ⟨v, hp⟩) (regsWith_regsAny rs vs)
  | _ :: _, [] => entails_refl _

theorem regsAny_reval : ∀ {rs : List Reg} {h : Frag} (m : MState), regsAny rs h →
    regsAny rs (reval h (toFrag m))
  | [], _, _, hp => emp_reval _ hp
  | _ :: rs, _, m, hp =>
    Silmaril.Proofs.X86.Sep.sep_reval _ hp (fun _ ha => regAny_reval m ha)
      (fun _ hb => regsAny_reval (rs := rs) m hb)

theorem sysVRegs_reval {args : List Word} {h : Frag} (m : MState) (hp : SysVRegs args h) :
    SysVRet (m.core.read .rax) (reval h (toFrag m)) := by
  have hT : (regsAny argRegs ∗ (regPt .rax (m.core.read .rax) ∗ regsAny [.r10, .r11]))
      (reval h (toFrag m)) :=
    Silmaril.Proofs.X86.Sep.sep_reval _ hp
      (fun a ha => regsAny_reval m (regsWith_regsAny _ _ a ha))
      (fun b hb => Silmaril.Proofs.X86.Sep.sep_reval _ hb
        (fun a ha => regAny_reval_exact m ha) (fun c hc => regsAny_reval (rs := [.r10, .r11]) m hc))
  have e : (regsAny argRegs ∗ (regPt .rax (m.core.read .rax) ∗ regsAny [.r10, .r11])) =
      SysVRet (m.core.read .rax) := by
    simp only [SysVRet, regsAny, regsWith, argRegs, clobberedRegs]
    ac_rfl
  rw [← e]; exact hT

theorem sysVRegs_dom {args : List Word} {h : Frag} (hp : SysVRegs args h) {r : Reg}
    (hr : r ∈ argRegs ∨ r ∈ scratchRegs) : (h (.reg r)).isSome := by
  rcases hr with hr | hr
  · exact sep_dom_left hp (fun _ ha => regsWith_dom ha r hr)
  · exact sep_dom_right hp (fun _ hb => regsWith_dom hb r hr)

/-! ## The template -/

theorem sysVEntry_dom_rip {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    (hT : S.SysVEntry x entry sp ret h) : (h .rip).isSome :=
  sep_dom_left hT (fun _ ha => ripPt_dom ha)

theorem sysVEntry_dom_flags {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    (hT : S.SysVEntry x entry sp ret h) : (h .flags).isSome :=
  sep_dom_right hT fun _ h1 => sep_dom_right h1 fun _ h2 => sep_dom_right h2 fun _ h3 =>
    sep_dom_left h3 fun _ h4 => flagsAny_dom h4

theorem sysVEntry_dom_reg {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    (hT : S.SysVEntry x entry sp ret h) {r : Reg} (hr : r ∉ sysv64.calleeSaved) :
    (h (.reg r)).isSome := by
  by_cases hsp : r = .rsp
  · subst hsp
    exact sep_dom_right hT fun _ h1 => sep_dom_left h1 fun _ h2 => regPt_dom h2
  · have hmem : r ∈ argRegs ∨ r ∈ scratchRegs := by
      cases r <;> simp_all [argRegs, scratchRegs, Silmaril.X86.sysv64_calleeSaved]
    exact sep_dom_right hT fun _ h1 => sep_dom_right h1 fun _ h2 => sep_dom_left h2
      fun _ h3 => sysVRegs_dom h3 hmem

theorem sysVEntry_reval {S : FnSpec} {x : S.Arg} {entry sp ret : Word} {h : Frag}
    {m fin : MState} (hT : S.SysVEntry x entry sp ret h) (hl : Le h (toFrag m))
    (hst : S.stack ≤ sp.toNat) (hrip : fin.core.rip = ret)
    (hrsp : fin.core.read .rsp = sp + 8#64) (hreg : fin.memory.regions = m.memory.regions) :
    S.SysVExit sp ret (fin.core.read .rax) (reval h (toFrag fin)) := by
  have hperms : ∀ a, permsAt fin.memory a = permsAt m.memory a := by
    intro a; simp [permsAt, Memory.permits, hreg]
  have hI : (ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ SysVRet (fin.core.read .rax) ∗ flagsAny ∗
      blockAny sp.toNat 8 ∗ blockAny (sp.toNat - S.stack) S.stack) (reval h (toFrag fin)) := by
    refine sep_reval_le _ hT hl (fun a ha _ => hrip ▸ ripPt_reval fin ha) fun b hb hlb => ?_
    refine sep_reval_le _ hb hlb (fun a ha _ => hrsp ▸ regPt_reval fin ha) fun b hb hlb => ?_
    refine sep_reval_le _ hb hlb (fun a ha _ => sysVRegs_reval fin ha) fun b hb hlb => ?_
    refine sep_reval_le _ hb hlb (fun a ha _ => flagsAny_reval fin ha) fun b hb hlb => ?_
    refine sep_reval_le _ hb hlb (fun a ha hla => ?_) fun b hb hlb => ?_
    · have hw := wordPt_blockAny _ _ a ha
      exact blockAny_reval hw fun i hi => (hperms _).symm ▸ (blockAny_le hw hla i hi).2
    · exact blockAny_reval hb fun i hi => (hperms _).symm ▸ (blockAny_le hb hlb i hi).2
  have e : (ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ SysVRet (fin.core.read .rax) ∗ flagsAny ∗
      blockAny sp.toNat 8 ∗ blockAny (sp.toNat - S.stack) S.stack) =
      S.SysVExit sp ret (fin.core.read .rax) := by
    simp only [FnSpec.SysVExit]
    rw [blockAny_add, show sp.toNat - S.stack + S.stack = sp.toNat by omega]
    ac_rfl
  rw [← e]; exact hI

/-! ## Specs from runs -/

theorem satWith_of_runs {A : Word → Prop} {S : FnSpec} {C : SProp} {entry : Word}
    (h : ∀ x sp ret (m : σ) (hc ht hu : Frag), I.live m → A sp → S.stack ≤ sp.toNat → C hc →
      S.SysVEntry x entry sp ret ht → S.pre x hu → Disjoint hc (union ht hu) →
      Disjoint ht hu → Le (union hc (union ht hu)) (frag I m) →
      ∃ fin, Reaches I.step m fin ∧ (I.core fin).rip = ret ∧
        (I.core fin).read .rsp = sp + 8#64 ∧
        (∀ r ∈ sysv64.calleeSaved, (I.core fin).read r = (I.core m).read r) ∧
        (I.mem m).WritesWithin (I.mem fin) (fun a => (union ht hu (.mem a)).isSome) ∧
        S.post x ((I.core fin).read .rax) (reval hu (frag I fin))) :
    S.SatWith I A C entry := by
  intro x sp ret hA hst
  apply Triple.of_local
  intro m h₁ hlive hP hl
  obtain ⟨hc, r1, hcP, hr1, hlc, hlr1, hd1, rfl⟩ := sep_le hP hl
  obtain ⟨ht, hu, htP, huP, hlt, hlu, hd2, rfl⟩ := sep_le hr1 hlr1
  obtain ⟨fin, hrun, hrip, hrsp, hcs, hww, hpost⟩ :=
    h x sp ret m hc ht hu hlive hA hst hcP htP huP hd1 hd2 hl
  have unchanged : ∀ l, union ht hu l = none → frag I fin l = frag I m l := by
    intro l hl0
    obtain ⟨ht0, -⟩ := Silmaril.Proofs.X86.Sep.Frag.union_eq_none.mp hl0
    cases l with
    | reg r =>
      have hr : r ∈ sysv64.calleeSaved := by
        by_contra hn
        have := sysVEntry_dom_reg htP hn
        rw [ht0] at this; cases this
      simp [frag, toFrag, hcs r hr]
    | rip => have := sysVEntry_dom_rip htP; rw [ht0] at this; cases this
    | flags => have := sysVEntry_dom_flags htP; rw [ht0] at this; cases this
    | mem a =>
      have hb := hww.2 a (by show ¬ ((union ht hu (.mem a)).isSome = true); rw [hl0]; simp)
      simp only [frag, toFrag]
      rw [hb]
      simp [permsAt, Memory.permits, hww.1]
    | regions => simp [frag, toFrag, hww.1]
  refine ⟨fin, hrun, fun l hl0 => unchanged l (Silmaril.Proofs.X86.Sep.Frag.union_eq_none.mp hl0).2, ?_⟩
  have d1 := Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd1 (frag I fin)
  have d2 := Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd2 (frag I fin)
  rw [Silmaril.Proofs.X86.Sep.Frag.reval_union] at d1
  rw [Silmaril.Proofs.X86.Sep.Frag.reval_union, Silmaril.Proofs.X86.Sep.Frag.reval_union]
  refine ⟨_, _, d1, rfl, ?_, (I.core fin).read .rax, _, _, d2, rfl,
    sysVEntry_reval htP hlt hst hrip hrsp hww.1, hpost⟩
  rw [Silmaril.Proofs.X86.Sep.Frag.reval_eq_of_agree hlc (fun l hl' => unchanged l (none_of_disjoint hd1 hl'))]
  exact hcP

/-! ## The call rule -/

theorem call_rule (E : Silmaril.X86.Open.isa.Extends I) {A : Word → Prop} {S : FnSpec}
    {Cf : SProp} {f pc s : Word} {rel : BitVec 32} (x : S.Arg) (hS : S.SatWith I A Cf f)
    (hf : pc + 5#64 + rel.signExtend 64 = f) (hA : A (s - 8#64))
    (hlow : S.stack + 8 ≤ s.toNat) :
    SPEC I (codePt pc.toNat (Insn.encode (.call rel)) ∗ Cf)
      (ripPt pc ∗ regPt .rsp s ∗ SysVRegs (S.args x) ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.pre x)
      (sexists fun v => ripPt (pc + 5#64) ∗ regPt .rsp s ∗ SysVRet v ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.post x v) := by
  have esp : (s - 8#64).toNat = s.toNat - 8 := Silmaril.Proofs.X86.Sep.toNat_sub_eight
    (by omega)
  have eback : s - 8#64 + 8#64 = s := by bv_omega
  have h1 := Triple.frame ((call_step pc s rel (by omega)).lift E)
    (Cf ∗ SysVRegs (S.args x) ∗ flagsAny ∗ blockAny (s.toNat - 8 - S.stack) S.stack ∗ S.pre x)
  have h2 := Triple.frame (hS x (s - 8#64) (pc + 5#64) hA (by omega))
    (codePt pc.toNat (Insn.encode (.call rel)))
  unfold SPEC at h2 ⊢
  refine Triple.trans (Triple.pre ?_ h1) (Triple.post (Triple.pre ?_ h2) ?_)
  · apply entails_of_eq
    rw [blockAny_add, show s.toNat - 8 - S.stack + S.stack = s.toNat - 8 by omega]
    ac_rfl
  · apply entails_of_eq
    simp only [FnSpec.SysVPre, FnSpec.SysVEntry]
    rw [esp, hf]
    ac_rfl
  · simp only [FnSpec.SysVPost, FnSpec.SysVExit]
    rw [sep_sexists, sexists_sep, sep_sexists]
    refine sexists_elim fun v => sexists_intro v (entails_of_eq ?_)
    rw [esp, eback]
    ac_rfl

/-! ## Refinement -/

theorem sub_trans {S T U : FnSpec} (h₁ : S.Sub T) (h₂ : T.Sub U) : S.Sub U := by
  refine ⟨le_trans h₁.stack h₂.stack, fun z => ?_⟩
  obtain ⟨y, hy, R₂, hpre₂, hpost₂⟩ := h₂.arg z
  obtain ⟨x, hx, R₁, hpre₁, hpost₁⟩ := h₁.arg y
  refine ⟨x, hx.trans hy, R₁ ∗ R₂, ?_, fun v => ?_⟩
  · refine entails_trans hpre₂ (entails_trans (sep_mono_left R₂ hpre₁) ?_)
    exact entails_of_eq (sep_assoc _ _ _)
  · refine entails_trans (entails_of_eq (sep_assoc _ _ _).symm) ?_
    exact entails_trans (sep_mono_left R₂ (hpost₁ v)) (hpost₂ v)


theorem sub_mono {A : Word → Prop} {S T : FnSpec} {C : SProp} {entry : Word}
    (hS : S.SatWith I A C entry) (hsub : S.Sub T) : T.SatWith I A C entry := by
  intro y sp ret hA hst
  obtain ⟨x, hargs, R, hpre, hpost⟩ := hsub.arg y
  have hle := hsub.stack
  have h := SPEC.frame (hS x sp ret hA (le_trans hle hst))
    (blockAny (sp.toNat - T.stack) (T.stack - S.stack) ∗ R)
  have split : ∀ k, blockAny (sp.toNat - T.stack) (T.stack + k) =
      (blockAny (sp.toNat - T.stack) (T.stack - S.stack) ∗
        blockAny (sp.toNat - S.stack) (S.stack + k)) := by
    intro k
    rw [← show sp.toNat - T.stack + (T.stack - S.stack) = sp.toNat - S.stack by omega,
      ← blockAny_add]
    congr 1; omega
  refine SPEC.conseq ?_ h ?_
  · simp only [FnSpec.SysVPre]
    refine entails_trans (sep_mono_right _ hpre) (entails_of_eq ?_)
    simp only [FnSpec.SysVEntry]
    have split0 := split 0
    simp only [Nat.add_zero] at split0
    rw [hargs, split0]
    ac_rfl
  · simp only [FnSpec.SysVPost]
    rw [sexists_sep]
    refine sexists_elim fun v => sexists_intro v ?_
    refine entails_trans (entails_of_eq ?_) (sep_mono_right _ (hpost v))
    simp only [FnSpec.SysVExit]
    rw [split 8]
    ac_rfl

end Silmaril.Proofs.X86.SepSysV

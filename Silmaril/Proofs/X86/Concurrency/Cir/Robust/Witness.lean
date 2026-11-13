module

public import Silmaril.Proofs.X86.Concurrency.Cir.Robust.Sound

/-!
# The explorer: SC final-state checks and TSO witnesses

Two more uses of the explorer, so that a failed robustness check can be
turned into a theorem:

* `scCheck_sound`: a closed set under the fused SC successors (`scStepT_complete`, with the same
  silent-step argument as for TSO, run on `Cfg.toO`) covers every finished SC configuration, so a
  property of its finished elements holds of every finished SC-reachable configuration;
* `tsoStates_reach`: every explored TSO configuration is TSO-reachable (`tsoStepT_sound`), so a
  finished element is a TSO witness.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Robust

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Csl (Heap Ent TStep view newest OStep ScStep upd OCfg Cfg Star)

/-! ## SC steps are enumerated -/

/-- **Every SC step is enumerated.** -/
theorem scStepT_complete {N : Nat} {c : CSt} (hok : c.okB N = true) {C' : Cfg}
    (h : ScStep N c.cfg C') : ∃ t < N, ∃ d ∈ scStepT c t, d.cfg = C' := by
  obtain ⟨hl, -, hnb⟩ := okB_parts hok
  cases h with
  | tau ht hs =>
    rename_i t s' rs'
    have hm := tsucc_complete (vw := memOf c.mem) hs (hnb t ht) noneOk.1
    refine ⟨t, ht, c.setTh t s' rs', ?_, cfg_eq (th_setTh c (hl ▸ ht) s' rs') rfl⟩
    simp only [scStepT, List.mem_filterMap]
    exact ⟨_, hm, rfl⟩
  | lab ht hs hmem hc hrd =>
    rename_i t l s' rs'
    have hm := tsucc_complete (vw := memOf c.mem) hs (hnb t ht)
      (fun l' e p hp => by cases e; exact hrd p hp)
    have hnbl := (tsucc_sound hm).2.2 l rfl
    have hmap : mappedB c.mem l = true := (mappedB_iff hnbl).mpr hc
    refine ⟨t, ht, { c.setTh t s' rs' with mem := updL c.mem l }, ?_,
      cfg_eq (th_setTh c (hl ▸ ht) s' rs') (memOf_updL _ _ hnbl)⟩
    simp only [scStepT, List.mem_filterMap]
    exact ⟨_, hm, by simp [hmem, hmap]⟩

theorem scStepT_buf {c : CSt} {t : Nat} {d : CSt} (h : d ∈ scStepT c t) : d.buf = c.buf := by
  simp only [scStepT, List.mem_filterMap] at h
  obtain ⟨⟨o, s', rs'⟩, -, hd⟩ := h
  cases o with
  | none => simp only [Option.some.injEq] at hd; subst hd; rfl
  | some l =>
    simp only at hd
    split at hd
    · simp only [Option.some.injEq] at hd; subst hd; rfl
    · cases hd

theorem tauNF_buf (t : Nat) : ∀ (f : Nat) (c : CSt), (tauNF t f c).buf = c.buf
  | 0, _ => rfl
  | f + 1, c => by
    simp only [tauNF]
    split
    · rw [tauNF_buf t f]; rfl
    · rfl

/-! ## The SC cover -/

/-- The SC configurations whose silent completion is in `S`. -/
def CovS (N : Nat) (S : List CSt) (C : Cfg) : Prop := ∃ d ∈ S, Star (TauStep N) C.toO d.ocfg

theorem closedScB_parts {N : Nat} {S : List CSt} (h : closedScB N S = true) {d : CSt}
    (hd : d ∈ S) : d.okB N = true ∧ d.normalB N = true ∧ d.cfg.toO = d.ocfg ∧
      ∀ e ∈ fscSucc N d, e ∈ S := by
  simp only [closedScB, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h d hd
  exact ⟨h1, h2, toO_ocfg h3, fun e he => memB_ofList (h4 e he)⟩

theorem covS_step {N : Nat} {S : List CSt} (hcl : closedScB N S = true) {C C' : Cfg}
    (hc : CovS N S C) (hst : ScStep N C C') : CovS N S C' := by
  obtain ⟨d, hd, hpath⟩ := hc
  obtain ⟨hok, hnorm, hto, hsucc⟩ := closedScB_parts hcl hd
  have hD := normal_of_normalB hnorm
  obtain ⟨hmem, hbuf⟩ := taus_mb hpath
  cases hst with
  | tau ht hs => exact ⟨d, hd, tau_into_normal hpath hD ⟨_, ht, _, _, hs, rfl⟩⟩
  | lab ht hs hm hc hrd =>
    rename_i t l s' rs'
    have hn : ∀ s₂ rs₂, ¬ TStep (C.ts t).1 (C.ts t).2 none s₂ rs₂ :=
      fun _ _ h => tstep_tau_excl h hs
    have hkeep := taus_keep hpath hn
    have hts : d.cfg.ts t = C.ts t := hkeep
    have hmem' : d.cfg.mem = C.mem := hmem
    have hst' : ScStep N d.cfg ⟨upd d.cfg.ts t (s', rs'), l.updH d.cfg.mem⟩ :=
      .lab ht (by rw [hts]; exact hs) hm (by rw [hmem']; exact hc) (by rw [hmem']; exact hrd)
    obtain ⟨t', ht', e, he, hecfg⟩ := scStepT_complete hok hst'
    have heb : e.buf = d.buf := scStepT_buf he
    refine ⟨tauNF t' tauFuel e, hsucc _ ?_, star_trans ?_ (tauNF_tau ht' tauFuel e)⟩
    · simp only [fscSucc, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨t', ht', e, he, rfl⟩
    · have := taus_lift hpath hn (s', rs') (l.updH C.mem) (fun _ => [])
      have hdb : d.ocfg.buf = fun _ => [] := by rw [← hto]; rfl
      have he' : e.ocfg = ⟨upd d.ocfg.ts t (s', rs'), l.updH C.mem, fun _ => []⟩ := by
        apply ocfg_eq
        · exact congrArg Cfg.ts hecfg
        · rw [← hmem']; exact congrArg Cfg.mem hecfg
        · rw [heb, ← hdb]; rfl
      rw [he']
      exact this

/-- **The SC final-state check is sound.** -/
theorem scCheck_sound {N fuel : Nat} {c0 : CSt} {P : CSt → Bool} (h : scCheck N fuel c0 P = true)
    {C : Cfg} (hr : Csl.ScReach N c0.cfg C) (hfin : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ d, P d = true ∧ d.cfg = C := by
  simp only [scCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hcl, h0⟩, hb⟩, hP⟩ := h
  rw [List.all_eq_true] at hP
  have h0' := memB_ofList h0
  have hc : CovS N (scStates N fuel c0) c0.cfg := by
    refine ⟨_, h0', ?_⟩
    rw [toO_ocfg hb]
    exact normAll_tau tauFuel (List.range N) (fun t ht => List.mem_range.mp ht) c0
  have key : ∀ {X Y : Cfg}, Csl.ScReach N X Y → CovS N (scStates N fuel c0) X →
      CovS N (scStates N fuel c0) Y := by
    intro X Y hxy
    induction hxy with
    | refl => exact id
    | step h _ ih => exact fun hx => ih (covS_step hcl hx h)
  obtain ⟨d, hd, hp⟩ := key hr hc
  have hfin' : ∀ t < N, (C.toO.ts t).1 = .skip := hfin
  have heq := taus_done hp hfin'
  obtain ⟨-, -, hto, -⟩ := closedScB_parts hcl hd
  have hdc : d.cfg = C := by
    have := congrArg (fun X : OCfg => (⟨X.ts, X.mem⟩ : Cfg)) (hto.trans heq)
    simp only [Csl.Cfg.toO] at this
    exact cfg_eq (congrArg Cfg.ts this) (congrArg Cfg.mem this)
  have := hP d hd
  have hdone : d.doneB N = true := by
    simp only [CSt.doneB, List.all_eq_true, List.mem_range]
    intro t ht
    have h1 := hfin t ht
    rw [← hdc] at h1
    simp only [CSt.cfg] at h1
    rw [h1]; rfl
  simp only [hdone, Bool.not_true, Bool.false_or] at this
  exact ⟨d, this, hdc⟩

/-! ## TSO witnesses -/

theorem tauStep_ostep {N : Nat} {C D : OCfg} (h : Star (TauStep N) C D) :
    Csl.OReach .tso N C D := by
  induction h with
  | refl => exact .refl
  | step h _ ih =>
    obtain ⟨t, ht, s', rs', hs, rfl⟩ := h
    exact .step (.tau ht hs) ih

/-- **Every enumerated TSO step is a TSO step.** -/
theorem tsoStepT_sound {N : Nat} {c : CSt} {t : Nat} (ht : t < N) (hb : t < c.buf.length)
    {d : CSt} (h : d ∈ tsoStepT c t) : OStep .tso N c.ocfg d.ocfg := by
  simp only [tsoStepT, List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨⟨o, s', rs'⟩, hm, hd⟩ | h
  · have hlt := th_lt hm
    obtain ⟨hs, hrd, hnb⟩ := tsucc_sound hm
    cases o with
    | none =>
      simp only [Option.some.injEq] at hd
      subst hd
      have := OStep.tau (M := .tso) (N := N) (C := c.ocfg) ht hs
      rwa [← ocfg_eq (c := c.setTh t s' rs')
        (C := ⟨upd c.ocfg.ts t (s', rs'), c.ocfg.mem, c.ocfg.buf⟩)
        (th_setTh c hlt s' rs') rfl rfl] at this
    | some l =>
      simp only at hd
      split at hd
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        have hnbl := hnb l rfl
        split at hd
        · rename_i hdr
          split at hd
          · rename_i he
            simp only [Option.some.injEq] at hd
            subst hd
            have := OStep.drained (M := .tso) (N := N) (C := c.ocfg) ht hs hc.1 hdr he
              ((mappedB_iff hnbl).mp hc.2) (by have := hrd l rfl; rw [he] at this; exact this)
            rwa [← ocfg_eq (c := { c.setTh t s' rs' with mem := updL c.mem l })
              (C := ⟨upd c.ocfg.ts t (s', rs'), l.updH c.ocfg.mem, c.ocfg.buf⟩)
              (th_setTh c hlt s' rs') (memOf_updL _ _ hnbl) rfl] at this
          · cases hd
        · rename_i hdr
          simp only [Option.some.injEq] at hd
          subst hd
          have := OStep.buffered (M := .tso) (N := N) (C := c.ocfg) ht hs hc.1
            (by simpa using hdr) ((mappedB_iff hnbl).mp hc.2) (hrd l rfl)
          rwa [← ocfg_eq (c := { c.setTh t s' rs' with buf := c.buf.set t (c.bufT t ++ l.ents) })
            (C := ⟨upd c.ocfg.ts t (s', rs'), c.ocfg.mem,
              upd c.ocfg.buf t (c.ocfg.buf t ++ l.ents)⟩)
            (th_setTh c hlt s' rs') rfl (bufGet_set c.buf hb _)] at this
      · cases hd
  · split at h
    · rename_i e post hbt
      simp only [List.mem_singleton] at h
      subst h
      have := OStep.flush (M := .tso) (N := N) (C := c.ocfg) (pre := []) ht hbt
        (by simp [Csl.Ent.passes]; cases e <;> simp) (Or.inr rfl)
      rwa [← ocfg_eq (c := { c with mem := applyE c.mem e, buf := c.buf.set t post })
        (C := ⟨c.ocfg.ts, e.apply c.ocfg.mem, upd c.ocfg.buf t ([] ++ post)⟩)
        rfl (memOf_applyE _ _) (bufGet_set c.buf hb _)] at this
    · simp at h

theorem tauNF_len (t : Nat) : ∀ (f : Nat) (c : CSt), (tauNF t f c).buf.length = c.buf.length
  | f, c => by rw [tauNF_buf]

theorem tsoStepT_len {c : CSt} {t : Nat} {d : CSt} (h : d ∈ tsoStepT c t) :
    d.buf.length = c.buf.length := by
  simp only [tsoStepT, List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨⟨o, s', rs'⟩, -, hd⟩ | h
  · cases o with
    | none => simp only [Option.some.injEq] at hd; subst hd; rfl
    | some l =>
      simp only at hd
      split at hd
      · split at hd
        · split at hd
          · simp only [Option.some.injEq] at hd; subst hd; rfl
          · cases hd
        · simp only [Option.some.injEq] at hd; subst hd; simp
      · cases hd
  · split at h
    · simp only [List.mem_singleton] at h; subst h; simp
    · simp at h

/-- **Every explored TSO configuration is TSO-reachable** (for `N` threads with `N` buffers). -/
theorem tsoStates_reach {N fuel : Nat} {c0 : CSt} (hb : c0.buf.length = N) {e : CSt}
    (he : e ∈ tsoStates N fuel c0) : Csl.OReach .tso N c0.ocfg e.ocfg ∧ e.buf.length = N := by
  have hn : (normAll N tauFuel c0).buf.length = N := by
    have : ∀ (l : List Nat) (c : CSt), (l.foldl (fun c t => tauNF t tauFuel c) c).buf.length =
        c.buf.length := by
      intro l; induction l with
      | nil => intro c; rfl
      | cons t l ih => intro c; simp only [List.foldl_cons]; rw [ih, tauNF_len]
    rw [normAll, this, hb]
  have h0 : Csl.OReach .tso N c0.ocfg (normAll N tauFuel c0).ocfg :=
    tauStep_ostep (normAll_tau tauFuel (List.range N) (fun t ht => List.mem_range.mp ht) c0)
  refine explore_inv (ftsoSucc N)
    (fun x => Csl.OReach .tso N c0.ocfg x.ocfg ∧ x.buf.length = N) ?_ fuel _ _ _
    (fun x hx => by simp at hx; subst hx; exact ⟨h0, hn⟩)
    (fun x hx => by simp at hx; subst hx; exact ⟨h0, hn⟩) e he
  intro x ⟨hx, hxl⟩ y hy
  simp only [ftsoSucc, List.mem_flatMap, List.mem_range, List.mem_map] at hy
  obtain ⟨t, ht, z, hz, rfl⟩ := hy
  refine ⟨star_trans hx (.step (tsoStepT_sound ht (hxl ▸ ht) hz)
    (tauStep_ostep (tauNF_tau ht tauFuel z))), ?_⟩
  rw [tauNF_len, tsoStepT_len hz, hxl]

/-! ## From Boolean finals to configurations -/

theorem drained_of {c : CSt} (h : c.drainedB = true) : c.ocfg.Drained := by
  intro t
  simp only [CSt.drainedB, List.all_eq_true, List.isEmpty_iff] at h
  simp only [CSt.ocfg, List.getD_eq_getElem?_getD]
  cases ht : c.buf[t]? with
  | none => rfl
  | some b => simpa using h b (List.mem_of_getElem? ht)

theorem done_of {N : Nat} {c : CSt} (h : c.doneB N = true) : ∀ t < N, (c.ocfg.ts t).1 = .skip := by
  intro t ht
  simp only [CSt.doneB, List.all_eq_true, List.mem_range] at h
  exact Silmaril.X86.Concurrency.Cir.TvCfg.sbeq_eq (h t ht)

/-- **A TSO witness**: a finished, drained explored configuration satisfying `P` is reachable. -/
theorem witness_of_any {N fuel : Nat} {c0 : CSt} (hb : c0.buf.length = N)
    (he : c0.buf.all List.isEmpty = true) {P : CSt → Bool}
    (h : ((tsoStates N fuel c0).any fun c => c.doneB N && c.drainedB && P c) = true) :
    ∃ d, Csl.OReach .tso N c0.cfg.toO d.ocfg ∧ d.ocfg.Drained ∧ (∀ t < N, (d.ocfg.ts t).1 = .skip) ∧
      P d = true := by
  simp only [List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨d, hd, ⟨h1, h2⟩, h3⟩ := h
  refine ⟨d, ?_, drained_of h2, done_of h1, h3⟩
  rw [toO_ocfg he]
  exact (tsoStates_reach hb hd).1

end Silmaril.Proofs.X86.Concurrency.Cir.Robust

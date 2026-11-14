module

public import Silmaril.Proofs.X86.Concurrency.Cir.Robust.Cfg

/-!
# The explorer: soundness of eager silent steps, the TSO check and the robustness check

Silent `Csl.TStep`s are deterministic (`tstep_tau_det`), a thread with a
silent step has no labelled one (`tstep_tau_excl`), and silent steps touch neither memory nor
buffers. So a silent step commutes with every step of another thread and with every flush, and
every configuration the TSO machine reaches can be completed by silent steps to an element of a
closed set of silent-step-free configurations (`fused_reach`). A finished configuration has no
silent step, so it *is* an element (`tsoCheck_sound`, `robustB_sound`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Robust

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Csl (Heap Ent TStep view newest OStep ScStep upd OCfg Cfg Star)

/-! ## Silent steps are deterministic and exclusive -/

theorem tstep_tau_det {s : Stmt} {rs : Regs} {s₁ : Stmt} {rs₁ : Regs}
    (h : TStep s rs none s₁ rs₁) : ∀ {s₂ rs₂}, TStep s rs none s₂ rs₂ → s₁ = s₂ ∧ rs₁ = rs₂ := by
  generalize ho : (none : Option Lab) = o at h
  induction h with
  | assign => intro _ _ h'; cases h'; exact ⟨rfl, rfl⟩
  | seq h ih =>
    intro _ _ h'
    cases h' with
    | seq h' => obtain ⟨rfl, rfl⟩ := ih ho h'; exact ⟨rfl, rfl⟩
    | seqSkip => cases h
  | seqSkip => intro _ _ h'; cases h' with
    | seq h' => cases h'
    | seqSkip => exact ⟨rfl, rfl⟩
  | iteT hc => intro _ _ h'; cases h' with
    | iteT _ => exact ⟨rfl, rfl⟩
    | iteF hc' => rw [hc] at hc'; cases hc'
  | iteF hc => intro _ _ h'; cases h' with
    | iteT hc' => rw [hc] at hc'; cases hc'
    | iteF _ => exact ⟨rfl, rfl⟩
  | loopT hc => intro _ _ h'; cases h' with
    | loopT _ => exact ⟨rfl, rfl⟩
    | loopF hc' => rw [hc] at hc'; cases hc'
  | loopF hc => intro _ _ h'; cases h' with
    | loopT hc' => rw [hc] at hc'; cases hc'
    | loopF _ => exact ⟨rfl, rfl⟩
  | _ => cases ho

theorem tstep_tau_excl {s : Stmt} {rs : Regs} {s₁ : Stmt} {rs₁ : Regs}
    (h : TStep s rs none s₁ rs₁) : ∀ {l s₂ rs₂}, ¬ TStep s rs (some l) s₂ rs₂ := by
  generalize ho : (none : Option Lab) = o at h
  induction h with
  | assign => intro _ _ _ h'; cases h'
  | seq h ih =>
    intro _ _ _ h'
    cases h' with
    | seq h' => exact ih ho h'
  | seqSkip => intro _ _ _ h'; cases h' with
    | seq h' => cases h'
  | iteT => intro _ _ _ h'; cases h'
  | iteF => intro _ _ _ h'; cases h'
  | loopT => intro _ _ _ h'; cases h'
  | loopF => intro _ _ _ h'; cases h'
  | _ => cases ho

/-! ## Updates commute -/

theorem upd_ne {α : Type} (f : Nat → α) {t u : Nat} (h : u ≠ t) (x : α) : upd f t x u = f u := by
  simp [upd, h]

theorem upd_comm {α : Type} (f : Nat → α) {t u : Nat} (h : t ≠ u) (x y : α) :
    upd (upd f t x) u y = upd (upd f u y) t x := by
  funext v; simp only [upd]; by_cases hv : v = u <;> by_cases hv' : v = t <;> simp_all

/-! ## Silent paths -/

/-- No thread below `N` has a silent step. -/
def Normal (N : Nat) (C : OCfg) : Prop :=
  ∀ t < N, ∀ s' rs', ¬ TStep (C.ts t).1 (C.ts t).2 none s' rs'

theorem normal_of_normalB {N : Nat} {d : CSt} (h : d.normalB N = true) : Normal N d.ocfg := by
  intro t ht s' rs' hs
  have hm := tsucc_complete_tau (vw := memOf d.mem) hs
  simp only [CSt.normalB, List.all_eq_true, List.mem_range] at h
  have := h t ht
  simp only [CSt.normalT, List.all_eq_true] at this
  simpa using this _ hm

/-- Silent paths keep memory and buffers. -/
theorem taus_mb {N : Nat} {C D : OCfg} (h : Star (TauStep N) C D) :
    D.mem = C.mem ∧ D.buf = C.buf := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | step h _ ih =>
    obtain ⟨t, _, s', rs', _, rfl⟩ := h
    exact ih

/-- A thread with no silent step keeps its state along a silent path. -/
theorem taus_keep {N : Nat} {C D : OCfg} (h : Star (TauStep N) C D) {t : Nat}
    (hn : ∀ s' rs', ¬ TStep (C.ts t).1 (C.ts t).2 none s' rs') : D.ts t = C.ts t := by
  induction h with
  | refl => rfl
  | step h _ ih =>
    obtain ⟨u, _, s', rs', hs, rfl⟩ := h
    have hu : t ≠ u := fun e => by subst e; exact hn _ _ hs
    have := ih (by simpa [upd_ne _ hu] using hn)
    simpa [upd_ne _ hu] using this

/-- A silent path lifts over a change of memory and buffers. -/
theorem taus_lift_mb {N : Nat} {C D : OCfg} (h : Star (TauStep N) C D) (M : Heap)
    (B : Nat → List Ent) :
    Star (TauStep N) { C with mem := M, buf := B } { D with mem := M, buf := B } := by
  induction h with
  | refl => exact .refl
  | step h _ ih =>
    obtain ⟨u, hu, s', rs', hs, rfl⟩ := h
    exact .step ⟨u, hu, s', rs', hs, rfl⟩ ih

/-- A silent path that does not move thread `t` lifts over a change of `t`'s state, memory and
buffers. -/
theorem taus_lift {N : Nat} {C D : OCfg} (h : Star (TauStep N) C D) {t : Nat}
    (hn : ∀ s' rs', ¬ TStep (C.ts t).1 (C.ts t).2 none s' rs') (x : Stmt × Regs) (M : Heap)
    (B : Nat → List Ent) :
    Star (TauStep N) { C with ts := upd C.ts t x, mem := M, buf := B }
      { D with ts := upd D.ts t x, mem := M, buf := B } := by
  induction h with
  | refl => exact .refl
  | step h _ ih =>
    obtain ⟨u, hu, s', rs', hs, rfl⟩ := h
    have hut : t ≠ u := fun e => by subst e; exact hn _ _ hs
    refine .step ⟨u, hu, s', rs', ?_, ?_⟩ (ih (by simpa [upd_ne _ hut] using hn))
    · simpa [upd_ne _ (Ne.symm hut)] using hs
    · simp only [upd_comm _ hut]

/-- **A silent step into a normal target** stays on a silent path to it. -/
theorem tau_into_normal {N : Nat} {C D : OCfg} (h : Star (TauStep N) C D) (hD : Normal N D) :
    ∀ {C'}, TauStep N C C' → Star (TauStep N) C' D := by
  induction h with
  | refl =>
    intro C' hc
    obtain ⟨t, ht, s', rs', hs, -⟩ := hc
    exact absurd hs (hD t ht s' rs')
  | @step A B _ h1 htail ih =>
    intro C' hc
    obtain ⟨u, hu, s₁, rs₁, hs₁, rfl⟩ := h1
    obtain ⟨t, ht, s', rs', hs, rfl⟩ := hc
    by_cases htu : t = u
    · subst htu
      obtain ⟨rfl, rfl⟩ := tstep_tau_det hs hs₁
      exact htail
    · have hs1 : TStep ((upd A.ts u (s₁, rs₁)) t).1 ((upd A.ts u (s₁, rs₁)) t).2 none s' rs' := by
        simpa [upd_ne _ htu] using hs
      have h2 := ih hD (C' := ⟨upd (upd A.ts u (s₁, rs₁)) t (s', rs'), A.mem, A.buf⟩)
        ⟨t, ht, s', rs', hs1, rfl⟩
      refine .step ⟨u, hu, s₁, rs₁, ?_, ?_⟩ h2
      · simpa [upd_ne _ (Ne.symm htu)] using hs₁
      · simp only [upd_comm _ htu]

/-! ## The closed set covers every reachable configuration -/

/-- Every configuration completes by silent steps to an element of `S`. -/
def Cov (N : Nat) (S : List CSt) (C : OCfg) : Prop := ∃ d ∈ S, Star (TauStep N) C d.ocfg

theorem closedB_parts {N : Nat} {S : List CSt} (h : closedB N S = true) {d : CSt} (hd : d ∈ S) :
    d.okB N = true ∧ d.normalB N = true ∧ ∀ e ∈ ftsoSucc N d, e ∈ S := by
  simp only [closedB, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h d hd
  exact ⟨h1, h2, fun e he => memB_ofList (h3 e he)⟩

/-- From a TSO step of `d`'s configuration to an element of `S`. -/
theorem cov_of_step {N : Nat} {S : List CSt} (hcl : closedB N S = true) {d : CSt} (hd : d ∈ S)
    {D' : OCfg} (hst : OStep .tso N d.ocfg D') : Cov N S D' := by
  obtain ⟨hok, -, hsucc⟩ := closedB_parts hcl hd
  obtain ⟨t, ht, e, he, rfl⟩ := tsoStepT_complete hok hst
  refine ⟨tauNF t tauFuel e, hsucc _ ?_, tauNF_tau ht tauFuel e⟩
  simp only [ftsoSucc, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨t, ht, e, he, rfl⟩

/-- **One TSO step keeps the cover.** -/
theorem cov_step {N : Nat} {S : List CSt} (hcl : closedB N S = true) {C C' : OCfg}
    (hc : Cov N S C) (hst : OStep .tso N C C') : Cov N S C' := by
  obtain ⟨d, hd, hpath⟩ := hc
  have hD := normal_of_normalB (closedB_parts hcl hd).2.1
  obtain ⟨hmem, hbuf⟩ := taus_mb hpath
  cases hst with
  | tau ht hs => exact ⟨d, hd, tau_into_normal hpath hD ⟨_, ht, _, _, hs, rfl⟩⟩
  | buffered ht hs hm hdr hc hok =>
    rename_i t l s' rs'
    have hn : ∀ s₂ rs₂, ¬ TStep (C.ts t).1 (C.ts t).2 none s₂ rs₂ :=
      fun _ _ h => tstep_tau_excl h hs
    have hkeep := taus_keep hpath hn
    have hst' : OStep .tso N d.ocfg
        ⟨upd d.ocfg.ts t (s', rs'), d.ocfg.mem, upd d.ocfg.buf t (d.ocfg.buf t ++ l.ents)⟩ := by
      refine .buffered ht (by rw [hkeep]; exact hs) hm hdr (by rw [hmem]; exact hc)
        (by rw [hmem, hbuf]; exact hok)
    obtain ⟨d', hd', hp'⟩ := cov_of_step hcl hd hst'
    refine ⟨d', hd', star_trans ?_ hp'⟩
    have := taus_lift hpath hn (s', rs') C.mem (upd C.buf t (C.buf t ++ l.ents))
    rw [hmem, hbuf]; exact this
  | drained ht hs hm hdr he hc hok =>
    rename_i t l s' rs'
    have hn : ∀ s₂ rs₂, ¬ TStep (C.ts t).1 (C.ts t).2 none s₂ rs₂ :=
      fun _ _ h => tstep_tau_excl h hs
    have hkeep := taus_keep hpath hn
    have hst' : OStep .tso N d.ocfg ⟨upd d.ocfg.ts t (s', rs'), l.updH d.ocfg.mem, d.ocfg.buf⟩ := by
      refine .drained ht (by rw [hkeep]; exact hs) hm hdr (by rw [hbuf]; exact he)
        (by rw [hmem]; exact hc) (by rw [hmem]; exact hok)
    obtain ⟨d', hd', hp'⟩ := cov_of_step hcl hd hst'
    refine ⟨d', hd', star_trans ?_ hp'⟩
    have := taus_lift hpath hn (s', rs') (l.updH C.mem) C.buf
    rw [hmem, hbuf]; exact this
  | flush ht hb hp hmod =>
    rename_i t pre e post
    have hst' : OStep .tso N d.ocfg
        ⟨d.ocfg.ts, e.apply d.ocfg.mem, upd d.ocfg.buf t (pre ++ post)⟩ :=
      .flush ht (by rw [hbuf]; exact hb) hp hmod
    obtain ⟨d', hd', hp'⟩ := cov_of_step hcl hd hst'
    refine ⟨d', hd', star_trans ?_ hp'⟩
    have := taus_lift_mb hpath (e.apply C.mem) (upd C.buf t (pre ++ post))
    rw [hmem, hbuf]; exact this

/-- **The closed set covers every TSO-reachable configuration.** -/
theorem fused_reach {N : Nat} {S : List CSt} (hcl : closedB N S = true) {C C' : OCfg}
    (h : Csl.OReach .tso N C C') (hc : Cov N S C) : Cov N S C' := by
  induction h with
  | refl => exact hc
  | step h _ ih => exact ih (cov_step hcl hc h)

/-- A finished configuration has no silent path out of it. -/
theorem taus_done {N : Nat} {C D : OCfg} (h : Star (TauStep N) C D)
    (hfin : ∀ t < N, (C.ts t).1 = .skip) : D = C := by
  cases h with
  | refl => rfl
  | step h _ =>
    obtain ⟨t, ht, s', rs', hs, -⟩ := h
    rw [hfin t ht] at hs
    cases hs

/-! ## Exploration only adds successors -/

theorem fold_new_sub (l : List CSt) : ∀ (acc : List CSt × HTree) (y : CSt),
    y ∈ (l.foldl (fun (acc : List CSt × HTree) y =>
      if acc.2.memB y then acc else (y :: acc.1, acc.2.ins y.hash y)) acc).1 →
      y ∈ acc.1 ∨ y ∈ l := by
  induction l with
  | nil => intro acc y h; exact Or.inl h
  | cons z l ih =>
    intro acc y h
    rcases ih _ y h with h | h
    · simp only at h
      split at h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Every explored configuration satisfies any property that holds of the start and is kept by
the successors. -/
theorem explore_inv (succ : CSt → List CSt) (P : CSt → Prop)
    (hstep : ∀ x, P x → ∀ y ∈ succ x, P y) :
    ∀ (f : Nat) (st : List CSt) (T : HTree) (vis : List CSt), (∀ x ∈ st, P x) → (∀ x ∈ vis, P x) →
      ∀ y ∈ explore succ f st T vis, P y
  | 0, _, _, _, _, hv => hv
  | _ + 1, [], _, _, _, hv => hv
  | f + 1, x :: st, T, vis, hs, hv => by
    simp only [explore]
    have hx := hs x (List.mem_cons_self ..)
    have hnew : ∀ y ∈ ((succ x).foldl (fun (acc : List CSt × HTree) y =>
        if acc.2.memB y then acc else (y :: acc.1, acc.2.ins y.hash y)) ([], T)).1, P y := by
      intro y hy
      rcases fold_new_sub _ _ y hy with h | h
      · simp at h
      · exact hstep x hx y h
    apply explore_inv succ P hstep f
    · intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact hnew y h
      · exact hs y (List.mem_cons_of_mem _ h)
    · intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact hnew y h
      · exact hv y h

/-- **Every explored SC configuration is SC-reachable.** -/
theorem scStates_reach {N fuel : Nat} {c0 : CSt} {e : CSt} (he : e ∈ scStates N fuel c0) :
    Csl.ScReach N c0.cfg e.cfg := by
  have h0 : Csl.ScReach N c0.cfg (normAll N tauFuel c0).cfg :=
    normAll_sc tauFuel (List.range N) (fun t ht => List.mem_range.mp ht) c0
  refine explore_inv (fscSucc N) (fun x => Csl.ScReach N c0.cfg x.cfg) ?_ fuel _ _ _
    (fun x hx => by simp at hx; subst hx; exact h0)
    (fun x hx => by simp at hx; subst hx; exact h0) e he
  intro x hx y hy
  simp only [fscSucc, List.mem_flatMap, List.mem_range, List.mem_map] at hy
  obtain ⟨t, ht, z, hz, rfl⟩ := hy
  exact star_trans hx (.step (scStepT_sound ht hz) (tauNF_sc ht tauFuel z))

/-! ## The checks -/

theorem toO_ocfg {c : CSt} (h : c.buf.all List.isEmpty = true) : c.cfg.toO = c.ocfg := by
  simp only [Csl.Cfg.toO, CSt.cfg, CSt.ocfg]
  congr 1
  funext t
  simp only [List.all_eq_true, List.isEmpty_iff] at h
  simp only [List.getD_eq_getElem?_getD]
  cases ht : c.buf[t]? with
  | none => rfl
  | some b => simpa using (h b (List.mem_of_getElem? ht)).symm

theorem done_drained {N : Nat} {d : CSt} {C : OCfg} (he : d.ocfg = C) (hd : C.Drained)
    (hfin : ∀ t < N, (C.ts t).1 = .skip) : d.doneB N = true ∧ d.drainedB = true := by
  subst he
  constructor
  · simp only [CSt.doneB, List.all_eq_true, List.mem_range]
    intro t ht
    have := hfin t ht
    simp only [CSt.ocfg] at this
    rw [this]; rfl
  · simp only [CSt.drainedB, List.all_eq_true, List.isEmpty_iff]
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have := hd i
    simp only [CSt.ocfg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] at this
    exact this

/-- The reachable finished, drained TSO configurations are elements of the closed set. -/
theorem final_mem {N : Nat} {S : List CSt} (hcl : closedB N S = true) {c0 : CSt}
    (h0 : normAll N tauFuel c0 ∈ S) (hb : c0.buf.all List.isEmpty = true) {C : OCfg}
    (hr : Csl.OReach .tso N c0.cfg.toO C) (hfin : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ d ∈ S, d.ocfg = C := by
  rw [toO_ocfg hb] at hr
  have hc : Cov N S c0.ocfg :=
    ⟨_, h0, normAll_tau tauFuel (List.range N) (fun t ht => List.mem_range.mp ht) c0⟩
  obtain ⟨d, hd, hp⟩ := fused_reach hcl hr hc
  exact ⟨d, hd, taus_done hp hfin⟩

/-- **The TSO final-state check is sound.** -/
theorem tsoCheck_sound {N fuel : Nat} {c0 : CSt} {P : CSt → Bool} (h : tsoCheck N fuel c0 P = true)
    {C : OCfg} (hr : Csl.OReach .tso N c0.cfg.toO C) (hd : C.Drained)
    (hfin : ∀ t < N, (C.ts t).1 = .skip) : ∃ d, P d = true ∧ d.ocfg = C := by
  simp only [tsoCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hcl, h0⟩, hb⟩, hP⟩ := h
  rw [List.all_eq_true] at hP
  obtain ⟨d, hd', he⟩ := final_mem hcl (memB_ofList h0) hb hr hfin
  obtain ⟨h1, h2⟩ := done_drained he hd hfin
  have := hP d hd'
  simp only [h1, h2, Bool.and_self, Bool.not_true, Bool.false_or] at this
  exact ⟨d, this, he⟩

/-- **The robustness check is sound**: every finished, drained TSO configuration is a finished
SC configuration with the same threads and memory. -/
theorem robustB_sound {N fT fS : Nat} {c0 : CSt} (h : robustB N fT fS c0 = true) {C : OCfg}
    (hr : Csl.OReach .tso N c0.cfg.toO C) (hd : C.Drained) (hfin : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ C' : Cfg, Csl.ScReach N c0.cfg C' ∧ C'.ts = C.ts ∧ C'.mem = C.mem := by
  simp only [robustB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hcl, h0⟩, hb⟩, hP⟩ := h
  rw [List.all_eq_true] at hP
  obtain ⟨d, hd', rfl⟩ := final_mem hcl (memB_ofList h0) hb hr hfin
  obtain ⟨h1, h2⟩ := done_drained rfl hd hfin
  have := hP d hd'
  simp only [h1, h2, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
    List.mem_filter] at this
  obtain ⟨e, ⟨he, -⟩, hs⟩ := this
  obtain ⟨hts, hmem⟩ := sameFinal_eq hs
  refine ⟨e.cfg, scStates_reach he, ?_, ?_⟩
  · simp only [CSt.cfg, CSt.ocfg]; funext t; simp only [CSt.th, hts]
  · simp only [CSt.cfg, CSt.ocfg, hmem]

end Silmaril.Proofs.X86.Concurrency.Cir.Robust

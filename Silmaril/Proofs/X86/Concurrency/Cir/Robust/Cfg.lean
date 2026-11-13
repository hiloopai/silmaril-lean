module

public import Silmaril.Proofs.X86.Concurrency.Cir.Robust.Step

/-!
# The explorer: concrete configurations and machine steps

* `CSt.beq_eq`, `sameFinal_eq`: the Boolean equalities are equalities;
* `th_setTh`, `ocfg_setTh`: concrete updates are `Csl.upd`;
* `HTree.mem_elems`, `memB_ofList`: a hashed lookup finds an element of the list;
* `tsoStepT_complete`: every TSO step (`Csl.OStep .tso`) from a well-shaped configuration is
  enumerated by `tsoStepT`;
* `scStepT_sound`: every enumerated SC step is a `Csl.ScStep`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Robust

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Csl (Heap Ent TStep view newest OStep ScStep upd OCfg Cfg)
open Silmaril.X86.Concurrency.Cir.TvCfg (sbeq_eq)

/-! ## Equality -/

theorem zip_all_eq : ∀ {l l' : List (Stmt × List Word)}, l.length = l'.length →
    (l.zip l').all (fun p => TvCfg.sbeq p.1.1 p.2.1 && p.1.2 == p.2.2) = true → l = l'
  | [], [], _, _ => rfl
  | p :: l, p' :: l', hl, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [zip_all_eq hl h3]
    obtain ⟨a, b⟩ := p; obtain ⟨a', b'⟩ := p'
    simp only at h1 h2
    rw [sbeq_eq h1, h2]
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem CSt.beq_eq {c d : CSt} (h : CSt.beq c d = true) : c = d := by
  simp only [CSt.beq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨ts, mem, buf⟩ := c
  obtain ⟨ts', mem', buf'⟩ := d
  simp only at h1 h2 h3 h4
  rw [zip_all_eq h1 h2, h3, h4]

theorem sameFinal_eq {c d : CSt} (h : CSt.sameFinal c d = true) : c.ts = d.ts ∧ c.mem = d.mem := by
  simp only [CSt.sameFinal, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨zip_all_eq h.1.1 h.1.2, h.2⟩

/-! ## Updates -/

theorem th_setTh (c : CSt) {t : Nat} (ht : t < c.ts.length) (s : Stmt) (rs : Regs) :
    (c.setTh t s rs).th = upd c.th t (s, rs) := by
  funext u
  simp only [CSt.th, CSt.setTh, upd, List.getElem?_set]
  by_cases hu : u = t
  · subst hu; simp [ht, rget_rlist]
  · simp [Ne.symm hu, hu]

theorem bufGet_set (b : List (List Ent)) {t : Nat} (ht : t < b.length) (x : List Ent) :
    (fun u => (b.set t x).getD u []) = upd (fun u => b.getD u []) t x := by
  funext u
  simp only [upd, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hu : u = t
  · subst hu; simp [ht]
  · simp [Ne.symm hu, hu]

theorem th_lt {c : CSt} {t : Nat} {o : Option Lab} {s' : Stmt} {rs' : Regs} {vw : Heap}
    (h : (o, s', rs') ∈ tsucc vw (c.th t).1 (c.th t).2) : t < c.ts.length := by
  by_contra hn
  simp only [CSt.th, List.getElem?_eq_none (Nat.le_of_not_lt hn)] at h
  simp [tsucc] at h

/-! ## Hashed trees -/

theorem find_elems : ∀ {T : HTree} {k : Nat} {x : CSt}, x ∈ T.find k → x ∈ T.elems
  | .leaf, _, _, h => by simp [HTree.find] at h
  | .node l k' vs r, k, x, h => by
    simp only [HTree.find] at h
    simp only [HTree.elems, List.mem_append]
    split at h
    · exact Or.inl (Or.inl (find_elems h))
    · split at h
      · exact Or.inr (find_elems h)
      · exact Or.inl (Or.inr h)

theorem ins_elems : ∀ {T : HTree} {k : Nat} {c x : CSt}, x ∈ (T.ins k c).elems →
    x = c ∨ x ∈ T.elems
  | .leaf, _, _, _, h => by simp [HTree.ins, HTree.elems] at h; exact Or.inl h
  | .node l k' vs r, k, c, x, h => by
    simp only [HTree.ins] at h
    split at h
    · simp only [HTree.elems, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · rcases ins_elems h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr h)
    · split at h
      · simp only [HTree.elems, List.mem_append] at h ⊢
        rcases h with (h | h) | h
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inl (Or.inr h))
        · rcases ins_elems h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      · simp only [HTree.elems, List.mem_append, List.mem_cons] at h ⊢
        rcases h with (h | h | h) | h
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inr h))
        · exact Or.inr (Or.inr h)

theorem ofList_elems_aux : ∀ (l : List CSt) (T : HTree) (x : CSt),
    x ∈ (l.foldl (fun T c => T.ins c.hash c) T).elems → x ∈ l ∨ x ∈ T.elems
  | [], T, x, h => Or.inr h
  | c :: l, T, x, h => by
    rcases ofList_elems_aux l _ x h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases ins_elems h with h | h
      · exact Or.inl (h ▸ List.mem_cons_self ..)
      · exact Or.inr h

/-- **A hashed lookup finds an element of the list.** -/
theorem memB_ofList {S : List CSt} {c : CSt} (h : (HTree.ofList S).memB c = true) : c ∈ S := by
  simp only [HTree.memB, List.any_eq_true] at h
  obtain ⟨d, hd, he⟩ := h
  have hd' := find_elems hd
  rcases ofList_elems_aux S .leaf d hd' with h | h
  · rw [CSt.beq_eq he]; exact h
  · simp [HTree.elems] at h

/-! ## TSO steps are enumerated -/

theorem okB_parts {N : Nat} {c : CSt} (h : c.okB N = true) :
    c.ts.length = N ∧ c.buf.length = N ∧ ∀ t < N, noBlk (c.th t).1 = true := by
  simp only [CSt.okB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun t ht => ?_⟩
  have ht' : t < c.ts.length := h1 ▸ ht
  simp only [CSt.th, List.getElem?_eq_getElem ht']
  exact (h3 _ (List.getElem_mem ht')).1

theorem ocfg_eq {c : CSt} {C : OCfg} (h1 : c.th = C.ts) (h2 : memOf c.mem = C.mem)
    (h3 : (fun u => c.buf.getD u []) = C.buf) : c.ocfg = C := by
  obtain ⟨a, b, d⟩ := C
  simp only at h1 h2 h3
  simp only [CSt.ocfg, h1, h2, h3]

/-- **Every TSO step is enumerated.** -/
theorem tsoStepT_complete {N : Nat} {c : CSt} (hok : c.okB N = true) {C' : OCfg}
    (h : OStep .tso N c.ocfg C') : ∃ t < N, ∃ d ∈ tsoStepT c t, d.ocfg = C' := by
  obtain ⟨hl, hb, hnb⟩ := okB_parts hok
  cases h with
  | tau ht hs =>
    rename_i t s' rs'
    have hm := tsucc_complete (vw := view (memOf c.mem) (c.bufT t)) hs (hnb t ht) noneOk.1
    refine ⟨t, ht, c.setTh t s' rs', ?_, ?_⟩
    · simp only [tsoStepT, List.mem_append, List.mem_filterMap]
      exact Or.inl ⟨_, hm, rfl⟩
    · exact ocfg_eq (th_setTh c (hl ▸ ht) s' rs') rfl rfl
  | buffered ht hs hmem hd hc hrd =>
    rename_i t l s' rs'
    have hm := tsucc_complete (vw := view (memOf c.mem) (c.bufT t)) hs (hnb t ht)
      (fun l' e p hp => by cases e; exact hrd p hp)
    have hnbl := (tsucc_sound hm).2.2 l rfl
    have hmap : mappedB c.mem l = true := (mappedB_iff hnbl).mpr hc
    refine ⟨t, ht, { c.setTh t s' rs' with buf := c.buf.set t (c.bufT t ++ l.ents) }, ?_, ?_⟩
    · simp only [tsoStepT, List.mem_append, List.mem_filterMap]
      refine Or.inl ⟨_, hm, ?_⟩
      simp [hmem, hmap, hd]
    · exact ocfg_eq (th_setTh c (hl ▸ ht) s' rs') rfl (bufGet_set c.buf (hb ▸ ht) _)
  | drained ht hs hmem hd he hc hrd =>
    rename_i t l s' rs'
    have hm := tsucc_complete (vw := view (memOf c.mem) (c.bufT t)) hs (hnb t ht)
      (fun l' e p hp => by
        cases e
        have : c.bufT t = [] := he
        rw [this]; exact hrd p hp)
    have hnbl := (tsucc_sound hm).2.2 l rfl
    have hmap : mappedB c.mem l = true := (mappedB_iff hnbl).mpr hc
    refine ⟨t, ht, { c.setTh t s' rs' with mem := updL c.mem l }, ?_, ?_⟩
    · simp only [tsoStepT, List.mem_append, List.mem_filterMap]
      refine Or.inl ⟨_, hm, ?_⟩
      have : c.bufT t = [] := he
      simp [hmem, hmap, hd, this]
    · exact ocfg_eq (th_setTh c (hl ▸ ht) s' rs') (memOf_updL _ _ hnbl) rfl
  | flush ht hbuf hp hmod =>
    rename_i t pre e post
    have hpre : pre = [] := by
      rcases hmod with h | h
      · cases h
      · exact h
    subst hpre
    have hbt : c.bufT t = e :: post := hbuf
    refine ⟨t, ht, { c with mem := applyE c.mem e, buf := c.buf.set t post }, ?_, ?_⟩
    · simp [tsoStepT, hbt]
    · exact ocfg_eq rfl (memOf_applyE _ _) (bufGet_set c.buf (hb ▸ ht) _)

/-! ## SC steps are sound -/

theorem cfg_eq {c : CSt} {C : Cfg} (h1 : c.th = C.ts) (h2 : memOf c.mem = C.mem) : c.cfg = C := by
  obtain ⟨a, b⟩ := C
  simp only at h1 h2
  simp only [CSt.cfg, h1, h2]

/-- **Every enumerated SC step is an SC step.** -/
theorem scStepT_sound {N : Nat} {c : CSt} {t : Nat} (ht : t < N) {d : CSt} (h : d ∈ scStepT c t) :
    ScStep N c.cfg d.cfg := by
  simp only [scStepT, List.mem_filterMap] at h
  obtain ⟨⟨o, s', rs'⟩, hm, hd⟩ := h
  have hlt := th_lt hm
  obtain ⟨hs, hrd, hnb⟩ := tsucc_sound hm
  cases o with
  | none =>
    simp only [Option.some.injEq] at hd
    subst hd
    have := ScStep.tau (N := N) (C := c.cfg) ht hs
    have e : (c.setTh t s' rs').cfg = ⟨upd c.cfg.ts t (s', rs'), c.cfg.mem⟩ :=
      cfg_eq (th_setTh c hlt s' rs') rfl
    rwa [e]
  | some l =>
    simp only at hd
    split at hd
    · rename_i hc
      simp only [Option.some.injEq] at hd
      subst hd
      simp only [Bool.and_eq_true] at hc
      have hnbl := hnb l rfl
      have := ScStep.lab (N := N) (C := c.cfg) ht hs hc.1 ((mappedB_iff hnbl).mp hc.2)
        (fun p hp => hrd l rfl p hp)
      have e : ({ c.setTh t s' rs' with mem := updL c.mem l } : CSt).cfg =
          ⟨upd c.cfg.ts t (s', rs'), l.updH c.cfg.mem⟩ :=
        cfg_eq (th_setTh c hlt s' rs') (memOf_updL _ _ hnbl)
      rwa [e]
    · cases hd

/-! ## Silent steps -/

/-- A silent step of one of the first `N` threads of a buffered configuration. -/
def TauStep (N : Nat) (C D : OCfg) : Prop :=
  ∃ t < N, ∃ s' rs', TStep (C.ts t).1 (C.ts t).2 none s' rs' ∧
    D = { C with ts := upd C.ts t (s', rs') }

theorem tauNF_tau {N t : Nat} (ht : t < N) : ∀ (f : Nat) (c : CSt),
    Csl.Star (TauStep N) c.ocfg (tauNF t f c).ocfg
  | 0, c => .refl
  | f + 1, c => by
    simp only [tauNF]
    split
    · rename_i s' rs' hts
      have hm : (none, s', rs') ∈ tsucc (memOf c.mem) (c.th t).1 (c.th t).2 := by
        rw [hts]; exact List.mem_singleton_self _
      refine .step ⟨t, ht, s', rs', (tsucc_sound hm).1, ?_⟩ (tauNF_tau ht f _)
      exact (ocfg_eq (C := { c.ocfg with ts := upd c.ocfg.ts t (s', rs') })
        (th_setTh c (th_lt hm) s' rs') rfl rfl)
    · exact .refl

theorem tauNF_sc {N t : Nat} (ht : t < N) : ∀ (f : Nat) (c : CSt),
    Csl.ScReach N c.cfg (tauNF t f c).cfg
  | 0, c => .refl
  | f + 1, c => by
    simp only [tauNF]
    split
    · rename_i s' rs' hts
      have hm : (none, s', rs') ∈ tsucc (memOf c.mem) (c.th t).1 (c.th t).2 := by
        rw [hts]; exact List.mem_singleton_self _
      have h1 := ScStep.tau (N := N) (C := c.cfg) ht (tsucc_sound hm).1
      have e : (c.setTh t s' rs').cfg = ⟨upd c.cfg.ts t (s', rs'), c.cfg.mem⟩ :=
        cfg_eq (th_setTh c (th_lt hm) s' rs') rfl
      rw [← e] at h1
      exact .step h1 (tauNF_sc ht f _)
    · exact .refl

theorem star_trans {α : Type} {r : α → α → Prop} {a b c : α} (h : Csl.Star r a b)
    (h' : Csl.Star r b c) : Csl.Star r a c := by
  induction h with
  | refl => exact h'
  | step h _ ih => exact .step h (ih h')

theorem normAll_tau {N : Nat} (f : Nat) : ∀ (l : List Nat), (∀ t ∈ l, t < N) → ∀ c : CSt,
    Csl.Star (TauStep N) c.ocfg ((l.foldl (fun c t => tauNF t f c) c)).ocfg
  | [], _, _ => .refl
  | t :: l, h, c =>
    star_trans (tauNF_tau (h t (List.mem_cons_self ..)) f c)
      (normAll_tau f l (fun u hu => h u (List.mem_cons_of_mem _ hu)) _)

theorem normAll_sc {N : Nat} (f : Nat) : ∀ (l : List Nat), (∀ t ∈ l, t < N) → ∀ c : CSt,
    Csl.ScReach N c.cfg ((l.foldl (fun c t => tauNF t f c) c)).cfg
  | [], _, _ => .refl
  | t :: l, h, c =>
    star_trans (tauNF_sc (h t (List.mem_cons_self ..)) f c)
      (normAll_sc f l (fun u hu => h u (List.mem_cons_of_mem _ hu)) _)

end Silmaril.Proofs.X86.Concurrency.Cir.Robust

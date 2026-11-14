module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.Buf

/-!
# CSL with release stores: soundness on the TSO store-buffer machine

`XInvR` (the buffered invariant with release records) is preserved by every step of
`OStep .tso` (`xinvR_step`), it holds at a `GInvR` start, and at a drained, finished
configuration it gives every thread's postcondition, the resource invariant, and ghost
conservation (`rel_tso`). Stated in `Silmaril.X86.Concurrency.Cir.Csl.Rel.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab truthy)
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel

theorem upd_self {α : Type} (f : Nat → α) (t : Nat) (x : α) : upd f t x t = x := by
  simp [upd]

theorem upd_ne {α : Type} (f : Nat → α) {t u : Nat} (x : α) (h : u ≠ t) : upd f t x u = f u := by
  simp [upd, h]

section X
variable {I : GProp} {Q : Nat → Bool → Regs → Heap → Heap → Prop} {N : Nat} {G0 : Heap}

/-- The result of a step: some ghost state for the new configuration. -/
def XEx (I : GProp) (Q : Nat → Bool → Regs → Heap → Heap → Prop) (N : Nat) (G0 : Heap)
    (C : OCfg) : Prop :=
  ∃ hs gs hI gI ps ab, XInvR I Q N G0 C hs gs hI gI ps ab

/-! ## Silent steps -/

theorem xinvR_tau {C : OCfg} {hs gs : Nat → Heap} {hI gI : Heap} {ps : Nat → Bool}
    {ab : Nat → ABuf} (X : XInvR I Q N G0 C hs gs hI gI ps ab) {t : Nat} (ht : t < N)
    {s' : Stmt} {rs' : Regs} (st : TStep (C.ts t).1 (C.ts t).2 none s' rs') :
    XInvR I Q N G0 { C with ts := upd C.ts t (s', rs') } hs gs hI gI ps ab := by
  obtain ⟨hab, dT, dP, dI, gT, gP, gI_, leI, iI, vw, aok, pfl, abN, safe, cons⟩ := X
  refine ⟨hab, dT, dP, dI, gT, gP, gI_, leI, iI, vw, aok, pfl, abN, fun u hu => ?_, cons⟩
  by_cases e : u = t
  · subst e; simp only [upd_self]; exact (safeR_unfold (safe u hu)).2.1 _ _ st
  · simp only [upd_ne _ _ e]; exact safe u hu

/-! ## Consequences of the invariant -/

theorem ab_nil {C : OCfg} {hs gs : Nat → Heap} {hI gI : Heap} {ps : Nat → Bool}
    {ab : Nat → ABuf} (X : XInvR I Q N G0 C hs gs hI gI ps ab) {t : Nat} (he : C.buf t = []) :
    ab t = [] := by
  have := X.1 t; rw [he] at this; exact List.map_eq_nil_iff.mp this

/-- Without pending releases, the thread's view agrees with its heap and the invariant's. -/
theorem view_shared {C : OCfg} {hs gs : Nat → Heap} {hI gI : Heap} {ps : Nat → Bool}
    {ab : Nat → ABuf} (X : XInvR I Q N G0 C hs gs hI gI ps ab) {t : Nat} (hp : ps t = false)
    {c : Nat} (hc : (Heap.union (hs t) hI c).isSome) :
    view C.mem (C.buf t) c = Heap.union (hs t) hI c := by
  obtain ⟨hab, -, -, dI, -, -, -, leI, -, vw, aok, pfl, -, -, -⟩ := X
  rw [union_apply]
  cases eh : hs t c with
  | some v => exact vw t c v eh
  | none =>
    rw [Option.none_or]
    rw [union_isSome, eh] at hc
    simp only [Option.isSome_none, Bool.false_or] at hc
    obtain ⟨v, ev⟩ := Option.isSome_iff_exists.mp hc
    have hn : newest (C.buf t) c = none := by
      cases en : newest (C.buf t) c with
      | none => rfl
      | some _ =>
        have := aok_newest (pfl t hp) (aok t) (c := c) (by rw [hab t, en]; rfl)
        rw [eh] at this; cases this
    rw [view_apply, hn, Option.none_or, ev, leI c v ev]

/-! ## Buffered labels -/

theorem xinvR_buffered {C : OCfg} {hs gs : Nat → Heap} {hI gI : Heap} {ps : Nat → Bool}
    {ab : Nat → ABuf} (X : XInvR I Q N G0 C hs gs hI gI ps ab) {t : Nat} (ht : t < N)
    {l : Lab} {s' : Stmt} {rs' : Regs} (st : TStep (C.ts t).1 (C.ts t).2 (some l) s' rs')
    (hd : l.drains = false) (hok : l.okH (view C.mem (C.buf t))) :
    XEx I Q N G0 { C with ts := upd C.ts t (s', rs'), buf := upd C.buf t (C.buf t ++ l.ents) } := by
  have X' := X
  obtain ⟨hab, dT, dP, dI, gT, gP, gI_, leI, iI, vw, aok, pfl, abN, safe, cons⟩ := X
  obtain ⟨-, H⟩ := (safeR_unfold (safe t ht)).2.2 l s' rs' st
  rcases H with ⟨tc, k⟩ | ⟨-, pc, sh⟩ |
    ⟨m, fl, a, sz, v, rfl, -, h', hR, g', gR, d1, eh, d2, eg, k, ob⟩
  · -- local
    have ag : ∀ c, l.Touches c → view C.mem (C.buf t) c = hs t c := fun c tc' => by
      obtain ⟨u, eu⟩ := Option.isSome_iff_exists.mp (tc c tc')
      rw [eu]; exact vw t c u eu
    have k' := k (okH_congr ag hok)
    rw [hd, Bool.not_false, Bool.and_true] at k'
    have domU : ∀ c, (l.updH (hs t) c).isSome = (hs t c).isSome := fun c => by
      rw [updH_apply, or_isSome]
      cases ew : (l.wval c).isSome
      · rfl
      · rw [tc c (wval_touch ew)]; rfl
    have domD : Dom (l.updH (hs t)) (hs t) := fun c e => by rw [← domU]; exact e
    let ab' := upd ab t (ab t ++ l.ents.map fun e => (e, (none : Option PRec)))
    have pH' : pH (ab' t) = pH (ab t) := by
      simp only [ab', upd_self, pH_append, pH_nones, union_empty_right]
    have pG' : pG (ab' t) = pG (ab t) := by
      simp only [ab', upd_self, pG_append, pG_nones, union_empty_right]
    have own : ∀ u, Dom (Heap.union (upd hs t (l.updH (hs t)) u) (pH (ab' u)))
        (Heap.union (hs u) (pH (ab u))) := fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, pH']
        exact dom_union (dom_trans domD (dom_union_left _ _)) (dom_union_right _ _)
      · simp only [ab', upd_ne _ _ e]; exact dom_refl _
    refine ⟨upd hs t (l.updH (hs t)), gs, hI, gI, ps, ab', ?_⟩
    refine ⟨fun u => ?_, fun u w e => disj_of_dom (dT u w e) (own u) (own w), fun u => ?_,
      fun u => disj_of_dom (dI u) (own u) (dom_refl _), fun u w e => ?_, fun u => ?_, fun u => ?_,
      leI, iI, fun u c x ex => ?_, fun u => ?_, fun u hu x hx => ?_, fun u hu => ?_,
      fun u hu => ?_, fun c hc => ?_⟩
    · by_cases e : u = t
      · subst e; simp [ab', upd_self, hab u, Function.comp_def]
      · simp [ab', upd_ne _ _ e, hab u]
    · by_cases e : u = t
      · subst e; rw [upd_self, pH']
        refine ⟨disj_of_dom (dP u).1 domD (dom_refl _), ?_⟩
        simp only [ab', upd_self]; exact pDisj_append_nones _ (dP u).2
      · simp only [ab', upd_ne _ _ e]; exact dP u
    · have g1 := gT u w e
      by_cases e1 : u = t
      · subst e1; rw [pG']; simpa [ab', upd_ne _ _ (Ne.symm e)] using g1
      · by_cases e2 : w = t
        · subst e2; rw [pG']; simpa [ab', upd_ne _ _ e1] using g1
        · simpa [ab', upd_ne _ _ e1, upd_ne _ _ e2] using g1
    · by_cases e : u = t
      · subst e; rw [pG']; exact gP u
      · simp only [ab', upd_ne _ _ e]; exact gP u
    · by_cases e : u = t
      · subst e; rw [pG']; exact gI_ u
      · simp only [ab', upd_ne _ _ e]; exact gI_ u
    · by_cases e : u = t
      · subst e
        simp only [upd_self] at ex ⊢
        rw [view_ents hd]
        rw [updH_apply] at ex
        revert ex
        cases ew : l.wval c with
        | some y => intro ex; simpa using ex
        | none => intro ex; rw [Option.none_or] at ex ⊢; exact vw u c x ex
      · simp only [upd_ne _ _ e] at ex ⊢; exact vw u c x ex
    · by_cases e : u = t
      · subst e
        simp only [ab', upd_self]
        refine aok_append_nones _ (fun c v w hm => ?_) (aok_dom (fun c => (domU c).symm)
          (fun _ => rfl) (aok u))
        rw [domU]; exact tc c (wval_touch (ents_wval hm))
      · simp only [ab', upd_ne _ _ e]; exact aok u
    · by_cases e : u = t
      · subst e
        simp only [ab', upd_self, List.mem_append, List.mem_map] at hx
        rcases hx with hx | ⟨_, -, rfl⟩
        · exact pfl u hu x hx
        · rfl
      · simp only [ab', upd_ne _ _ e] at hx; exact pfl u hu x hx
    · have := abN u hu
      simp only [ab', upd_ne _ _ (show u ≠ t by omega)]; exact this
    · by_cases e : u = t
      · subst e; simp only [upd_self]; exact k'
      · simp only [upd_ne _ _ e]; exact safe u hu
    · rcases cons c hc with h1 | ⟨u, hu, h2⟩
      · exact Or.inl h1
      · refine Or.inr ⟨u, hu, ?_⟩
        by_cases e : u = t
        · subst e; rw [pG']; exact h2
        · simp only [ab', upd_ne _ _ e]; exact h2
  · -- shared (the flag is clear: the label does not drain)
    have hp : ps t = false := by
      rcases pc with pc | pc
      · exact pc
      · rw [hd] at pc; cases pc
    have nr := pfl t hp
    have pH0 : pH (ab t) = Heap.empty := pH_norec nr
    have pG0 : pG (ab t) = Heap.empty := pG_norec nr
    have dtI : Heap.Disjoint (hs t) hI := by
      have := dI t; rw [pH0, union_empty_right] at this; exact this
    have dtgI : Heap.Disjoint (gs t) gI := by
      have := gI_ t; rw [pG0, union_empty_right] at this; exact this
    obtain ⟨tc, wo, ex⟩ := sh hI gI iI dtI dtgI
    have ag : ∀ c, l.Touches c → view C.mem (C.buf t) c = Heap.union (hs t) hI c :=
      fun c tc' => view_shared X' hp (tc c tc')
    obtain ⟨h', hI', g', gI', d1, eq1, d2, eq2, iI', k', sur⟩ := ex (okH_congr ag hok)
    have sur' := sur hd
    -- the new heaps live in the old footprint
    have dom1 : Dom (Heap.union h' hI') (Heap.union (hs t) hI) := fun c e => by
      rw [eq1, updH_apply, or_isSome] at e
      cases ew : (l.wval c).isSome
      · rw [ew, Bool.false_or] at e; exact e
      · exact dom_union_left _ _ c (wo hd c ew)
    have domh' : Dom h' (Heap.union (hs t) hI) := dom_trans (dom_union_left _ _) dom1
    have domI' : Dom hI' (Heap.union (hs t) hI) := dom_trans (dom_union_right _ _) dom1
    have gdom1 : Dom (Heap.union g' gI') (Heap.union (gs t) gI) := by rw [eq2]; exact dom_refl _
    have domg' : Dom g' (Heap.union (gs t) gI) := dom_trans (dom_union_left _ _) gdom1
    have domgI' : Dom gI' (Heap.union (gs t) gI) := dom_trans (dom_union_right _ _) gdom1
    let ab' := upd ab t (ab t ++ l.ents.map fun e => (e, (none : Option PRec)))
    have nr' : ∀ x ∈ ab' t, x.2 = none := by
      intro x hx
      simp only [ab', upd_self, List.mem_append, List.mem_map] at hx
      rcases hx with hx | ⟨_, -, rfl⟩
      · exact nr x hx
      · rfl
    have pH' : pH (ab' t) = Heap.empty := pH_norec nr'
    have pG' : pG (ab' t) = Heap.empty := pG_norec nr'
    -- other threads' resources are disjoint from the old footprint
    have dO : ∀ u, u ≠ t → Heap.Disjoint (Heap.union (hs u) (pH (ab u))) (Heap.union (hs t) hI) :=
      fun u e => by
        refine disjoint_symm (disj_union_left ?_ (disjoint_symm (dI u)))
        have := dT t u (Ne.symm e); rw [pH0, union_empty_right] at this; exact this
    have gO : ∀ u, u ≠ t → Heap.Disjoint (Heap.union (gs u) (pG (ab u))) (Heap.union (gs t) gI) :=
      fun u e => by
        refine disjoint_symm (disj_union_left ?_ (disjoint_symm (gI_ u)))
        have := gT t u (Ne.symm e); rw [pG0, union_empty_right] at this; exact this
    have hIc : ∀ c, (hI' c).isSome → hI' c = hI c := fun c e => by
      have e1 : h' c = none := none_of_disj d1 e
      have e2 : hs t c = none := by
        cases e3 : hs t c with
        | none => rfl
        | some _ => have := sur' c (by rw [e3]; rfl); rw [e1] at this; cases this
      have e4 : l.wval c = none := by
        cases e5 : l.wval c with
        | none => rfl
        | some _ => have := wo hd c (by rw [e5]; rfl); rw [e2] at this; cases this
      have := congrFun eq1 c
      rw [union_apply, e1, Option.none_or, updH_apply, e4, Option.none_or, union_apply, e2,
        Option.none_or] at this
      exact this
    refine ⟨upd hs t h', upd gs t g', hI', gI', ps, ab', ?_⟩
    refine ⟨fun u => ?_, fun u w e => ?_, fun u => ?_, fun u => ?_, fun u w e => ?_, fun u => ?_,
      fun u => ?_, fun c x ex => ?_, iI', fun u c x ex => ?_, fun u => ?_, fun u hu x hx => ?_,
      fun u hu => ?_, fun u hu => ?_, fun c hc => ?_⟩
    · by_cases e : u = t
      · subst e; simp [ab', upd_self, hab u, Function.comp_def]
      · simp [ab', upd_ne _ _ e, hab u]
    · by_cases e1 : u = t
      · subst e1
        simp only [upd_self, pH', union_empty_right, upd_ne _ _ (Ne.symm e)]
        simp only [ab', upd_ne _ _ (Ne.symm e)]
        exact disjoint_symm (disj_of_dom (dO w (Ne.symm e)) (dom_refl _) domh')
      · by_cases e2 : w = t
        · subst e2
          simp only [upd_self, pH', union_empty_right, upd_ne _ _ e1]
          simp only [ab', upd_ne _ _ e1]
          exact disj_of_dom (dO u e1) (dom_refl _) domh'
        · simpa [ab', upd_ne _ _ e1, upd_ne _ _ e2] using dT u w e
    · by_cases e : u = t
      · subst e; rw [upd_self, pH']
        refine ⟨disjoint_empty_right _, ?_⟩
        simp only [ab', upd_self]; exact pDisj_append_nones _ (dP u).2
      · simp only [ab', upd_ne _ _ e]; exact dP u
    · by_cases e : u = t
      · subst e; rw [upd_self, pH', union_empty_right]; exact d1
      · simp only [ab', upd_ne _ _ e]; exact disj_of_dom (dO u e) (dom_refl _) domI'
    · by_cases e1 : u = t
      · subst e1
        simp only [upd_self, pG', union_empty_right, upd_ne _ _ (Ne.symm e)]
        simp only [ab', upd_ne _ _ (Ne.symm e)]
        exact disjoint_symm (disj_of_dom (gO w (Ne.symm e)) (dom_refl _) domg')
      · by_cases e2 : w = t
        · subst e2
          simp only [upd_self, pG', union_empty_right, upd_ne _ _ e1]
          simp only [ab', upd_ne _ _ e1]
          exact disj_of_dom (gO u e1) (dom_refl _) domg'
        · simpa [ab', upd_ne _ _ e1, upd_ne _ _ e2] using gT u w e
    · by_cases e : u = t
      · subst e; rw [upd_self, pG']; exact disjoint_empty_right _
      · simp only [ab', upd_ne _ _ e]; exact gP u
    · by_cases e : u = t
      · subst e; rw [upd_self, pG', union_empty_right]; exact d2
      · simp only [ab', upd_ne _ _ e]; exact disj_of_dom (gO u e) (dom_refl _) domgI'
    · rw [hIc c (by rw [ex]; rfl)] at ex; exact leI c x ex
    · by_cases e : u = t
      · subst e
        simp only [upd_self] at ex ⊢
        rw [view_ents hd]
        have p1 := congrFun eq1 c
        rw [union_apply, ex, updH_apply] at p1
        revert p1
        cases ew : l.wval c with
        | some y => intro p1; simpa using p1.symm
        | none =>
          intro p1
          rw [Option.none_or] at p1 ⊢
          have hc : (Heap.union (hs u) hI c).isSome := by rw [← p1]; rfl
          rw [view_shared X' hp hc, ← p1]; rfl
      · simp only [upd_ne _ _ e] at ex ⊢; exact vw u c x ex
    · by_cases e : u = t
      · subst e
        simp only [ab', upd_self, upd_self]
        refine aok_append_nones _ (fun c v w hm => sur' c (wo hd c (ents_wval hm))) ?_
        exact aok_grow sur' nr (aok u)
      · simp only [ab', upd_ne _ _ e]; exact aok u
    · by_cases e : u = t
      · subst e; exact nr' x hx
      · simp only [ab', upd_ne _ _ e] at hx; exact pfl u hu x hx
    · simp only [ab', upd_ne _ _ (show u ≠ t by omega)]; exact abN u hu
    · by_cases e : u = t
      · subst e; simp only [upd_self, hp]; exact k'
      · simp only [upd_ne _ _ e]; exact safe u hu
    · rcases cons c hc with h1 | ⟨u, hu, h2⟩
      · have : (Heap.union g' gI' c).isSome := by
          rw [eq2, union_isSome, h1, Bool.or_true]
        rw [union_isSome] at this
        cases e1 : (gI' c).isSome
        · rw [e1, Bool.or_false] at this
          exact Or.inr ⟨t, ht, Or.inl (by rw [upd_self]; exact this)⟩
        · exact Or.inl rfl
      · by_cases e : u = t
        · subst e
          rw [pG0] at h2
          rcases h2 with h2 | h2
          · have : (Heap.union g' gI' c).isSome := by
              rw [eq2, union_isSome, h2]; rfl
            rw [union_isSome] at this
            cases e1 : (gI' c).isSome
            · rw [e1, Bool.or_false] at this
              exact Or.inr ⟨u, hu, Or.inl (by rw [upd_self]; exact this)⟩
            · exact Or.inl rfl
          · cases h2
        · exact Or.inr ⟨u, hu, by simpa [ab', upd_ne _ _ e] using h2⟩
  · -- release
    have hRle : Dom hR (hs t) := by rw [eh]; exact dom_union_right _ _
    have h'le : Dom h' (hs t) := by rw [eh]; exact dom_union_left _ _
    have gRle : Dom gR (gs t) := by rw [eg]; exact dom_union_right _ _
    have g'le : Dom g' (gs t) := by rw [eg]; exact dom_union_left _ _
    -- the store's cell is not kept: the obligation, at the current invariant state
    have ha : h' a = none := by
      have dtI : Heap.Disjoint (hs t) hI := disj_of_dom (dI t) (dom_union_left _ _) (dom_refl _)
      have dgI : Heap.Disjoint (gs t) gI := disj_of_dom (gI_ t) (dom_union_left _ _) (dom_refl _)
      obtain ⟨⟨a', v', w', ea, ain⟩, -⟩ := ob hI gI iI dtI dgI
      simp only [Ent.st.injEq] at ea; obtain ⟨rfl, -, -⟩ := ea
      rw [union_isSome] at ain
      cases e : h' a with
      | none => rfl
      | some _ =>
        have h1 : hR a = none := disj_none d1 (by rw [e]; rfl)
        have h2 : hI a = none := disj_none (disj_of_dom dtI h'le (dom_refl _)) (by rw [e]; rfl)
        rw [h1, h2] at ain; cases ain
    let r : PRec := ⟨hR, gR, hs t, gs t⟩
    let ab' := upd ab t (ab t ++ [(Ent.st a v (fl != .wb), some r)])
    have pH' : pH (ab' t) = Heap.union (pH (ab t)) (Heap.union hR Heap.empty) := by
      simp only [ab', upd_self, pH_append]; rfl
    have pG' : pG (ab' t) = Heap.union (pG (ab t)) (Heap.union gR Heap.empty) := by
      simp only [ab', upd_self, pG_append]; rfl
    have own : ∀ u, Dom (Heap.union (upd hs t h' u) (pH (ab' u)))
        (Heap.union (hs u) (pH (ab u))) := fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, pH']
        refine dom_union (dom_trans h'le (dom_union_left _ _))
          (dom_union (dom_union_right _ _) (dom_union (dom_trans hRle (dom_union_left _ _))
            (dom_empty _)))
      · simp only [ab', upd_ne _ _ e]; exact dom_refl _
    have gown : ∀ u, Dom (Heap.union (upd gs t g' u) (pG (ab' u)))
        (Heap.union (gs u) (pG (ab u))) := fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self, pG']
        refine dom_union (dom_trans g'le (dom_union_left _ _))
          (dom_union (dom_union_right _ _) (dom_union (dom_trans gRle (dom_union_left _ _))
            (dom_empty _)))
      · simp only [ab', upd_ne _ _ e]; exact dom_refl _
    refine ⟨upd hs t h', upd gs t g', hI, gI, upd ps t true, ab', ?_⟩
    refine ⟨fun u => ?_, fun u w e => disj_of_dom (dT u w e) (own u) (own w), fun u => ?_,
      fun u => disj_of_dom (dI u) (own u) (dom_refl _),
      fun u w e => disj_of_dom (gT u w e) (gown u) (gown w), fun u => ?_,
      fun u => disj_of_dom (gI_ u) (gown u) (dom_refl _), leI, iI, fun u c x ex => ?_,
      fun u => ?_, fun u hu x hx => ?_, fun u hu => ?_, fun u hu => ?_, fun c hc => ?_⟩
    · by_cases e : u = t
      · subst e; simp [ab', upd_self, hab u, Lab.ents]
      · simp [ab', upd_ne _ _ e, hab u]
    · by_cases e : u = t
      · subst e; rw [upd_self, pH']
        refine ⟨disj_union_right (disj_of_dom (dP u).1 h'le (dom_refl _))
          (disj_union_right d1 (disjoint_empty_right _)), ?_⟩
        simp only [ab', upd_self]
        exact pDisj_append_rec _ r (dP u).2 (disjoint_symm (disj_of_dom (dP u).1 hRle (dom_refl _)))
          (disjoint_symm (disj_of_dom (gP u) gRle (dom_refl _)))
      · simp only [ab', upd_ne _ _ e]; exact dP u
    · by_cases e : u = t
      · subst e; rw [upd_self, pG']
        exact disj_union_right (disj_of_dom (gP u) g'le (dom_refl _))
          (disj_union_right d2 (disjoint_empty_right _))
      · simp only [ab', upd_ne _ _ e]; exact gP u
    · by_cases e : u = t
      · subst e
        simp only [upd_self] at ex ⊢
        have hca : c ≠ a := fun h => by rw [h, ha] at ex; cases ex
        have ex' : hs u c = some x := by rw [eh, union_apply, ex]; rfl
        rw [view_apply, newest_append]
        simp only [Lab.ents, newest, Ent.val, Ne.symm hca, ite_false, Option.none_or]
        exact vw u c x ex'
      · simp only [upd_ne _ _ e] at ex ⊢; exact vw u c x ex
    · by_cases e : u = t
      · subst e
        simp only [ab', upd_self]
        refine aok_release (aok u) eh eg ha ob (fun c x ex => ?_)
        rw [hab u]
        exact vw u c x (by rw [eh, union_apply, none_of_disj d1 (by rw [ex]; rfl), ex]; rfl)
      · simp only [ab', upd_ne _ _ e]; exact aok u
    · by_cases e : u = t
      · subst e; rw [upd_self] at hu; cases hu
      · simp only [upd_ne _ _ e] at hu; simp only [ab', upd_ne _ _ e] at hx; exact pfl u hu x hx
    · simp only [ab', upd_ne _ _ (show u ≠ t by omega)]; exact abN u hu
    · by_cases e : u = t
      · subst e; simp only [upd_self]; exact k
      · simp only [upd_ne _ _ e]; exact safe u hu
    · rcases cons c hc with h1 | ⟨u, hu, h2⟩
      · exact Or.inl h1
      · refine Or.inr ⟨u, hu, ?_⟩
        by_cases e : u = t
        · subst e
          rw [upd_self, pG']
          rw [eg, union_isSome] at h2
          simp only [union_isSome, Bool.or_eq_true] at h2 ⊢
          rcases h2 with (h2 | h2) | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inr (Or.inl h2))
          · exact Or.inr (Or.inl h2)
        · simp only [ab', upd_ne _ _ e]; exact h2

/-! ## Draining labels -/

theorem updH_le {A M : Heap} (l : Lab) (h : Heap.Le A M) : Heap.Le (l.updH A) (l.updH M) := by
  intro a v e; rw [updH_apply] at e ⊢
  cases e' : l.wval a with
  | none => rw [e', Option.none_or] at e; rw [Option.none_or]; exact h a v e
  | some w => rw [e'] at e; exact e

theorem xinvR_drained {C : OCfg} {hs gs : Nat → Heap} {hI gI : Heap} {ps : Nat → Bool}
    {ab : Nat → ABuf} (X : XInvR I Q N G0 C hs gs hI gI ps ab) {t : Nat} (ht : t < N)
    {l : Lab} {s' : Stmt} {rs' : Regs} (st : TStep (C.ts t).1 (C.ts t).2 (some l) s' rs')
    (hd : l.drains = true) (he : C.buf t = []) (hok : l.okH C.mem) :
    XEx I Q N G0 { C with ts := upd C.ts t (s', rs'), mem := l.updH C.mem } := by
  have abt := ab_nil X he
  obtain ⟨hab, dT, dP, dI, gT, gP, gI_, leI, iI, vw, aok, pfl, abN, safe, cons⟩ := X
  have pH0 : pH (ab t) = Heap.empty := by rw [abt]; rfl
  have pG0 : pG (ab t) = Heap.empty := by rw [abt]; rfl
  have vt : ∀ c x, hs t c = some x → C.mem c = some x := fun c x ex => by
    have := vw t c x ex; rwa [he, view_nil] at this
  have dtI : Heap.Disjoint (hs t) hI := by
    have := dI t; rw [pH0, union_empty_right] at this; exact this
  have dtgI : Heap.Disjoint (gs t) gI := by
    have := gI_ t; rw [pG0, union_empty_right] at this; exact this
  have dO : ∀ u, u ≠ t → Heap.Disjoint (Heap.union (hs u) (pH (ab u))) (Heap.union (hs t) hI) :=
    fun u e => by
      refine disjoint_symm (disj_union_left ?_ (disjoint_symm (dI u)))
      have := dT t u (Ne.symm e); rw [pH0, union_empty_right] at this; exact this
  have gO : ∀ u, u ≠ t → Heap.Disjoint (Heap.union (gs u) (pG (ab u))) (Heap.union (gs t) gI) :=
    fun u e => by
      refine disjoint_symm (disj_union_left ?_ (disjoint_symm (gI_ u)))
      have := gT t u (Ne.symm e); rw [pG0, union_empty_right] at this; exact this
  -- memory changes only on the cells the label writes, all in `hs t ∪ hI`
  have memO : ∀ (W : Heap), (∀ c, (l.wval c).isSome → (W c).isSome) → ∀ u, u ≠ t →
      Heap.Disjoint (Heap.union (hs u) (pH (ab u))) W →
      ∀ c, (Heap.union (hs u) (pH (ab u)) c).isSome → l.updH C.mem c = C.mem c := by
    intro W hW u e dW c hc
    rw [updH_apply]
    cases ew : l.wval c with
    | none => rfl
    | some _ => have := hW c (by rw [ew]; rfl); rw [disj_none dW hc] at this; cases this
  obtain ⟨-, H⟩ := (safeR_unfold (safe t ht)).2.2 l s' rs' st
  rcases H with ⟨tc, k⟩ | ⟨-, -, sh⟩ | ⟨m, fl, a, sz, v, rfl, -⟩
  · -- local
    have ag : ∀ c, l.Touches c → hs t c = C.mem c := fun c tc' => by
      obtain ⟨u, eu⟩ := Option.isSome_iff_exists.mp (tc c tc')
      rw [eu, vt c u eu]
    have k' := k (okH_congr (fun c tc' => (ag c tc').symm) hok)
    rw [hd, Bool.not_true, Bool.and_false] at k'
    have hW : ∀ c, (l.wval c).isSome → (hs t c).isSome := fun c e => tc c (wval_touch e)
    have domU : ∀ c, (l.updH (hs t) c).isSome = (hs t c).isSome := fun c => by
      rw [updH_apply, or_isSome]
      cases ew : (l.wval c).isSome
      · rfl
      · rw [hW c ew]; rfl
    have domD : Dom (l.updH (hs t)) (hs t) := fun c e => by rw [← domU]; exact e
    have own : ∀ u, Dom (Heap.union (upd hs t (l.updH (hs t)) u) (pH (ab u)))
        (Heap.union (hs u) (pH (ab u))) := fun u => by
      by_cases e : u = t
      · subst e; rw [upd_self]
        exact dom_union (dom_trans domD (dom_union_left _ _)) (dom_union_right _ _)
      · rw [upd_ne _ _ e]; exact dom_refl _
    have memU : ∀ u, u ≠ t → ∀ c, (Heap.union (hs u) (pH (ab u)) c).isSome →
        l.updH C.mem c = C.mem c := fun u e =>
      memO (hs t) hW u e (disj_of_dom (dO u e) (dom_refl _) (dom_union_left _ _))
    refine ⟨upd hs t (l.updH (hs t)), gs, hI, gI, upd ps t false, ab, ?_⟩
    refine ⟨hab, fun u w e => disj_of_dom (dT u w e) (own u) (own w), fun u => ?_,
      fun u => disj_of_dom (dI u) (own u) (dom_refl _), gT, gP, gI_, fun c x ex => ?_, iI,
      fun u c x ex => ?_, fun u => ?_, fun u hu x hx => ?_, abN, fun u hu => ?_, cons⟩
    · by_cases e : u = t
      · subst e; rw [upd_self]; exact ⟨disj_of_dom (dP u).1 domD (dom_refl _), (dP u).2⟩
      · rw [upd_ne _ _ e]; exact dP u
    · show l.updH C.mem c = some x
      rw [updH_apply]
      cases ew : l.wval c with
      | none => rw [Option.none_or]; exact leI c x ex
      | some _ =>
        have := hW c (by rw [ew]; rfl)
        rw [disj_none dtI this] at ex; cases ex
    · by_cases e : u = t
      · subst e
        simp only [upd_self] at ex ⊢
        rw [he, view_nil, updH_apply]
        rw [updH_apply] at ex
        revert ex
        cases ew : l.wval c with
        | some y => intro ex; simpa using ex
        | none => intro ex; rw [Option.none_or] at ex ⊢; exact vt c x ex
      · simp only [upd_ne _ _ e] at ex ⊢
        rw [view_apply, memU u e c (by rw [union_isSome, ex]; rfl)]
        exact vw u c x ex
    · by_cases e : u = t
      · subst e; rw [upd_self, abt]; trivial
      · rw [upd_ne _ _ e]
        exact aok_mem (fun c hc => (memU u e c (by rw [union_isSome, hc, Bool.or_true])).symm)
          (aok u)
    · by_cases e : u = t
      · subst e; rw [abt] at hx; cases hx
      · rw [upd_ne _ _ e] at hu; exact pfl u hu x hx
    · by_cases e : u = t
      · subst e; simp only [upd_self]; exact k'
      · simp only [upd_ne _ _ e]; exact safe u hu
  · -- shared
    obtain ⟨tc, -, ex⟩ := sh hI gI iI dtI dtgI
    have leU : Heap.Le (Heap.union (hs t) hI) C.mem := le_union (fun c x e => vt c x e) leI
    have ag : ∀ c, l.Touches c → Heap.union (hs t) hI c = C.mem c := fun c tc' => by
      obtain ⟨u, eu⟩ := Option.isSome_iff_exists.mp (tc c tc')
      rw [eu, leU c u eu]
    obtain ⟨h', hI', g', gI', d1, eq1, d2, eq2, iI', k', -⟩ :=
      ex (okH_congr (fun c tc' => (ag c tc').symm) hok)
    have hW : ∀ c, (l.wval c).isSome → (Heap.union (hs t) hI c).isSome :=
      fun c e => tc c (wval_touch e)
    have dom1 : Dom (Heap.union h' hI') (Heap.union (hs t) hI) := fun c e => by
      rw [eq1, updH_apply, or_isSome] at e
      cases ew : (l.wval c).isSome
      · rw [ew, Bool.false_or] at e; exact e
      · exact hW c ew
    have domh' : Dom h' (Heap.union (hs t) hI) := dom_trans (dom_union_left _ _) dom1
    have domI' : Dom hI' (Heap.union (hs t) hI) := dom_trans (dom_union_right _ _) dom1
    have gdom1 : Dom (Heap.union g' gI') (Heap.union (gs t) gI) := by rw [eq2]; exact dom_refl _
    have domg' : Dom g' (Heap.union (gs t) gI) := dom_trans (dom_union_left _ _) gdom1
    have domgI' : Dom gI' (Heap.union (gs t) gI) := dom_trans (dom_union_right _ _) gdom1
    have leN : Heap.Le (Heap.union h' hI') (l.updH C.mem) := by rw [eq1]; exact updH_le l leU
    have memU : ∀ u, u ≠ t → ∀ c, (Heap.union (hs u) (pH (ab u)) c).isSome →
        l.updH C.mem c = C.mem c := fun u e => memO _ hW u e (dO u e)
    refine ⟨upd hs t h', upd gs t g', hI', gI', upd ps t false, ab, ?_⟩
    refine ⟨hab, fun u w e => ?_, fun u => ?_, fun u => ?_, fun u w e => ?_, fun u => ?_,
      fun u => ?_, fun c x ex => ?_, iI', fun u c x ex => ?_, fun u => ?_, fun u hu x hx => ?_, abN,
      fun u hu => ?_, fun c hc => ?_⟩
    · by_cases e1 : u = t
      · subst e1
        rw [upd_self, upd_ne _ _ (Ne.symm e), pH0, union_empty_right]
        exact disjoint_symm (disj_of_dom (dO w (Ne.symm e)) (dom_refl _) domh')
      · by_cases e2 : w = t
        · subst e2
          rw [upd_self, upd_ne _ _ e1, pH0, union_empty_right]
          exact disj_of_dom (dO u e1) (dom_refl _) domh'
        · rw [upd_ne _ _ e1, upd_ne _ _ e2]; exact dT u w e
    · by_cases e : u = t
      · subst e; rw [upd_self, pH0]; exact ⟨disjoint_empty_right _, (dP u).2⟩
      · rw [upd_ne _ _ e]; exact dP u
    · by_cases e : u = t
      · subst e; rw [upd_self, pH0, union_empty_right]; exact d1
      · rw [upd_ne _ _ e]; exact disj_of_dom (dO u e) (dom_refl _) domI'
    · by_cases e1 : u = t
      · subst e1
        rw [upd_self, upd_ne _ _ (Ne.symm e), pG0, union_empty_right]
        exact disjoint_symm (disj_of_dom (gO w (Ne.symm e)) (dom_refl _) domg')
      · by_cases e2 : w = t
        · subst e2
          rw [upd_self, upd_ne _ _ e1, pG0, union_empty_right]
          exact disj_of_dom (gO u e1) (dom_refl _) domg'
        · rw [upd_ne _ _ e1, upd_ne _ _ e2]; exact gT u w e
    · by_cases e : u = t
      · subst e; rw [upd_self, pG0]; exact disjoint_empty_right _
      · rw [upd_ne _ _ e]; exact gP u
    · by_cases e : u = t
      · subst e; rw [upd_self, pG0, union_empty_right]; exact d2
      · rw [upd_ne _ _ e]; exact disj_of_dom (gO u e) (dom_refl _) domgI'
    · have e1 : h' c = none := none_of_disj d1 (by rw [ex]; rfl)
      exact leN c x (by rw [union_apply, e1, ex]; rfl)
    · by_cases e : u = t
      · subst e
        simp only [upd_self] at ex ⊢
        rw [he, view_nil]
        exact leN c x (by rw [union_apply, ex]; rfl)
      · simp only [upd_ne _ _ e] at ex ⊢
        rw [view_apply, memU u e c (by rw [union_isSome, ex]; rfl)]
        exact vw u c x ex
    · by_cases e : u = t
      · subst e; rw [abt]; trivial
      · rw [upd_ne _ _ e, upd_ne _ _ e]
        exact aok_mem (fun c hc => (memU u e c (by rw [union_isSome, hc, Bool.or_true])).symm)
          (aok u)
    · by_cases e : u = t
      · subst e; rw [abt] at hx; cases hx
      · rw [upd_ne _ _ e] at hu; exact pfl u hu x hx
    · by_cases e : u = t
      · subst e; simp only [upd_self]; exact k'
      · simp only [upd_ne _ _ e]; exact safe u hu
    · rcases cons c hc with h1 | ⟨u, hu, h2⟩
      · have : (Heap.union g' gI' c).isSome := by
          rw [eq2, union_isSome, h1, Bool.or_true]
        rw [union_isSome] at this
        cases e1 : (gI' c).isSome
        · rw [e1, Bool.or_false] at this
          exact Or.inr ⟨t, ht, Or.inl (by rw [upd_self]; exact this)⟩
        · exact Or.inl rfl
      · by_cases e : u = t
        · subst e
          rw [pG0] at h2
          rcases h2 with h2 | h2
          · have : (Heap.union g' gI' c).isSome := by
              rw [eq2, union_isSome, h2]; rfl
            rw [union_isSome] at this
            cases e1 : (gI' c).isSome
            · rw [e1, Bool.or_false] at this
              exact Or.inr ⟨u, hu, Or.inl (by rw [upd_self]; exact this)⟩
            · exact Or.inl rfl
          · cases h2
        · exact Or.inr ⟨u, hu, by rw [upd_ne _ _ e]; exact h2⟩
  · -- a release store does not drain
    cases hd

/-! ## Flushes (TSO: the oldest entry) -/

theorem xinvR_flush {C : OCfg} {hs gs : Nat → Heap} {hI gI : Heap} {ps : Nat → Bool}
    {ab : Nat → ABuf} (X : XInvR I Q N G0 C hs gs hI gI ps ab) {t : Nat} {e : Ent}
    {post : List Ent} (hb : C.buf t = e :: post) :
    XEx I Q N G0 { C with mem := e.apply C.mem, buf := upd C.buf t post } := by
  obtain ⟨hab, dT, dP, dI, gT, gP, gI_, leI, iI, vw, aok, pfl, abN, safe, cons⟩ := X
  obtain ⟨x, abp, eab, ex1, ex2⟩ :
      ∃ x abp, ab t = x :: abp ∧ x.1 = e ∧ abp.map Prod.fst = post := by
    have := hab t; rw [hb] at this
    cases eab : ab t with
    | nil => rw [eab] at this; cases this
    | cons x abp =>
      rw [eab, List.map_cons, List.cons.injEq] at this
      exact ⟨x, abp, rfl, this.1, this.2⟩
  obtain ⟨e0, r⟩ := x
  simp only at ex1; subst ex1
  have tN : t < N := by
    by_contra h
    have := abN t (by omega); rw [eab] at this; cases this
  let ab' := upd ab t abp
  have vwt : ∀ c x, hs t c = some x → view (e0.apply C.mem) post c = some x := fun c x ex => by
    have := vw t c x ex; rwa [hb, view_cons] at this
  -- the cell the entry writes is the thread's or held by one of its releases
  cases r with
  | none =>
    obtain ⟨h1, h2⟩ : _ ∧ AOk I (hs t) (gs t) (e0.apply C.mem) abp := by
      have := aok t; rw [eab] at this; exact this
    have pHe : pH (ab t) = pH abp := by rw [eab]; rfl
    have pGe : pG (ab t) = pG abp := by rw [eab]; rfl
    -- memory changes only inside `own t`
    have memO : ∀ c, (Heap.union (hs t) (pH (ab t)) c).isSome = false →
        e0.apply C.mem c = C.mem c := fun c hc => by
      cases e0 with
      | bar => rfl
      | st c0 v0 w0 =>
        rw [apply_st]
        by_cases h : c = c0
        · subst h
          rw [union_isSome, pHe] at hc
          rcases h1 with h1 | h1 <;> simp_all
        · simp [h]
    have memU : ∀ u, u ≠ t → ∀ c, (Heap.union (hs u) (pH (ab u)) c).isSome →
        e0.apply C.mem c = C.mem c := fun u ne c hc => memO c (by
          cases e' : (Heap.union (hs t) (pH (ab t)) c).isSome
          · rfl
          · rw [disj_none (dT t u (Ne.symm ne)) e'] at hc; cases hc)
    refine ⟨hs, gs, hI, gI, ps, ab', ?_⟩
    refine ⟨fun u => ?_, fun u w ne => ?_, fun u => ?_, fun u => ?_, fun u w ne => ?_, fun u => ?_,
      fun u => ?_, fun c x ex => ?_, iI, fun u c x ex => ?_, fun u => ?_, fun u hu x hx => ?_,
      fun u hu => ?_, safe, fun c hc => ?_⟩
    · by_cases ne : u = t
      · subst ne; simp [ab', upd_self, ex2]
      · simp [ab', upd_ne _ _ ne, hab u]
    · have := dT u w ne
      by_cases e1 : u = t
      · subst e1; simpa [ab', upd_self, upd_ne _ _ (Ne.symm ne), pHe] using this
      · by_cases e2 : w = t
        · subst e2; simpa [ab', upd_self, upd_ne _ _ e1, pHe] using this
        · simpa [ab', upd_ne _ _ e1, upd_ne _ _ e2] using this
    · by_cases ne : u = t
      · subst ne; have := dP u; rw [eab] at this; simp only [ab', upd_self]; exact ⟨by
          rw [← pHe, eab]; exact this.1, this.2⟩
      · simp only [ab', upd_ne _ _ ne]; exact dP u
    · by_cases ne : u = t
      · subst ne; simp only [ab', upd_self]; rw [← pHe]; exact dI u
      · simp only [ab', upd_ne _ _ ne]; exact dI u
    · have := gT u w ne
      by_cases e1 : u = t
      · subst e1; simpa [ab', upd_self, upd_ne _ _ (Ne.symm ne), pGe] using this
      · by_cases e2 : w = t
        · subst e2; simpa [ab', upd_self, upd_ne _ _ e1, pGe] using this
        · simpa [ab', upd_ne _ _ e1, upd_ne _ _ e2] using this
    · by_cases ne : u = t
      · subst ne; simp only [ab', upd_self]; rw [← pGe]; exact gP u
      · simp only [ab', upd_ne _ _ ne]; exact gP u
    · by_cases ne : u = t
      · subst ne; simp only [ab', upd_self]; rw [← pGe]; exact gI_ u
      · simp only [ab', upd_ne _ _ ne]; exact gI_ u
    · show e0.apply C.mem c = some x
      rw [memO c (by
        cases e' : (Heap.union (hs t) (pH (ab t)) c).isSome
        · rfl
        · rw [disj_none (dI t) e'] at ex; cases ex)]
      exact leI c x ex
    · by_cases ne : u = t
      · subst ne; simp only [upd_self]; exact vwt c x ex
      · simp only [upd_ne _ _ ne]
        rw [view_apply, memU u ne c (by rw [union_isSome, ex]; rfl)]; exact vw u c x ex
    · by_cases ne : u = t
      · subst ne; simp only [ab', upd_self]; exact h2
      · simp only [ab', upd_ne _ _ ne]
        exact aok_mem (fun c hc => (memU u ne c (by rw [union_isSome, hc, Bool.or_true])).symm)
          (aok u)
    · by_cases ne : u = t
      · subst ne; simp only [ab', upd_self] at hx
        exact pfl u hu x (by rw [eab]; exact List.mem_cons_of_mem _ hx)
      · simp only [ab', upd_ne _ _ ne] at hx; exact pfl u hu x hx
    · simp only [ab', upd_ne _ _ (show u ≠ t by omega)]; exact abN u hu
    · rcases cons c hc with h | ⟨u, hu, h⟩
      · exact Or.inl h
      · refine Or.inr ⟨u, hu, ?_⟩
        by_cases ne : u = t
        · subst ne; simp only [ab', upd_self]; rw [← pGe]; exact h
        · simp only [ab', upd_ne _ _ ne]; exact h
  | some r =>
    obtain ⟨⟨a, v, w, rfl, ha, hpa⟩, ob, hle, hH, hG, h6⟩ : _ ∧ _ ∧ Heap.Le r.hR C.mem ∧ _ ∧ _ ∧
        AOk I (hs t) (gs t) (Ent.apply C.mem e0) abp := by
      have := aok t; rw [eab] at this; exact this
    have pHe : pH (ab t) = Heap.union r.hR (pH abp) := by rw [eab]; rfl
    have pGe : pG (ab t) = Heap.union r.gR (pG abp) := by rw [eab]; rfl
    have pd : PDisj (ab t) := (dP t).2
    rw [eab] at pd
    obtain ⟨pd1, pd2, pd3⟩ := pd
    obtain ⟨⟨a', v', w', ea, ain⟩, iI'⟩ := ob hI gI iI
      (disj_of_dom (dI t) (by rw [eab]; exact hH) (dom_refl _))
      (disj_of_dom (gI_ t) (by rw [eab]; exact hG) (dom_refl _))
    simp only [Ent.st.injEq] at ea; obtain ⟨rfl, rfl, rfl⟩ := ea
    let hI' := (Ent.st a v w).apply (Heap.union r.hR hI)
    have domI' : Dom hI' (Heap.union r.hR hI) := dom_apply ain
    -- `own t` without the record, and with it
    have ownt : Dom (Heap.union (hs t) (pH abp)) (Heap.union (hs t) (pH (ab t))) := by
      rw [pHe]
      exact dom_union (dom_union_left _ _)
        (dom_trans (dom_union_right r.hR _) (dom_union_right _ _))
    have gownt : Dom (Heap.union (gs t) (pG abp)) (Heap.union (gs t) (pG (ab t))) := by
      rw [pGe]
      exact dom_union (dom_union_left _ _)
        (dom_trans (dom_union_right r.gR _) (dom_union_right _ _))
    have hRt : Dom r.hR (Heap.union (hs t) (pH (ab t))) := by
      rw [pHe]; exact dom_trans (dom_union_left _ _) (dom_union_right _ _)
    have gRt : Dom r.gR (Heap.union (gs t) (pG (ab t))) := by
      rw [pGe]; exact dom_trans (dom_union_left _ _) (dom_union_right _ _)
    have own : ∀ u, Dom (Heap.union (hs u) (pH (ab' u))) (Heap.union (hs u) (pH (ab u))) :=
      fun u => by
        by_cases ne : u = t
        · subst ne; simp only [ab', upd_self]; exact ownt
        · simp only [ab', upd_ne _ _ ne]; exact dom_refl _
    have gown : ∀ u, Dom (Heap.union (gs u) (pG (ab' u))) (Heap.union (gs u) (pG (ab u))) :=
      fun u => by
        by_cases ne : u = t
        · subst ne; simp only [ab', upd_self]; exact gownt
        · simp only [ab', upd_ne _ _ ne]; exact dom_refl _
    -- every remaining resource is disjoint from the new invariant heap
    have dnew : ∀ u, Heap.Disjoint (Heap.union (hs u) (pH (ab' u))) (Heap.union r.hR hI) := by
      intro u
      by_cases ne : u = t
      · subst ne
        simp only [ab', upd_self]
        refine disj_union_right ?_ (disj_of_dom (dI u) ownt (dom_refl _))
        refine disj_union_left (disj_of_dom (dP u).1 (dom_refl _) ?_) (disjoint_symm pd1)
        rw [pHe]; exact dom_union_left _ _
      · simp only [ab', upd_ne _ _ ne]
        exact disj_union_right (disj_of_dom (dT u t ne) (dom_refl _) hRt) (dI u)
    have gnew : ∀ u, Heap.Disjoint (Heap.union (gs u) (pG (ab' u))) (Heap.union r.gR gI) := by
      intro u
      by_cases ne : u = t
      · subst ne
        simp only [ab', upd_self]
        refine disj_union_right ?_ (disj_of_dom (gI_ u) gownt (dom_refl _))
        refine disj_union_left (disj_of_dom (gP u) (dom_refl _) ?_) (disjoint_symm pd2)
        rw [pGe]; exact dom_union_left _ _
      · simp only [ab', upd_ne _ _ ne]
        exact disj_union_right (disj_of_dom (gT u t ne) (dom_refl _) gRt) (gI_ u)
    have memU : ∀ u, ∀ c, (Heap.union (hs u) (pH (ab' u)) c).isSome →
        (Ent.st a v w).apply C.mem c = C.mem c := fun u c hc => by
      rw [apply_st]
      by_cases h : c = a
      · subst h
        rw [disj_none (dnew u) hc] at ain; cases ain
      · simp [h]
    refine ⟨hs, gs, hI', Heap.union r.gR gI, ps, ab', ?_⟩
    refine ⟨fun u => ?_, fun u w ne => disj_of_dom (dT u w ne) (own u) (own w), fun u => ?_,
      fun u => disj_of_dom (dnew u) (dom_refl _) domI',
      fun u w ne => disj_of_dom (gT u w ne) (gown u) (gown w), fun u => ?_, gnew,
      le_apply _ (le_union hle leI), iI', fun u c x ex => ?_, fun u => ?_, fun u hu x hx => ?_,
      fun u hu => ?_, safe, fun c hc => ?_⟩
    · by_cases ne : u = t
      · subst ne; simp [ab', upd_self, ex2]
      · simp [ab', upd_ne _ _ ne, hab u]
    · by_cases ne : u = t
      · subst ne; simp only [ab', upd_self]
        refine ⟨disj_of_dom (dP u).1 (dom_refl _) ?_, pd3⟩
        rw [pHe]; exact dom_union_right _ _
      · simp only [ab', upd_ne _ _ ne]; exact dP u
    · by_cases ne : u = t
      · subst ne; simp only [ab', upd_self]
        refine disj_of_dom (gP u) (dom_refl _) ?_
        rw [pGe]; exact dom_union_right _ _
      · simp only [ab', upd_ne _ _ ne]; exact gP u
    · by_cases ne : u = t
      · subst ne; simp only [upd_self]; exact vwt c x ex
      · simp only [upd_ne _ _ ne]
        rw [view_apply, memU u c (by rw [union_isSome, ex]; rfl)]; exact vw u c x ex
    · by_cases ne : u = t
      · subst ne; simp only [ab', upd_self]; exact h6
      · simp only [ab', upd_ne _ _ ne]
        refine aok_mem (fun c hc => (memU u c ?_).symm) (aok u)
        simp only [ab', upd_ne _ _ ne]; rw [union_isSome, hc, Bool.or_true]
    · by_cases ne : u = t
      · subst ne; simp only [ab', upd_self] at hx
        exact pfl u hu x (by rw [eab]; exact List.mem_cons_of_mem _ hx)
      · simp only [ab', upd_ne _ _ ne] at hx; exact pfl u hu x hx
    · simp only [ab', upd_ne _ _ (show u ≠ t by omega)]; exact abN u hu
    · rcases cons c hc with h | ⟨u, hu, h⟩
      · left; rw [union_isSome, h, Bool.or_true]
      · by_cases ne : u = t
        · subst ne
          rw [pGe, union_isSome] at h
          simp only [Bool.or_eq_true] at h
          rcases h with h | h | h
          · exact Or.inr ⟨u, hu, Or.inl h⟩
          · left; rw [union_isSome, h]; rfl
          · exact Or.inr ⟨u, hu, Or.inr (by simp only [ab', upd_self]; exact h)⟩
        · exact Or.inr ⟨u, hu, by simp only [ab', upd_ne _ _ ne]; exact h⟩

/-! ## Runs -/

theorem xinvR_step {C C' : OCfg} (hX : XEx I Q N G0 C) (hst : OStep .tso N C C') :
    XEx I Q N G0 C' := by
  obtain ⟨hs, gs, hI, gI, ps, ab, X⟩ := hX
  cases hst with
  | tau ht st => exact ⟨hs, gs, hI, gI, ps, ab, xinvR_tau X ht st⟩
  | buffered ht st _ hd _ hok => exact xinvR_buffered X ht st hd hok
  | drained ht st _ hd he _ hok => exact xinvR_drained X ht st hd he hok
  | flush ht hb _ hmod =>
    rcases hmod with h | rfl
    · cases h
    · exact xinvR_flush X hb

theorem xinvR_reach {C C' : OCfg} (h : OReach .tso N C C') (hX : XEx I Q N G0 C) :
    XEx I Q N G0 C' := by
  induction h with
  | refl => exact hX
  | step s _ ih => exact ih (xinvR_step hX s)

theorem xinvR_init {C : Cfg} {hs gs : Nat → Heap} {hI gI : Heap}
    (G : GInvR I Q N C hs gs hI gI)
    (hG0 : ∀ c, (G0 c).isSome → (gI c).isSome ∨ ∃ t < N, (gs t c).isSome) :
    XInvR I Q N G0 C.toO hs gs hI gI (fun _ => false) (fun _ => []) := by
  obtain ⟨d1, d2, g1, g2, l1, l2, iI, safe⟩ := G
  refine ⟨fun _ => rfl, fun t u ne => ?_, fun t => ⟨?_, trivial⟩, fun t => ?_, fun t u ne => ?_,
    fun t => ?_, fun t => ?_, l2, iI, fun t a v e => ?_, fun _ => trivial,
    fun _ _ x hx => (by cases hx), fun _ _ => rfl, safe, fun c hc => ?_⟩
  · simp only [pH, union_empty_right]; exact d1 t u ne
  · simp only [pH]; exact disjoint_empty_right _
  · simp only [pH, union_empty_right]; exact d2 t
  · simp only [pG, union_empty_right]; exact g1 t u ne
  · simp only [pG]; exact disjoint_empty_right _
  · simp only [pG, union_empty_right]; exact g2 t
  · show view C.mem [] a = some v
    rw [view_nil]; exact l1 t a v e
  · rcases hG0 c hc with h | ⟨t, ht, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, Or.inl h⟩

/-- **Soundness of `SafeR` on TSO.** From a `GInvR` start, every finished, drained configuration
of the CIR-native TSO machine satisfies every thread's postcondition and the invariant, with
disjoint heaps inside memory, and no ghost cell of `G0` is lost. -/
theorem rel_tso {C0 : Cfg} {hs gs : Nat → Heap} {hI gI : Heap}
    (G : GInvR I Q N C0 hs gs hI gI)
    (hG0 : ∀ c, (G0 c).isSome → (gI c).isSome ∨ ∃ t < N, (gs t c).isSome)
    {C : OCfg} (hr : OReach .tso N C0.toO C) (hd : C.Drained)
    (hf : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ (hs' gs' : Nat → Heap) (hI' gI' : Heap) (ps' : Nat → Bool),
      (∀ t < N, Q t (ps' t) (C.ts t).2 (hs' t) (gs' t)) ∧ I hI' gI' ∧
      (∀ t, Heap.Le (hs' t) C.mem) ∧ Heap.Le hI' C.mem ∧
      (∀ t u, t ≠ u → Heap.Disjoint (hs' t) (hs' u)) ∧ (∀ t, Heap.Disjoint (hs' t) hI') ∧
      (∀ c, (G0 c).isSome → (gI' c).isSome ∨ ∃ t < N, (gs' t c).isSome) := by
  obtain ⟨hs', gs', hI', gI', ps', ab', X⟩ :=
    xinvR_reach hr ⟨hs, gs, hI, gI, _, _, xinvR_init G hG0⟩
  obtain ⟨hab, dT, dP, dI, -, -, -, leI, iI, vw, -, -, -, safe, cons⟩ := X
  have abE : ∀ t, ab' t = [] := fun t => by
    have := hab t; rw [hd t] at this; exact List.map_eq_nil_iff.mp this
  refine ⟨hs', gs', hI', gI', ps', fun t ht => ?_, iI, fun t c x ex => ?_, leI,
    fun t u ne => ?_, fun t => ?_, fun c hc => ?_⟩
  · have := safeR_skip_inv (by rw [← hf t ht]; exact safe t ht); exact this
  · have := vw t c x ex; rwa [hd t, view_nil] at this
  · have := dT t u ne; rw [abE, abE] at this; simpa [pH, union_empty_right] using this
  · have := dI t; rw [abE] at this; simpa [pH, union_empty_right] using this
  · rcases cons c hc with h | ⟨t, ht, h | h⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, h⟩
    · rw [abE] at h; cases h

/-- **`rel_tso` with the ghost heaps' disjointness**: at a drained, finished state
the threads' ghost heaps are also pairwise disjoint and disjoint from the invariant's. -/
theorem rel_tsoG {C0 : Cfg} {hs gs : Nat → Heap} {hI gI : Heap}
    (G : GInvR I Q N C0 hs gs hI gI)
    (hG0 : ∀ c, (G0 c).isSome → (gI c).isSome ∨ ∃ t < N, (gs t c).isSome)
    {C : OCfg} (hr : OReach .tso N C0.toO C) (hd : C.Drained)
    (hf : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ (hs' gs' : Nat → Heap) (hI' gI' : Heap) (ps' : Nat → Bool),
      (∀ t < N, Q t (ps' t) (C.ts t).2 (hs' t) (gs' t)) ∧ I hI' gI' ∧
      (∀ t, Heap.Le (hs' t) C.mem) ∧ Heap.Le hI' C.mem ∧
      (∀ t u, t ≠ u → Heap.Disjoint (hs' t) (hs' u)) ∧ (∀ t, Heap.Disjoint (hs' t) hI') ∧
      (∀ t u, t ≠ u → Heap.Disjoint (gs' t) (gs' u)) ∧ (∀ t, Heap.Disjoint (gs' t) gI') ∧
      (∀ c, (G0 c).isSome → (gI' c).isSome ∨ ∃ t < N, (gs' t c).isSome) := by
  obtain ⟨hs', gs', hI', gI', ps', ab', X⟩ :=
    xinvR_reach hr ⟨hs, gs, hI, gI, _, _, xinvR_init G hG0⟩
  obtain ⟨hab, dT, dP, dI, dgT, -, dgI, leI, iI, vw, -, -, -, safe, cons⟩ := X
  have abE : ∀ t, ab' t = [] := fun t => by
    have := hab t; rw [hd t] at this; exact List.map_eq_nil_iff.mp this
  refine ⟨hs', gs', hI', gI', ps', fun t ht => ?_, iI, fun t c x ex => ?_, leI,
    fun t u ne => ?_, fun t => ?_, fun t u ne => ?_, fun t => ?_, fun c hc => ?_⟩
  · have := safeR_skip_inv (by rw [← hf t ht]; exact safe t ht); exact this
  · have := vw t c x ex; rwa [hd t, view_nil] at this
  · have := dT t u ne; rw [abE, abE] at this; simpa [pH, union_empty_right] using this
  · have := dI t; rw [abE] at this; simpa [pH, union_empty_right] using this
  · have := dgT t u ne; rw [abE, abE] at this; simpa [pG, union_empty_right] using this
  · have := dgI t; rw [abE] at this; simpa [pG, union_empty_right] using this
  · rcases cons c hc with h | ⟨t, ht, h | h⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, h⟩
    · rw [abE] at h; cases h

end X

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel

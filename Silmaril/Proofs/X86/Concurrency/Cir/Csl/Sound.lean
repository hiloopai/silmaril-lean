module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rules

/-!
# CSL over CIR: soundness on the SC machine, and race freedom

Stated in `Silmaril.X86.Concurrency.Cir.Csl.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab truthy cellVals cellLast)
open Silmaril.X86.Concurrency.Cir.Csl

/-! ## Small facts -/

theorem upd_self {α : Type} (f : Nat → α) (t : Nat) (x : α) : upd f t x t = x := by
  simp [upd]

theorem upd_ne {α : Type} (f : Nat → α) {t u : Nat} (x : α) (h : u ≠ t) : upd f t x u = f u := by
  simp [upd, h]

theorem disjoint_of_dom {A B F : Heap} (hAB : ∀ a, (A a).isSome → (B a).isSome)
    (hd : Heap.Disjoint B F) : Heap.Disjoint A F := fun a => by
  rcases hd a with e | e
  · left
    cases e' : A a with
    | none => rfl
    | some _ => have := hAB a (by rw [e']; rfl); rw [e] at this; cases this
  · exact Or.inr e

theorem disjoint_of_excl {A B : Heap} (h : ∀ a, (A a).isSome → (B a).isSome → False) :
    Heap.Disjoint A B := fun a => by
  cases eA : A a with
  | none => exact Or.inl rfl
  | some _ =>
    cases eB : B a with
    | none => exact Or.inr rfl
    | some _ => exact absurd (h a (by rw [eA]; rfl) (by rw [eB]; rfl)) id

theorem disjoint_symm {A B : Heap} (hd : Heap.Disjoint A B) : Heap.Disjoint B A :=
  fun a => (hd a).symm

theorem na_drains {l : Lab} (h : l.na = true) : l.drains = false := by
  cases l <;> simp_all [Lab.na, Lab.drains]

/-- **One label step from `LabOk`**, next to an invariant heap: both the non-atomic and the
atomic case, in one form. -/
theorem labOk_use {I : HProp} {K : Heap → Prop} {l : Lab} {h hI : Heap} (L : LabOk I K l h)
    (hIi : I hI) (hd : Heap.Disjoint h hI) :
    l.isMem = true ∧ (∀ a, l.Touches a → (Heap.union h hI a).isSome) ∧
    (l.na = true → ∀ a, l.Touches a → (h a).isSome) ∧
    (l.drains = false → ∀ a, (l.wval a).isSome → (h a).isSome) ∧
    (l.okH (Heap.union h hI) → ∃ h' hI', Heap.Disjoint h' hI' ∧
      Heap.union h' hI' = l.updH (Heap.union h hI) ∧ I hI' ∧ K h' ∧
      (l.drains = false → ∀ a, (h a).isSome → (h' a).isSome)) := by
  obtain ⟨hm, hna, hat⟩ := L
  cases e : l.na
  · obtain ⟨c1, c2, c3⟩ := hat e hI hIi hd
    exact ⟨hm, c1, (fun e' => by cases e'), c2, c3⟩
  · obtain ⟨hc, hk⟩ := hna e
    refine ⟨hm, fun a ta => ?_, fun _ => hc, fun _ a ew => hc a (wval_touch ew), fun ok => ?_⟩
    · rw [union_isSome, hc a ta]; rfl
    · refine ⟨l.updH h, hI, disjoint_of_dom (fun a ea => ?_) hd, (updH_union h hI l).symm,
        hIi, hk (okH_of_le hc (le_union_left h hI) ok), fun _ a ea => ?_⟩
      · rw [updH_dom hc] at ea; exact ea
      · rw [updH_dom hc]; exact ea

/-! ## The global invariant -/

section GInv
variable {I : HProp} {Q : Nat → Regs → HProp} {N : Nat}

/-- **Footprints**: in a `GInv` state, every label step of a running thread touches only its
own heap and the invariant's; a non-atomic one only its own; a non-draining one writes only
its own. -/
theorem ginv_foot {C : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C hs hI) {t : Nat}
    (ht : t < N) {l : Lab} {s' : Stmt} {rs' : Regs}
    (st : TStep (C.ts t).1 (C.ts t).2 (some l) s' rs') :
    l.isMem = true ∧ (∀ a, l.Touches a → (Heap.union (hs t) hI a).isSome) ∧
    (l.na = true → ∀ a, l.Touches a → (hs t a).isSome) ∧
    (l.drains = false → ∀ a, (l.wval a).isSome → (hs t a).isSome) := by
  obtain ⟨-, hdI, -, -, hIi, hsafe⟩ := G
  obtain ⟨h1, h2, h3, h4, -⟩ := labOk_use ((safe_unfold (hsafe t ht)).2.2 l s' rs' st) hIi (hdI t)
  exact ⟨h1, h2, h3, h4⟩

theorem ginv_tau {C : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C hs hI) {t : Nat}
    (ht : t < N) {s' : Stmt} {rs' : Regs} (st : TStep (C.ts t).1 (C.ts t).2 none s' rs') :
    GInv I Q N ⟨upd C.ts t (s', rs'), C.mem⟩ hs hI := by
  obtain ⟨d1, d2, l1, l2, hIi, hsafe⟩ := G
  refine ⟨d1, d2, l1, l2, hIi, fun u hu => ?_⟩
  by_cases e : u = t
  · subst e; simp only [upd_self]; exact (safe_unfold (hsafe u hu)).2.1 _ _ st
  · simp only [upd_ne _ _ e]; exact hsafe u hu

/-- **Preservation by a label step** of the SC machine, with the new ghost heaps. -/
theorem ginv_lab {C : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C hs hI) {t : Nat}
    (ht : t < N) {l : Lab} {s' : Stmt} {rs' : Regs}
    (st : TStep (C.ts t).1 (C.ts t).2 (some l) s' rs') (hok : l.okH C.mem) :
    ∃ h' hI', GInv I Q N ⟨upd C.ts t (s', rs'), l.updH C.mem⟩ (upd hs t h') hI' ∧
      (l.drains = false → ∀ a, (hs t a).isSome → (h' a).isSome) := by
  obtain ⟨d1, d2, l1, l2, hIi, hsafe⟩ := G
  obtain ⟨-, c1, -, -, c3⟩ := labOk_use ((safe_unfold (hsafe t ht)).2.2 l s' rs' st) hIi (d2 t)
  obtain ⟨h', hI', d', eq', iI', k', sur⟩ := c3 (okH_of_le c1 (union_le (l1 t) l2) hok)
  -- the new heaps live inside the old footprint
  have dom' : ∀ a, ((h' a).isSome ∨ (hI' a).isSome) → (Heap.union (hs t) hI a).isSome := by
    intro a e
    have : (Heap.union h' hI' a).isSome := by
      rw [union_isSome]; rcases e with e | e <;> simp [e]
    rw [eq', updH_dom c1] at this; exact this
  have other : ∀ u, u ≠ t → ∀ a, (hs u a).isSome → (Heap.union (hs t) hI a).isSome → False := by
    intro u hu a e1 e2
    rw [union_isSome] at e2
    rcases d1 u t hu a with e | e
    · rw [e] at e1; cases e1
    · rcases d2 u a with e' | e'
      · rw [e'] at e1; cases e1
      · rw [e, e'] at e2; cases e2
  have wnone : ∀ u, u ≠ t → ∀ a, (hs u a).isSome → l.wval a = none := by
    intro u hu a e1
    cases ew : l.wval a with
    | none => rfl
    | some _ => exact absurd (other u hu a e1 (c1 a (wval_touch (by rw [ew]; rfl)))) id
  refine ⟨h', hI', ⟨fun u v huv => ?_, fun u => ?_, fun u => ?_, ?_, iI', fun u hu => ?_⟩, sur⟩
  · -- pairwise disjoint
    by_cases eu : u = t
    · subst eu
      rw [upd_self, upd_ne _ _ (Ne.symm huv)]
      exact disjoint_of_excl fun a e1 e2 => other v (Ne.symm huv) a e2 (dom' a (Or.inl e1))
    · by_cases ev : v = t
      · subst ev
        rw [upd_self, upd_ne _ _ eu]
        exact disjoint_of_excl fun a e1 e2 => other u eu a e1 (dom' a (Or.inl e2))
      · rw [upd_ne _ _ eu, upd_ne _ _ ev]; exact d1 u v huv
  · -- disjoint from the invariant heap
    by_cases eu : u = t
    · subst eu; rw [upd_self]; exact d'
    · rw [upd_ne _ _ eu]
      exact disjoint_of_excl fun a e1 e2 => other u eu a e1 (dom' a (Or.inr e2))
  · -- the thread heaps agree with memory
    by_cases eu : u = t
    · subst eu; rw [upd_self]
      exact le_trans (le_union_left h' hI')
        (eq' ▸ updH_le l (union_le (l1 u) l2))
    · rw [upd_ne _ _ eu]
      intro a v ev
      show l.updH C.mem a = some v
      rw [updH_of_not (wnone u eu a (by rw [ev]; rfl))]; exact l1 u a v ev
  · exact le_trans (le_union_right d') (eq' ▸ updH_le l (union_le (l1 t) l2))
  · by_cases eu : u = t
    · subst eu; simp only [upd_self]; exact k'
    · simp only [upd_ne _ _ eu]; exact hsafe u hu

/-- **Preservation by any SC step.** -/
theorem ginv_step {C C' : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C hs hI)
    (h : ScStep N C C') : ∃ hs' hI', GInv I Q N C' hs' hI' := by
  cases h with
  | tau ht hs => exact ⟨_, _, ginv_tau G ht hs⟩
  | lab ht st _ _ hok =>
    obtain ⟨h', hI', G', -⟩ := ginv_lab G ht st hok
    exact ⟨_, _, G'⟩

/-- **Preservation along SC runs.** -/
theorem ginv_reach {C C' : Cfg} (h : ScReach N C C') :
    ∀ {hs : Nat → Heap} {hI : Heap}, GInv I Q N C hs hI → ∃ hs' hI', GInv I Q N C' hs' hI' := by
  induction h with
  | refl => exact fun G => ⟨_, _, G⟩
  | step h _ ih =>
    intro hs hI G
    obtain ⟨hs', hI', G'⟩ := ginv_step G h
    exact ih G'

/-- **Adequacy**: in a finished `GInv` state every thread's postcondition holds of its heap,
the invariant holds of the shared heap, and these heaps are disjoint parts of memory. -/
theorem ginv_done {C : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C hs hI)
    (hd : C.Done N) :
    (∀ t < N, Q t (C.ts t).2 (hs t)) ∧ I hI ∧
    (∀ t u, t ≠ u → Heap.Disjoint (hs t) (hs u)) ∧ (∀ t, Heap.Disjoint (hs t) hI) ∧
    (∀ t, Heap.Le (hs t) C.mem) ∧ Heap.Le hI C.mem := by
  obtain ⟨d1, d2, l1, l2, hIi, hsafe⟩ := G
  refine ⟨fun t ht => ?_, hIi, d1, d2, l1, l2⟩
  have := hsafe t ht; rw [hd t ht] at this; exact safe_skip_inv this

/-! ## Race freedom -/

/-- **Owned non-atomic accesses never race.** -/
theorem ginv_no_race {C : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C hs hI) :
    ¬ Race N C := by
  rintro ⟨t, u, l, l', a, ht, hu, htu, ⟨s1, r1, st1⟩, ⟨s2, r2, st2⟩, ta, ta', hna⟩
  have F1 := ginv_foot G ht st1
  have F2 := ginv_foot G hu st2
  obtain ⟨d1, d2, -⟩ := G
  have key : ∀ t u, t ≠ u → (hs t a).isSome → (Heap.union (hs u) hI a).isSome → False := by
    intro t u htu e1 e2
    rw [union_isSome] at e2
    rcases d1 t u htu a with e | e
    · rw [e] at e1; cases e1
    · rcases d2 t a with e' | e'
      · rw [e'] at e1; cases e1
      · rw [e, e'] at e2; cases e2
  rcases hna with e | e
  · exact key t u htu (F1.2.2.1 e a ta) (F2.2.1 a ta')
  · exact key u t (Ne.symm htu) (F2.2.2.1 e a ta') (F1.2.1 a ta)

/-- **Weak stores need ownership**: an `nt` or `str` store of a running thread writes only a
cell the thread owns (it is a plain, non-draining store). -/
theorem ginv_weak_owned {C : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C hs hI)
    {t : Nat} (ht : t < N) {l : Lab} {s' : Stmt} {rs' : Regs}
    (st : TStep (C.ts t).1 (C.ts t).2 (some l) s' rs') (hw : l.weakStore = true) :
    ∀ a, l.Touches a → (hs t a).isSome := by
  obtain ⟨-, -, -, F⟩ := ginv_foot G ht st
  cases l with
  | wr m fl a0 sz v =>
    intro a ta
    rw [touches_wr.mp ta]
    exact F rfl a0 (by simp [Lab.wval])
  | _ => simp [Lab.weakStore] at hw

end GInv

end Silmaril.Proofs.X86.Concurrency.Cir.Csl

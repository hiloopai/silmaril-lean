module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.Basic

/-!
# CSL with release stores: domains, pending releases and the annotated-buffer invariant

Lemmas about `Dom`, `pH`/`pG`/`PDisj` and `AOk` used by the TSO adequacy proof
(`Rel/Tso.lean`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab truthy)
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel

/-! ## Domains -/

theorem dom_refl (h : Heap) : Dom h h := fun _ e => e

theorem dom_trans {a b c : Heap} (h₁ : Dom a b) (h₂ : Dom b c) : Dom a c :=
  fun x e => h₂ x (h₁ x e)

theorem dom_union_left (A B : Heap) : Dom A (Heap.union A B) := fun a e => by
  rw [union_isSome, e]; rfl

theorem dom_union_right (A B : Heap) : Dom B (Heap.union A B) := fun a e => by
  rw [union_isSome, e, Bool.or_true]

theorem dom_union {A B C : Heap} (h₁ : Dom A C) (h₂ : Dom B C) : Dom (Heap.union A B) C :=
  fun a e => by
    rw [union_isSome] at e
    cases e1 : (A a).isSome
    · rw [e1, Bool.false_or] at e; exact h₂ a e
    · exact h₁ a e1

theorem dom_empty (h : Heap) : Dom Heap.empty h := fun _ e => by cases e

theorem disj_of_dom {A B A' B' : Heap} (d : Heap.Disjoint A B) (h₁ : Dom A' A) (h₂ : Dom B' B) :
    Heap.Disjoint A' B' := fun a => by
  rcases d a with e | e
  · left
    cases e' : A' a with
    | none => rfl
    | some _ => have := h₁ a (by rw [e']; rfl); rw [e] at this; cases this
  · right
    cases e' : B' a with
    | none => rfl
    | some _ => have := h₂ a (by rw [e']; rfl); rw [e] at this; cases this

theorem disj_union_left {A B C : Heap} (h₁ : Heap.Disjoint A C) (h₂ : Heap.Disjoint B C) :
    Heap.Disjoint (Heap.union A B) C := fun a => by
  rw [union_apply]
  rcases h₁ a with e | e
  · rw [e, Option.none_or]; exact h₂ a
  · exact Or.inr e

theorem disj_union_right {A B C : Heap} (h₁ : Heap.Disjoint A B) (h₂ : Heap.Disjoint A C) :
    Heap.Disjoint A (Heap.union B C) :=
  disjoint_symm (disj_union_left (disjoint_symm h₁) (disjoint_symm h₂))

theorem disj_none {A B : Heap} (d : Heap.Disjoint A B) {a : Nat} (e : (A a).isSome) :
    B a = none := by
  rcases d a with e' | e'
  · rw [e'] at e; cases e
  · exact e'

theorem none_of_disj {A B : Heap} (d : Heap.Disjoint A B) {a : Nat} (e : (B a).isSome) :
    A a = none := by
  rcases d a with e' | e'
  · exact e'
  · rw [e'] at e; cases e

theorem isSome_of_le {A M : Heap} (h : Heap.Le A M) {a : Nat} (e : (A a).isSome) :
    (M a).isSome := by
  cases e' : A a with
  | none => rw [e'] at e; cases e
  | some v => rw [h a v e']; rfl

theorem le_union {A B M : Heap} (h₁ : Heap.Le A M) (h₂ : Heap.Le B M) :
    Heap.Le (Heap.union A B) M := by
  intro a v e; rw [union_apply] at e
  cases e' : A a with
  | none => rw [e', Option.none_or] at e; exact h₂ a v e
  | some w => rw [e'] at e; cases e; exact h₁ a _ e'

theorem le_union_left (A B : Heap) : Heap.Le A (Heap.union A B) := by
  intro a v e; rw [union_apply, e]; rfl

theorem le_union_right {A B : Heap} (d : Heap.Disjoint A B) : Heap.Le B (Heap.union A B) := by
  intro a v e; rw [union_apply, none_of_disj d (by rw [e]; rfl), Option.none_or]; exact e

theorem dom_of_le {A M : Heap} (h : Heap.Le A M) : Dom A M := fun _ e => isSome_of_le h e

theorem union_assoc (A B C : Heap) :
    Heap.union (Heap.union A B) C = Heap.union A (Heap.union B C) := by
  funext a; simp only [union_apply, Option.or_assoc]

/-! ## Entries -/

theorem apply_st (M : Heap) (a v : Nat) (w : Bool) (x : Nat) :
    (Ent.st a v w).apply M x = if x = a then some v else M x := rfl

theorem apply_bar (M : Heap) : Ent.bar.apply M = M := rfl

theorem le_apply {A M : Heap} (e : Ent) (h : Heap.Le A M) : Heap.Le (e.apply A) (e.apply M) := by
  cases e with
  | bar => exact h
  | st a v w =>
    intro x u ex; rw [apply_st] at ex ⊢
    by_cases hx : x = a
    · simp only [hx, ite_true] at ex ⊢; exact ex
    · simp only [hx, ite_false] at ex ⊢; exact h x u ex

theorem apply_agree {A M : Heap} (e : Ent) {x : Nat} (h : A x = M x) :
    e.apply A x = e.apply M x := by
  cases e with
  | bar => exact h
  | st a v w => rw [apply_st, apply_st]; split <;> simp_all

theorem dom_apply {A : Heap} {a v : Nat} {w : Bool} (ha : (A a).isSome) :
    Dom ((Ent.st a v w).apply A) A := fun x e => by
  rw [apply_st] at e
  by_cases hx : x = a
  · subst hx; exact ha
  · simpa [hx] using e

theorem dom_apply' {A : Heap} (e : Ent) : Dom A (e.apply A) := fun x ex => by
  cases e with
  | bar => exact ex
  | st a v w => rw [apply_st]; split <;> simp_all

/-- A label's buffered entries write only cells the label writes. -/
theorem ents_wval {l : Lab} {c v : Nat} {w : Bool} (h : Ent.st c v w ∈ l.ents) :
    (l.wval c).isSome := by
  cases l with
  | wr m fl a sz v0 =>
    simp only [Lab.ents, List.mem_singleton, Ent.st.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    simp [Lab.wval]
  | blk n ins outs rvs =>
    simp only [Lab.ents, List.mem_map] at h
    obtain ⟨⟨c1, c2, c3⟩, hm, he⟩ := h
    simp only [Ent.st.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    simp only [Lab.wval]
    clear * - hm
    induction outs with
    | nil => cases hm
    | cons d ds ih =>
      simp only [Silmaril.X86.Concurrency.Cir.cellLast]
      rcases List.mem_cons.mp hm with e | e
      · subst e; rw [or_isSome]; simp
      · rw [or_isSome, ih e]; rfl
  | fence k => cases k <;> simp [Lab.ents] at h
  | _ => simp [Lab.ents] at h

/-! ## Pending releases -/

theorem pH_append (b c : ABuf) : pH (b ++ c) = Heap.union (pH b) (pH c) := by
  induction b with
  | nil => simp [pH, union_empty]
  | cons x b ih =>
    obtain ⟨e, r⟩ := x
    cases r with
    | none => simp [pH, ih]
    | some r => simp [pH, ih, union_assoc]

theorem pG_append (b c : ABuf) : pG (b ++ c) = Heap.union (pG b) (pG c) := by
  induction b with
  | nil => simp [pG, union_empty]
  | cons x b ih =>
    obtain ⟨e, r⟩ := x
    cases r with
    | none => simp [pG, ih]
    | some r => simp [pG, ih, union_assoc]

theorem pH_nones (es : List Ent) : pH (es.map fun e => (e, (none : Option PRec))) = Heap.empty := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [pH] using ih

theorem pG_nones (es : List Ent) : pG (es.map fun e => (e, (none : Option PRec))) = Heap.empty := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [pG] using ih

theorem pH_norec {b : ABuf} (h : ∀ x ∈ b, x.2 = none) : pH b = Heap.empty := by
  induction b with
  | nil => rfl
  | cons x b ih =>
    obtain ⟨e, r⟩ := x
    have hr : r = none := h _ (List.mem_cons_self ..)
    subst hr
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem pG_norec {b : ABuf} (h : ∀ x ∈ b, x.2 = none) : pG b = Heap.empty := by
  induction b with
  | nil => rfl
  | cons x b ih =>
    obtain ⟨e, r⟩ := x
    have hr : r = none := h _ (List.mem_cons_self ..)
    subst hr
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem pDisj_append_nones {b : ABuf} (es : List Ent) (h : PDisj b) :
    PDisj (b ++ es.map fun e => (e, (none : Option PRec))) := by
  induction b with
  | nil =>
    simp only [List.nil_append]
    induction es with
    | nil => trivial
    | cons e es ih => exact ih
  | cons x b ih =>
    obtain ⟨e, r⟩ := x
    cases r with
    | none => exact ih h
    | some r =>
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨?_, ?_, ih h3⟩
      · change r.hR.Disjoint (pH (b ++ _)); rw [pH_append, pH_nones, union_empty_right]; exact h1
      · change r.gR.Disjoint (pG (b ++ _)); rw [pG_append, pG_nones, union_empty_right]; exact h2

theorem pDisj_append_rec {b : ABuf} (e : Ent) (r : PRec) (h : PDisj b)
    (dh : Heap.Disjoint (pH b) r.hR) (dg : Heap.Disjoint (pG b) r.gR) :
    PDisj (b ++ [(e, some r)]) := by
  induction b with
  | nil => exact ⟨disjoint_empty_right _, disjoint_empty_right _, trivial⟩
  | cons x b ih =>
    obtain ⟨e0, r0⟩ := x
    cases r0 with
    | none => exact ih h dh dg
    | some r0 =>
      obtain ⟨h1, h2, h3⟩ := h
      have dh' : Heap.Disjoint (pH b) r.hR :=
        disj_of_dom dh (dom_union_right _ _) (dom_refl _)
      have dg' : Heap.Disjoint (pG b) r.gR :=
        disj_of_dom dg (dom_union_right _ _) (dom_refl _)
      have d0 : Heap.Disjoint r0.hR r.hR := disj_of_dom dh (dom_union_left _ _) (dom_refl _)
      have g0 : Heap.Disjoint r0.gR r.gR := disj_of_dom dg (dom_union_left _ _) (dom_refl _)
      refine ⟨?_, ?_, ih h3 dh' dg'⟩
      · change r0.hR.Disjoint (pH (b ++ _)); rw [pH_append]; simp only [pH]
        exact disj_union_right h1 (disj_union_right d0 (disjoint_empty_right _))
      · change r0.gR.Disjoint (pG (b ++ _)); rw [pG_append]; simp only [pG]
        exact disj_union_right h2 (disj_union_right g0 (disjoint_empty_right _))

theorem pDisj_tail {x : Ent × Option PRec} {b : ABuf} (h : PDisj (x :: b)) : PDisj b := by
  obtain ⟨e, r⟩ := x
  cases r with
  | none => exact h
  | some r => exact h.2.2

/-! ## The annotated-buffer invariant -/

section A
variable {I : GProp}

/-- `AOk` depends on the owned heaps through their domains only. -/
theorem aok_dom {hs gs hs' gs' : Heap} (eh : ∀ a, (hs a).isSome = (hs' a).isSome)
    (eg : ∀ a, (gs a).isSome = (gs' a).isSome) {V : Heap} {b : ABuf} (H : AOk I hs gs V b) :
    AOk I hs' gs' V b := by
  induction b generalizing V with
  | nil => trivial
  | cons x b ih =>
    obtain ⟨e, r⟩ := x
    cases r with
    | none =>
      obtain ⟨h1, h2⟩ := H
      refine ⟨?_, ih h2⟩
      cases e with
      | st c v w => show (hs' c).isSome = true ∨ _; rw [← eh c]; exact h1
      | bar => trivial
    | some r =>
      obtain ⟨⟨a, v, w, rfl, ha, hp⟩, h2, h3, h4, h5, h6⟩ := H
      refine ⟨⟨a, v, w, rfl, ?_, hp⟩, h2, h3, fun x ex => ?_, fun x ex => ?_, ih h6⟩
      · cases e' : hs' a with
        | none => rfl
        | some _ => have := eh a; rw [ha, e'] at this; cases this
      · have := h4 x ex; rw [union_isSome] at this ⊢; rw [← eh x]; exact this
      · have := h5 x ex; rw [union_isSome] at this ⊢; rw [← eg x]; exact this

/-- Without pending releases, `AOk` survives growing the owned heap. -/
theorem aok_grow {hs gs hs' gs' : Heap} (dh : Dom hs hs') {V : Heap} {b : ABuf}
    (hn : ∀ x ∈ b, x.2 = none) (H : AOk I hs gs V b) : AOk I hs' gs' V b := by
  induction b generalizing V with
  | nil => trivial
  | cons x b ih =>
    obtain ⟨e, r⟩ := x
    have hr : r = none := hn _ (List.mem_cons_self ..)
    subst hr
    obtain ⟨h1, h2⟩ := H
    refine ⟨?_, ih (fun y hy => hn y (List.mem_cons_of_mem _ hy)) h2⟩
    cases e with
    | st c v w =>
      change (hs c).isSome = true ∨ (pH b c).isSome = true at h1
      show (hs' c).isSome = true ∨ (pH b c).isSome = true
      rw [pH_norec (fun y hy => hn y (List.mem_cons_of_mem _ hy))] at h1 ⊢
      rcases h1 with h1 | h1
      · exact Or.inl (dh c h1)
      · cases h1
    | bar => trivial

/-- Appending plain stores to owned cells. -/
theorem aok_append_nones {hs gs : Heap} (es : List Ent)
    (hes : ∀ c v w, Ent.st c v w ∈ es → (hs c).isSome) {V : Heap} {b : ABuf}
    (H : AOk I hs gs V b) : AOk I hs gs V (b ++ es.map fun e => (e, (none : Option PRec))) := by
  induction b generalizing V with
  | nil =>
    simp only [List.nil_append]
    clear H
    induction es generalizing V with
    | nil => trivial
    | cons e es ih =>
      refine ⟨?_, ih (fun c v w h => hes c v w (List.mem_cons_of_mem _ h))⟩
      cases e with
      | st c v w => exact Or.inl (hes c v w (List.mem_cons_self ..))
      | bar => trivial
  | cons x b ih =>
    obtain ⟨e, r⟩ := x
    rw [List.cons_append]
    cases r with
    | none =>
      obtain ⟨h1, h2⟩ := H
      refine ⟨?_, ih h2⟩
      cases e with
      | st c v w =>
        show (hs c).isSome = true ∨ (pH (b ++ _) c).isSome = true
        rw [pH_append, pH_nones, union_empty_right]; exact h1
      | bar => trivial
    | some r =>
      obtain ⟨⟨a, v, w, rfl, ha, hp⟩, h2, h3, h4, h5, h6⟩ := H
      refine ⟨⟨a, v, w, rfl, ha, ?_⟩, h2, h3, ?_, ?_, ih h6⟩
      · rw [pH_append, pH_nones, union_empty_right]; exact hp
      · have : pH ((Ent.st a v w, some r) :: (b ++ es.map fun e => (e, (none : Option PRec)))) =
            pH ((Ent.st a v w, some r) :: b) := by
          simp only [pH]; rw [pH_append, pH_nones, union_empty_right]
        rw [this]; exact h4
      · have : pG ((Ent.st a v w, some r) :: (b ++ es.map fun e => (e, (none : Option PRec)))) =
            pG ((Ent.st a v w, some r) :: b) := by
          simp only [pG]; rw [pG_append, pG_nones, union_empty_right]
        rw [this]; exact h5

/-- `AOk` depends on memory only on the cells held by pending releases. -/
theorem aok_mem {hs gs : Heap} {V V' : Heap} {b : ABuf}
    (ag : ∀ c, (pH b c).isSome → V c = V' c) (H : AOk I hs gs V b) : AOk I hs gs V' b := by
  induction b generalizing V V' with
  | nil => trivial
  | cons x b ih =>
    obtain ⟨e, r⟩ := x
    cases r with
    | none =>
      obtain ⟨h1, h2⟩ := H
      exact ⟨h1, ih (fun c hc => apply_agree e (ag c (by simpa [pH] using hc))) h2⟩
    | some r =>
      obtain ⟨h0, h2, h3, h4, h5, h6⟩ := H
      refine ⟨h0, h2, fun c u ec => ?_, h4, h5, ih (fun c hc => apply_agree e (ag c ?_)) h6⟩
      · rw [← ag c (by simp only [pH]; rw [union_isSome, ec]; rfl)]; exact h3 c u ec
      · simp only [pH]; rw [union_isSome, hc, Bool.or_true]

/-- **Appending a release.** The thread keeps `h'`/`g'` and the new record holds `hR`/`gR`. -/
theorem aok_release {h g h' hR g' gR : Heap} {a v : Nat} {w : Bool} {V : Heap} {b : ABuf}
    (H : AOk I h g V b) (eh : h = Heap.union h' hR) (eg : g = Heap.union g' gR)
    (ha : h' a = none)
    (ob : Oblig I (.st a v w) hR gR h g) (hle : Heap.Le hR (view V (b.map Prod.fst))) :
    AOk I h' g' V (b ++ [(.st a v w, some ⟨hR, gR, h, g⟩)]) := by
  induction b generalizing V with
  | nil =>
    refine ⟨⟨a, v, w, rfl, ha, rfl⟩, ob, by simpa [view_nil] using hle, ?_, ?_, trivial⟩
    · simp only [pH]; rw [eh, union_empty_right]; exact dom_refl _
    · simp only [pG]; rw [eg, union_empty_right]; exact dom_refl _
  | cons x b ih =>
    obtain ⟨e, r⟩ := x
    rw [List.cons_append]
    have hle' : Heap.Le hR (view (e.apply V) (b.map Prod.fst)) := by
      simpa [view_cons] using hle
    have dom1 : Dom h (Heap.union h' (pH (b ++ [(Ent.st a v w, some ⟨hR, gR, h, g⟩)]))) := by
      rw [eh, pH_append]; simp only [pH]
      refine dom_union (dom_union_left _ _) (dom_trans (dom_union_left hR Heap.empty)
        (dom_trans (dom_union_right (pH b) _) (dom_union_right _ _)))
    cases r with
    | none =>
      obtain ⟨h1, h2⟩ := H
      refine ⟨?_, ih h2 hle'⟩
      cases e with
      | st c u w' =>
        change (h c).isSome = true ∨ (pH b c).isSome = true at h1
        show (h' c).isSome = true ∨ (pH (b ++ _) c).isSome = true
        rcases h1 with h1 | h1
        · have := dom1 c h1; rw [union_isSome] at this; simpa [Bool.or_eq_true] using this
        · right; rw [pH_append, union_isSome, h1]; rfl
      | bar => trivial
    | some r =>
      obtain ⟨⟨a0, v0, w0, rfl, ha0, hp0⟩, h2, h3, h4, h5, h6⟩ := H
      refine ⟨⟨a0, v0, w0, rfl, ?_, ?_⟩, h2, h3, fun x ex => ?_, fun x ex => ?_, ih h6 hle'⟩
      · cases e' : h' a0 with
        | none => rfl
        | some _ =>
          have := dom_union_left h' hR a0 (by rw [e']; rfl)
          rw [← eh, ha0] at this; cases this
      · rw [pH_append]; simp only [pH]
        rw [union_apply, hp0, Option.none_or, union_apply, empty_apply, Option.or_none]
        cases e' : hR a0 with
        | none => rfl
        | some _ =>
          have := dom_union_right h' hR a0 (by rw [e']; rfl)
          rw [← eh, ha0] at this; cases this
      · have := h4 x ex
        simp only [pH] at this ⊢
        rw [union_isSome, union_isSome] at this
        rw [union_isSome, union_isSome, pH_append, union_isSome]; simp only [pH]
        rw [eh, union_isSome] at this
        cases e1 : (h' x).isSome <;> cases e2 : (hR x).isSome <;>
          cases e3 : (r.hR x).isSome <;> cases e4 : (pH b x).isSome <;> simp_all [union_empty_right]
      · have := h5 x ex
        simp only [pG] at this ⊢
        rw [union_isSome, union_isSome] at this
        rw [union_isSome, union_isSome, pG_append, union_isSome]; simp only [pG]
        rw [eg, union_isSome] at this
        cases e1 : (g' x).isSome <;> cases e2 : (gR x).isSome <;>
          cases e3 : (r.gR x).isSome <;> cases e4 : (pG b x).isSome <;> simp_all [union_empty_right]

/-- Without pending releases, every buffered cell is owned. -/
theorem aok_newest {hs gs V : Heap} {b : ABuf} (hn : ∀ x ∈ b, x.2 = none)
    (H : AOk I hs gs V b) {c : Nat} (e : (newest (b.map Prod.fst) c).isSome) : (hs c).isSome := by
  induction b generalizing V with
  | nil => cases e
  | cons x b ih =>
    obtain ⟨e0, r⟩ := x
    have hr : r = none := hn _ (List.mem_cons_self ..)
    subst hr
    obtain ⟨h1, h2⟩ := H
    simp only [List.map_cons, newest, or_isSome, Bool.or_eq_true] at e
    rcases e with e | e
    · exact ih (fun y hy => hn y (List.mem_cons_of_mem _ hy)) h2 e
    · cases e0 with
      | st c0 v0 w0 =>
        simp only [Ent.val] at e
        by_cases hc : c0 = c
        · subst hc
          change (hs c0).isSome = true ∨ (pH b c0).isSome = true at h1
          rw [pH_norec (fun y hy => hn y (List.mem_cons_of_mem _ hy))] at h1
          rcases h1 with h1 | h1
          · exact h1
          · cases h1
        · simp [hc] at e
      | bar => cases e

end A

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel

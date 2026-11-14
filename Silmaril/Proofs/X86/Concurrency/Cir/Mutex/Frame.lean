module

public import Silmaril.X86.Concurrency.Cir.Csl.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Defs

/-!
# Proofs: heap lemmas and the invariant frame rule

* the fixed-point helpers `labOk_mono`, `safeF_mono`, `safe_post`, `safe_intro` and the silent
  `safe_assign`, **restated** from `Proofs/…/Prim/Csl.lean` (the base CSL and explorer proofs
  modules belong to other topics and are not imported);
* heap lemmas on `Heap.union`, `Heap.single` and `∗`;
* **`safe_inv_frame`**: `Safe I Q s rs h → Safe (I ∗ J) Q s rs h`. A thread proved under the
  invariant `I` stays safe when the invariant is extended by any `J` it never opens. This is what
  lets `Mutex.Iface` state its specs under every frame invariant;
* `safe_inv_eq`: `Safe` respects equivalent invariants.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Sep.BI.SepAlg (pmapUnion pmapDisjoint)

/-! ## The fixed point, restated -/

theorem labOk_mono {I : HProp} {K K' : Heap → Prop} (hK : ∀ h, K h → K' h) {l : Lab} {h : Heap}
    (H : LabOk I K l h) : LabOk I K' l h := by
  obtain ⟨hm, hna, hat⟩ := H
  refine ⟨hm, fun hn => ⟨(hna hn).1, fun hok => hK _ ((hna hn).2 hok)⟩, fun hn hI hIi hd => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hat hn hI hIi hd
  refine ⟨h1, h2, fun hok => ?_⟩
  obtain ⟨h', hI', a, b, c, d, e⟩ := h3 hok
  exact ⟨h', hI', a, b, c, hK _ d, e⟩

theorem safeF_mono {I : HProp} {Q : Regs → HProp} {R R' : Stmt → Regs → Heap → Prop}
    (hR : ∀ s rs h, R s rs h → R' s rs h) {s : Stmt} {rs : Regs} {h : Heap}
    (H : SafeF I Q R s rs h) : SafeF I Q R' s rs h :=
  ⟨H.1, fun s' rs' hs => hR _ _ _ (H.2.1 s' rs' hs),
    fun l s' rs' hs => labOk_mono (hR _ _) (H.2.2 l s' rs' hs)⟩

theorem safe_post {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : Csl.Safe I Q s rs h) : SafeF I Q (Csl.Safe I Q) s rs h := by
  obtain ⟨R, hR, hpost⟩ := H
  exact safeF_mono (fun s rs h hr => ⟨R, hr, hpost⟩) (hpost _ _ _ hR)

theorem safe_intro {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : SafeF I Q (Csl.Safe I Q) s rs h) : Csl.Safe I Q s rs h := by
  refine ⟨fun s' rs' h' => (s' = s ∧ rs' = rs ∧ h' = h) ∨ Csl.Safe I Q s' rs' h',
    Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
  rintro s' rs' h' (⟨rfl, rfl, rfl⟩ | hs)
  · exact safeF_mono (fun _ _ _ x => Or.inr x) H
  · exact safeF_mono (fun _ _ _ x => Or.inr x) (safe_post hs)

/-- **A silent register assignment.** -/
theorem safe_assign {I : HProp} {Q : Regs → HProp} {d : Reg} {e : Expr} {rs : Regs} {h : Heap}
    (hq : Q (rs.set d (e.eval rs)) h) : Csl.Safe I Q (.assign d e) rs h := by
  refine safe_intro ⟨(fun e => by cases e), (fun s' rs' hs => ?_), (fun l s' rs' hs => by cases hs)⟩
  cases hs
  exact safe_skip hq

/-! ## Heaps -/

theorem union_apply (h₁ h₂ : Heap) (a : Nat) :
    Heap.union h₁ h₂ a = match h₁ a with | some v => some v | none => h₂ a := by
  simp only [Heap.union, pmapUnion]; cases h₁ a <;> rfl

theorem single_apply (a v x : Nat) : Heap.single a v x = if x = a then some v else none := by
  simp only [Heap.single]

theorem union_none {h₁ h₂ : Heap} {a : Nat} (h : h₁ a = none) : Heap.union h₁ h₂ a = h₂ a := by
  simp [union_apply, h]

theorem union_some {h₁ h₂ : Heap} {a v : Nat} (h : h₁ a = some v) :
    Heap.union h₁ h₂ a = some v := by
  simp [union_apply, h]

theorem union_eq_none {h₁ h₂ : Heap} {a : Nat} :
    Heap.union h₁ h₂ a = none ↔ h₁ a = none ∧ h₂ a = none := by
  cases e : h₁ a <;> simp [union_apply, e]

theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by
  funext x; simp [union_apply, Heap.empty]

theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by
  funext x; cases e : h x <;> simp [union_apply, e, Heap.empty]

theorem disjoint_empty (h : Heap) : Heap.Disjoint Heap.empty h := fun _ => Or.inl rfl

theorem disjoint_empty_right (h : Heap) : Heap.Disjoint h Heap.empty := fun _ => Or.inr rfl

theorem disjoint_symm {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) : Heap.Disjoint h₂ h₁ :=
  fun a => (d a).symm

theorem union_comm {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) :
    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by
  funext a
  rcases d a with e | e
  · rw [union_none e]; cases e' : h₂ a <;> simp [union_apply, e, e']
  · rw [union_none (h₁ := h₂) e]; cases e' : h₁ a <;> simp [union_apply, e, e']

theorem union_assoc (h₁ h₂ h₃ : Heap) :
    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) := by
  funext a; simp only [union_apply]; cases h₁ a <;> rfl

/-- Disjointness from a union. -/
theorem disjoint_union_left {h₁ h₂ h : Heap} :
    Heap.Disjoint (Heap.union h₁ h₂) h ↔ Heap.Disjoint h₁ h ∧ Heap.Disjoint h₂ h := by
  constructor
  · intro d
    refine ⟨fun a => ?_, fun a => ?_⟩ <;> rcases d a with e | e
    · exact Or.inl (union_eq_none.mp e).1
    · exact Or.inr e
    · exact Or.inl (union_eq_none.mp e).2
    · exact Or.inr e
  · rintro ⟨d₁, d₂⟩ a
    rcases d₁ a with e₁ | e₁
    · rcases d₂ a with e₂ | e₂
      · exact Or.inl (union_eq_none.mpr ⟨e₁, e₂⟩)
      · exact Or.inr e₂
    · exact Or.inr e₁

theorem disjoint_union_right {h₁ h₂ h : Heap} :
    Heap.Disjoint h (Heap.union h₁ h₂) ↔ Heap.Disjoint h h₁ ∧ Heap.Disjoint h h₂ := by
  constructor
  · intro d
    have := disjoint_union_left.mp (disjoint_symm d)
    exact ⟨disjoint_symm this.1, disjoint_symm this.2⟩
  · rintro ⟨d₁, d₂⟩
    exact disjoint_symm (disjoint_union_left.mpr ⟨disjoint_symm d₁, disjoint_symm d₂⟩)

theorem disjoint_single {a v b w : Nat} (h : a ≠ b) :
    Heap.Disjoint (Heap.single a v) (Heap.single b w) := by
  intro x
  by_cases hx : x = a
  · subst hx; exact Or.inr (by simp [single_apply, h])
  · exact Or.inl (by simp [single_apply, hx])

theorem disjoint_single_left {a v : Nat} {h : Heap} (e : h a = none) :
    Heap.Disjoint (Heap.single a v) h := by
  intro x
  by_cases hx : x = a
  · subst hx; exact Or.inr e
  · exact Or.inl (by simp [single_apply, hx])

/-- Disjoint heaps do not share a mapped cell. -/
theorem disjoint_some {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) {a : Nat}
    (e₁ : (h₁ a).isSome) (e₂ : (h₂ a).isSome) : False := by
  rcases d a with e | e <;> simp [e] at e₁ e₂

theorem sep_iff {P Q : HProp} {h : Heap} :
    (P ∗ Q) h ↔ ∃ h₁ h₂, Heap.Disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P h₁ ∧ Q h₂ := Iff.rfl

theorem sep_comm {P Q : HProp} {h : Heap} (H : (P ∗ Q) h) : (Q ∗ P) h := by
  obtain ⟨h₁, h₂, d, rfl, p, q⟩ := sep_iff.mp H
  exact sep_iff.mpr ⟨h₂, h₁, disjoint_symm d, union_comm d, q, p⟩

theorem sep_emp {P : HProp} {h : Heap} (H : P h) : (P ∗ hemp) h :=
  sep_iff.mpr ⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, H, rfl⟩

theorem le_union_left {h₁ h₂ : Heap} : Heap.Le h₁ (Heap.union h₁ h₂) :=
  fun _ _ e => union_some e

theorem le_union_right {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) :
    Heap.Le h₂ (Heap.union h₁ h₂) := by
  rw [union_comm d]; exact le_union_left

/-! ## The invariant frame rule -/

/-- A cell a label writes is a cell it touches. -/
theorem touches_of_wval {l : Lab} {a : Nat} (h : (l.wval a).isSome) : l.Touches a := Or.inr h

/-- Extending the invariant by `J` keeps a label step's obligations. -/
theorem labOk_frameI {I J : HProp} {K : Heap → Prop} {l : Lab} {h : Heap} (H : LabOk I K l h) :
    LabOk (I ∗ J) K l h := by
  obtain ⟨hm, hna, hat⟩ := H
  refine ⟨hm, hna, fun hn hIJ hIJi hd => ?_⟩
  obtain ⟨hI, hJ, dIJ, rfl, iI, jJ⟩ := sep_iff.mp hIJi
  obtain ⟨hdI, hdJ⟩ := disjoint_union_right.mp hd
  obtain ⟨t1, t2, t3⟩ := hat hn hI iI hdI
  -- the cells of `h ∪ hI` keep their values in `h ∪ (hI ∪ hJ)`
  have keep : ∀ a, (Heap.union h hI a).isSome →
      Heap.union h (Heap.union hI hJ) a = Heap.union h hI a := by
    intro a ha
    cases e1 : h a with
    | some v => simp [union_apply, e1]
    | none =>
      rw [union_none e1, union_none e1] at *
      cases e2 : hI a with
      | some v => simp [union_apply, e2]
      | none => simp [e2] at ha
  -- a cell of `hJ` is not in `h ∪ hI`
  have outJ : ∀ a, (hJ a).isSome → Heap.union h hI a = none := by
    intro a ha
    refine union_eq_none.mpr ⟨?_, ?_⟩
    · rcases hdJ a with e | e
      · exact e
      · simp [e] at ha
    · rcases dIJ a with e | e
      · exact e
      · simp [e] at ha
  refine ⟨fun a ha => ?_, t2, fun hok => ?_⟩
  · have := t1 a ha
    rw [keep a this]; exact this
  have hok' : l.okH (Heap.union h hI) := by
    intro p hp
    have ht : (Heap.union h hI p.1).isSome := t1 p.1 (Or.inl ⟨p.2, hp⟩)
    rw [← keep p.1 ht]; exact hok p hp
  obtain ⟨h', hI', d', e', iI', k', g'⟩ := t3 hok'
  -- the new heaps do not reach into `hJ`
  have newJ : ∀ a, (hJ a).isSome → h' a = none ∧ hI' a = none := by
    intro a ha
    have h0 := outJ a ha
    have hw : l.wval a = none := by
      cases e : l.wval a with
      | none => rfl
      | some v =>
        have := t1 a (touches_of_wval (by simp [e]))
        simp [h0] at this
    have : Heap.union h' hI' a = none := by
      rw [e']; simp [Lab.updH, hw, h0]
    exact union_eq_none.mp this
  have dJ' : Heap.Disjoint hI' hJ := by
    intro a
    cases e : hJ a with
    | none => exact Or.inr rfl
    | some v => exact Or.inl (newJ a (by simp [e])).2
  refine ⟨h', Heap.union hI' hJ, ?_, ?_, sep_iff.mpr ⟨hI', hJ, dJ', rfl, iI', jJ⟩, k', g'⟩
  · intro a
    cases e : hJ a with
    | none =>
      rcases d' a with x | x
      · exact Or.inl x
      · exact Or.inr (union_eq_none.mpr ⟨x, e⟩)
    | some v => exact Or.inl (newJ a (by simp [e])).1
  · funext a
    cases e : hJ a with
    | none =>
      have hJn : Heap.union h (Heap.union hI hJ) a = Heap.union h hI a := by
        cases e1 : h a with
        | some v => simp [union_apply, e1]
        | none => rw [union_none e1, union_none e1]; cases e2 : hI a <;> simp [union_apply, e2, e]
      have lhs : Heap.union h' (Heap.union hI' hJ) a = Heap.union h' hI' a := by
        cases e1 : h' a with
        | some v => simp [union_apply, e1]
        | none => rw [union_none e1, union_none e1]; cases e2 : hI' a <;> simp [union_apply, e2, e]
      rw [lhs, e']
      simp only [Lab.updH, hJn]
    | some v =>
      obtain ⟨n1, n2⟩ := newJ a (by simp [e])
      have h0 := outJ a (by simp [e])
      obtain ⟨z1, z2⟩ := union_eq_none.mp h0
      have hw : l.wval a = none := by
        cases ew : l.wval a with
        | none => rfl
        | some w =>
          have := t1 a (touches_of_wval (by simp [ew]))
          simp [h0] at this
      rw [union_none n1, union_none n2, e]
      simp only [Lab.updH, hw, union_none z1, union_none z2, e, Option.none_or]

/-- **The invariant frame rule.** -/
theorem safe_inv_frame {I J : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : Csl.Safe I Q s rs h) : Csl.Safe (I ∗ J) Q s rs h := by
  refine ⟨Csl.Safe I Q, H, fun s rs h H => ?_⟩
  obtain ⟨hq, htau, hlab⟩ := safe_post H
  exact ⟨hq, htau, fun l s' rs' st => labOk_frameI (hlab l s' rs' st)⟩

/-- `Safe` respects equivalent invariants. -/
theorem safe_inv_eq {I I' : HProp} (hI : ∀ h, I h ↔ I' h) {Q : Regs → HProp} {s : Stmt}
    {rs : Regs} {h : Heap} (H : Csl.Safe I Q s rs h) : Csl.Safe I' Q s rs h := by
  have : I = I' := funext fun h => propext (hI h)
  subst this; exact H

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex

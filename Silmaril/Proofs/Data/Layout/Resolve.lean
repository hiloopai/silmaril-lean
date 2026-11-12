module

public import Silmaril.Data.Layout.Thms

/-!
# Proofs: fuel monotonicity and nested member designators

`layoutTy` is monotone in its fuel; every member of a computed layout has the size of its
type's layout and an alignment that the type's alignment divides; and `resolve` designates a
subobject inside the object, at an offset its alignment divides (`resolve_wf`).
-/

@[expose] public section

namespace Silmaril.Proofs.Data.Layout

open Silmaril.Data.Layout

variable {dm : DataModel} {env : Env}

theorem fieldShapes_mono {g g' : CTy → Except String Shape}
    (hg : ∀ t s, g t = .ok s → g' t = .ok s) {fs : List Field} {ms : List Shape}
    (h : fieldShapes g fs = .ok ms) : fieldShapes g' fs = .ok ms := by
  induction fs generalizing ms with
  | nil => exact h
  | cons f fs ih =>
    simp only [fieldShapes] at h ⊢
    split at h; · cases h
    rename_i hb
    simp only [hb, Bool.false_eq_true, ite_false]
    split at h; · cases h
    rename_i s hs
    rw [hg _ _ hs]
    split at h; · cases h
    rename_i a ha
    simp only [ha]
    split at h; · cases h
    rename_i ss hss
    rw [ih hss]; exact h

theorem layoutTy_succ : ∀ (n : Nat) (t : CTy) (s : Shape),
    layoutTy dm env n t = .ok s → layoutTy dm env (n + 1) t = .ok s := by
  intro n
  induction n with
  | zero => intro t s h; simp [layoutTy] at h
  | succ n ih =>
    intro t s h
    cases t with
    | array e k =>
      simp only [layoutTy] at h ⊢
      split at h
      · rename_i s' hs'; rw [ih _ _ hs']; exact h
      · cases h
    | typedef _ t => exact ih t s h
    | struct tag =>
      simp only [layoutTy] at h ⊢
      split at h; · cases h
      split at h
      · rename_i ms hms; rw [fieldShapes_mono ih hms]; exact h
      · cases h
    | union tag =>
      simp only [layoutTy] at h ⊢
      split at h; · cases h
      split at h
      · rename_i ms hms; rw [fieldShapes_mono ih hms]; exact h
      · cases h
    | enum _ u => cases u <;> exact h
    | _ => exact h

theorem layoutTy_mono {n m : Nat} (hnm : n ≤ m) {t : CTy} {s : Shape}
    (h : layoutTy dm env n t = .ok s) : layoutTy dm env m t = .ok s := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact layoutTy_succ _ _ _ ih

/-- Typedefs only consume fuel. -/
theorem layoutTy_strip : ∀ (n : Nat) (t : CTy) (s : Shape), layoutTy dm env n t = .ok s →
    ∃ m ≤ n, layoutTy dm env m t.strip = .ok s := by
  intro n
  induction n with
  | zero => intro t s h; simp [layoutTy] at h
  | succ n ih =>
    intro t s h
    cases t with
    | typedef _ t =>
      obtain ⟨m, hm, h'⟩ := ih t s h
      exact ⟨m, by omega, by simpa [CTy.strip] using h'⟩
    | _ => exact ⟨n + 1, Nat.le_refl _, by simpa [CTy.strip] using h⟩

/-! ## Members of computed layouts -/

theorem fieldShapes_getElem {g : CTy → Except String Shape} {fs : List Field} {ms : List Shape}
    (h : fieldShapes g fs = .ok ms) (i : Nat) (h1 : i < fs.length) (h2 : i < ms.length) :
    ∃ s, g fs[i].ty = .ok s ∧ ms[i].size = s.size ∧ (Pow2 s.align → s.align ∣ ms[i].align) := by
  induction fs generalizing ms i with
  | nil => simp at h1
  | cons f fs ih =>
    simp only [fieldShapes] at h
    split at h; · cases h
    split at h; · cases h
    rename_i s hs
    split at h; · cases h
    rename_i a ha
    split at h; · cases h
    rename_i ss hss
    cases h
    cases i with
    | zero =>
      refine ⟨s, hs, rfl, fun hp => ?_⟩
      cases hal : f.alignas with
      | none => simp only [hal, memberAlign] at ha; cases ha; exact Nat.dvd_refl _
      | some b =>
        simp only [hal, memberAlign] at ha
        split at ha
        · cases ha
          exact Pow2.dvd_of_le hp (Pow2.max hp (pow2_of_isPow2 (by assumption)))
            (Nat.le_max_left _ _)
        · cases ha
    | succ i => exact ih hss i (by simpa using h1) (by simpa using h2)

theorem place_getElem (off : Nat) (ms : List Shape) (i : Nat) (h1 : i < (place off ms).length)
    (h2 : i < ms.length) :
    (place off ms)[i].size = ms[i].size ∧ (place off ms)[i].align = ms[i].align := by
  induction ms generalizing off i with
  | nil => simp at h2
  | cons s ss ih =>
    cases i with
    | zero => simp [place]
    | succ i =>
      simp only [place, List.getElem_cons_succ]
      exact ih _ i _ (by simpa using h2)

theorem kindPlace_getElem (k : Kind) (ms : List Shape) (i : Nat)
    (h1 : i < (kindPlace k ms).2.length) (h2 : i < ms.length) :
    (kindPlace k ms).2[i].size = ms[i].size ∧ (kindPlace k ms).2[i].align = ms[i].align := by
  cases k with
  | struct => exact place_getElem 0 ms i h1 h2
  | union => simp [kindPlace, unionPlace]

/-- A member of a computed layout has the size of its type's layout, and the type's alignment
divides the member's. -/
theorem declLayout_field (hdm : dm.WF) {d : Decl} {L : DeclLayout}
    (h : declLayout dm env d = .ok L) {f : PlacedField} (hf : f ∈ L.fields) :
    ∃ s, layoutTy dm env defaultFuel f.ty = .ok s ∧ f.size = s.size ∧ s.align ∣ f.align := by
  simp only [declLayout] at h
  split at h
  · cases h
  rename_i ms hms
  cases h
  have hlen := fieldShapes_length hms
  simp only [List.mem_map] at hf
  obtain ⟨⟨fd, sl⟩, hmem, rfl⟩ := hf
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
  rw [List.getElem_zip] at he
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hi1 : i < d.fields.length := by simp at hi; omega
  have hi2 : i < ms.length := by omega
  obtain ⟨s, hs, hsz, hal⟩ := fieldShapes_getElem hms i hi1 hi2
  have hpow := (layoutTy_wf hdm env _ _ _ hs).pow2
  have hslot := kindPlace_getElem d.kind ms i (by simp at hi; omega) hi2
  refine ⟨s, hs, ?_, ?_⟩
  · simp only; rw [hslot.1, hsz]
  · simp only; rw [hslot.2]; exact hal hpow

/-! ## Designators -/

theorem Env.find?_kind {k : Kind} {tag : String} {d : Decl} (h : env.find? k tag = some d) :
    d.kind = k := by
  have := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

/-- The struct or union type of a tag. -/
def tagTy : Kind → String → CTy
  | .struct, tag => .struct tag
  | .union, tag => .union tag

theorem strip_strip (t : CTy) : t.strip.strip = t.strip := by
  induction t <;> simp [CTy.strip, *]

theorem layoutTy_strip_eq {t : CTy} {s : Shape}
    (h : layoutTy dm env defaultFuel t = .ok s) {k : Kind} {tag : String}
    (hk : t.strip = tagTy k tag)
    {L : DeclLayout} (hL : tagLayout dm env k tag = .ok L) : L.shape = s := by
  obtain ⟨m, hm, h'⟩ := layoutTy_strip _ _ _ h
  rw [hk] at h'
  simp only [tagLayout] at hL
  split at hL; · cases hL
  rename_i d hd
  simp only [declLayout] at hL
  split at hL; · cases hL
  rename_i ms hms
  cases hL
  cases m with
  | zero => simp [layoutTy] at h'
  | succ m =>
    cases k with
    | struct =>
      simp only [tagTy, layoutTy, hd] at h'
      split at h'
      · rename_i ms' hms'
        cases h'
        have := fieldShapes_mono
          (fun t s h => layoutTy_mono (show m ≤ defaultFuel by omega) h) hms'
        rw [hms] at this; cases this; simp only [Env.find?_kind hd, kindPlace]
      · cases h'
    | union =>
      simp only [tagTy, layoutTy, hd] at h'
      split at h'
      · rename_i ms' hms'
        cases h'
        have := fieldShapes_mono
          (fun t s h => layoutTy_mono (show m ≤ defaultFuel by omega) h) hms'
        rw [hms] at this; cases this; simp only [Env.find?_kind hd, kindPlace]
      · cases h'

/-- A designated subobject lies inside the object, at an offset its alignment divides, and its
alignment divides the object's. -/
theorem resolve_wf (hdm : dm.WF) : ∀ (p : List Step) (t : CTy) (o : Nat) (t' : CTy) (s' s : Shape),
    resolve dm env t p = .ok (o, t', s') → layoutTy dm env defaultFuel t = .ok s →
    o + s'.size ≤ s.size ∧ s'.align ∣ o ∧ s'.align ∣ s.align := by
  intro p
  induction p with
  | nil =>
    intro t o t' s' s h hs
    simp only [resolve, hs] at h
    cases h
    exact ⟨by omega, Nat.dvd_zero _, Nat.dvd_refl _⟩
  | cons st p ih =>
    intro t o t' s' s h hs
    cases st with
    | index i =>
      simp only [resolve] at h
      split at h
      · rename_i e n hstrip
        split at h
        · rename_i hi
          split at h
          · rename_i se o' t'' s'' hse hr
            cases h
            obtain ⟨m, hm, h'⟩ := layoutTy_strip _ _ _ hs
            rw [hstrip] at h'
            cases m with
            | zero => simp [layoutTy] at h'
            | succ m =>
              simp only [layoutTy] at h'
              split at h'
              · rename_i se' hse'
                cases h'
                have := layoutTy_mono (show m ≤ defaultFuel by omega) hse'
                rw [hse] at this; cases this
                obtain ⟨h1, h2, h3⟩ := ih e o' t' s' se hr hse
                have hwf := layoutTy_wf hdm env _ _ _ hse
                refine ⟨?_, ?_, h3⟩
                · have : i * se.size + se.size ≤ n * se.size := by
                    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
                  simp only; omega
                · exact Nat.dvd_add (Nat.dvd_trans h3 (Nat.dvd_trans hwf.dvd (Nat.dvd_mul_left _ _))) h2
              · cases h'
          · cases h
          · cases h
        · cases h
      · cases h
    | field name =>
      simp only [resolve] at h
      split at h
      · cases h
      rename_i k tag htag
      split at h; · cases h
      rename_i L hL
      split at h; · cases h
      rename_i f hf
      split at h
      · rename_i o' t'' s'' hr
        cases h
        have hstrip : t.strip = tagTy k tag := by
          generalize t.strip = u at htag
          cases u <;> simp at htag <;> (obtain ⟨rfl, rfl⟩ := htag; rfl)
        have hshape := layoutTy_strip_eq hs hstrip hL
        have hLwf : L.WF := by
          simp only [tagLayout] at hL
          split at hL; · cases hL
          exact declLayout_wf hdm hL
        have hfm := (DeclLayout.mem_of_field? hf).1
        have hdecl : ∃ d, declLayout dm env d = .ok L := by
          simp only [tagLayout] at hL
          split at hL; · cases hL
          exact ⟨_, hL⟩
        obtain ⟨d, hd⟩ := hdecl
        obtain ⟨sf, hsf, hsize, hal⟩ := declLayout_field hdm hd hfm
        obtain ⟨h1, h2, h3⟩ := ih f.ty o' t' s' sf hr hsf
        have hb := hLwf.inBounds f hfm
        have ha := hLwf.aligned f hfm
        have hd' := hLwf.alignDvd f hfm
        rw [hshape] at hb hd'
        refine ⟨by omega, ?_, ?_⟩
        · exact Nat.dvd_add (Nat.dvd_trans h3 (Nat.dvd_trans hal ha)) h2
        · exact Nat.dvd_trans h3 (Nat.dvd_trans hal hd')
      · cases h

end Silmaril.Proofs.Data.Layout

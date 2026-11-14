module

public import Silmaril.X86.Concurrency.Cir.Refute.Defs
public import Silmaril.X86.MemoryModel.Axiomatic.Thms

/-!
# Refutation by forced cycles: soundness

Every forced edge of `Cir.Refute.edges` is an edge of `ghbXl` in every
well-formed XL-consistent candidate whose key-byte sources are the chosen ones; a cycle of
forced edges therefore contradicts XL (`refuteCombo_sound`). `safe_of_check` lifts this to
`AxReach`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Refute

open Relation
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Test XTrace units seqL Final finalOf dummyEv Cond Atom Byte
  AxReach ReadsOk finalAx writtenByte leValue)
open Silmaril.X86.Concurrency.Cir.Refute

/-! ## Lists -/

theorem before_total : ∀ (l : List Nat) {a b : Nat}, a ∈ l → b ∈ l → a ≠ b →
    before l a b = true ∨ before l b a = true
  | [], _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | c :: l, a, b, ha, hb, hab => by
    simp only [before, beq_iff_eq]
    by_cases hca : c = a
    · subst hca
      left
      simp only [ite_true]
      rcases List.mem_cons.mp hb with h | h
      · exact absurd h.symm hab
      · exact List.contains_iff_mem.mpr h
    · by_cases hcb : c = b
      · subst hcb
        right
        simp only [ite_true]
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hca
        · exact List.contains_iff_mem.mpr h
      · simp only [hca, hcb, ite_false]
        exact before_total l (List.mem_of_ne_of_mem (Ne.symm hca) ha)
          (List.mem_of_ne_of_mem (Ne.symm hcb) hb) hab

theorem eq_single_of_nodup : ∀ {l : List Nat} {w : Nat}, l.Nodup → (∀ z ∈ l, z = w) → w ∈ l →
    l = [w]
  | [], _, _, _, h => absurd h List.not_mem_nil
  | a :: l, w, hn, hall, _ => by
    have ha : a = w := hall a (List.mem_cons_self ..)
    subst ha
    cases l with
    | nil => rfl
    | cons b l =>
      have hb : b = a := hall b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      subst hb
      exact absurd (List.mem_cons_self ..) (List.nodup_cons.mp hn).1

theorem mem_seqL_map {α β : Type} (g : β → List α) (f : β → α) :
    ∀ (l : List β), (∀ a ∈ l, f a ∈ g a) → l.map f ∈ seqL (l.map g)
  | [], _ => by simp [seqL]
  | a :: l, h => by
    simp only [List.map_cons, seqL, List.mem_flatMap, List.mem_map]
    exact ⟨f a, h a (List.mem_cons_self ..), l.map f,
      mem_seqL_map g f l (fun b hb => h b (List.mem_cons_of_mem _ hb)), rfl⟩

theorem mem_seqL_of_forall₂ {α : Type} : ∀ {l : List α} {L : List (List α)},
    List.Forall₂ (· ∈ ·) l L → l ∈ seqL L
  | [], [], _ => by simp [seqL]
  | a :: l, A :: L, h => by
    cases h with
    | cons h₁ h₂ =>
      simp only [seqL, List.mem_flatMap, List.mem_map]
      exact ⟨a, h₁, l, mem_seqL_of_forall₂ h₂, rfl⟩

theorem mem_zip_map {α β : Type} (f : α → β) : ∀ (l : List α) {p : α × β},
    p ∈ l.zip (l.map f) → p.1 ∈ l ∧ p.2 = f p.1
  | [], _, h => by simp at h
  | a :: l, p, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨List.mem_cons_self .., rfl⟩
    · have := mem_zip_map f l h
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

/-! ## Cycles -/

/-- The edge relation of a list. -/
def ER (E : List (Nat × Nat)) (a b : Nat) : Prop := (a, b) ∈ E

theorem mem_succs {E : List (Nat × Nat)} {a b : Nat} (h : b ∈ succs E a) : ER E a b := by
  simp only [succs, List.mem_filterMap] at h
  obtain ⟨p, hp, hq⟩ := h
  by_cases h1 : p.1 = a
  · simp only [h1, beq_self_eq_true, ite_true, Option.some.injEq] at hq
    subst hq; subst h1; exact hp
  · simp [beq_iff_eq, h1] at hq

theorem mem_addNew : ∀ (l : List Nat) {S : List Nat} {b : Nat}, b ∈ addNew S l → b ∈ S ∨ b ∈ l
  | [], S, b, h => by simp [addNew] at h; exact .inl h
  | c :: l, S, b, h => by
    simp only [addNew, List.foldl_cons] at h
    have := mem_addNew l (S := if S.contains c then S else S ++ [c]) h
    rcases this with h | h
    · split at h
      · exact .inl h
      · rcases List.mem_append.mp h with h | h
        · exact .inl h
        · simp at h; exact .inr (h ▸ List.mem_cons_self ..)
    · exact .inr (List.mem_cons_of_mem _ h)

theorem grow_sound (E : List (Nat × Nat)) (a : Nat) : ∀ (k : Nat) (S : List Nat),
    (∀ b ∈ S, TransGen (ER E) a b) → ∀ b ∈ grow E k S, TransGen (ER E) a b
  | 0, S, h => by simpa [grow] using h
  | k + 1, S, h => by
    simp only [grow]
    split
    · exact h
    · apply grow_sound E a k
      intro b hb
      rcases mem_addNew _ hb with hb | hb
      · exact h b hb
      · simp only [List.mem_flatMap] at hb
        obtain ⟨c, hc, hcb⟩ := hb
        exact .tail (h c hc) (mem_succs hcb)

theorem hasCycle_sound {E : List (Nat × Nat)} {n : Nat} {starts : List Nat}
    (h : hasCycle E n starts = true) : ∃ a, TransGen (ER E) a a := by
  simp only [hasCycle, List.any_eq_true] at h
  obtain ⟨a, _, ha⟩ := h
  exact ⟨a, grow_sound E a n _ (fun b hb => .single (mem_succs hb)) a
    (List.contains_iff_mem.mp ha)⟩

theorem transGen_fin {E : List (Nat × Nat)} {n : Nat} {G : BRel n}
    (h : ∀ a b, ER E a b → ∃ (ha : a < n) (hb : b < n), G ⟨a, ha⟩ ⟨b, hb⟩ = true) {a b : Nat}
    (hab : TransGen (ER E) a b) : ∃ (ha : a < n) (hb : b < n), TransGen G.Holds ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction hab with
  | single h1 =>
    obtain ⟨ha, hb, hg⟩ := h _ _ h1
    exact ⟨ha, hb, .single hg⟩
  | tail _ h2 ih =>
    obtain ⟨ha, hc, ih⟩ := ih
    obtain ⟨hc', hb, hg⟩ := h _ _ h2
    exact ⟨ha, hb, .tail ih hg⟩

/-! ## Units of a candidate -/

section Exec
variable {x : Exec}

theorem evAt_eq (x : Exec) (i : Nat) : evAt x.evs i = x.evN i := rfl

theorem evN_fin (x : Exec) (a : Fin x.n) : x.evN a.val = x.ev a := by
  simp [Exec.evN, Exec.ev, List.getD_eq_getElem?_getD]

theorem evN_eq (x : Exec) {i : Nat} (h : i < x.n) : x.evN i = x.ev ⟨i, h⟩ := evN_fin x ⟨i, h⟩

theorem covers_iff (e : Ev) (y : Nat) : e.covers y = true ↔ y ∈ e.bytes := by
  simp [Ev.covers, Ev.bytes, List.mem_range']
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨y - e.addr, by omega, by omega⟩
  · rintro ⟨i, h1, rfl⟩; omega

/-- The parts of well-formedness used here. -/
structure WfParts (x : Exec) : Prop where
  rf : ∀ r : Fin x.n, (x.ev r).isR = true → ∀ y ∈ (x.ev r).bytes, ∀ w, x.rf r.val y = some w →
    w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true
  co : ∀ y ∈ x.touched, (x.co y).Nodup ∧
    (∀ w ∈ x.co y, w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true) ∧
    ∀ w : Fin x.n, (x.ev w).isW = true → (x.ev w).covers y = true → w.val ∈ x.co y
  size : ∀ e ∈ x.evs, e.isM = true → 0 < e.size

theorem wfParts (h : x.Wf = true) : WfParts x := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro r hr y hy w hw
    have := h1 r (List.mem_finRange r)
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at this
    rcases this with h | h
    · simp [hr] at h
    · have := h y hy
      rw [hw] at this
      simp only [Bool.and_eq_true, Exec.valid, decide_eq_true_eq] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
  · intro y hy
    have := h2 y hy
    simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at this
    obtain ⟨⟨hn, ha⟩, hc⟩ := this
    refine ⟨hn, fun w hw => ?_, fun w hw hcv => ?_⟩
    · have := ha w hw
      simp only [Exec.valid, decide_eq_true_eq] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    · rcases hc w (List.mem_finRange w) with h | h
      · simp [hw, hcv] at h
      · exact List.contains_iff_mem.mp h
  · intro e he hm
    have := h5 e he
    simp only [hm, ite_true, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1

theorem addr_mem_bytes {e : Ev} (h : 0 < e.size) : e.addr ∈ e.bytes := by
  rw [Ev.bytes, List.mem_range']; exact ⟨0, h, by simp⟩

theorem mem_touched {w : Fin x.n} (hw : (x.ev w).isW = true) {y : Nat}
    (hy : (x.ev w).covers y = true) : y ∈ x.touched := by
  simp only [Exec.touched, List.mem_flatMap, List.mem_filter]
  refine ⟨x.ev w, ⟨List.getElem_mem .., ?_⟩, (covers_iff _ _).mp hy⟩
  simp [Ev.isM, hw]

theorem size_pos (hw : WfParts x) (a : Fin x.n) (hm : (x.ev a).isM = true) : 0 < (x.ev a).size :=
  hw.size _ (List.getElem_mem ..) hm

theorem isM_of_isR {e : Ev} (h : e.isR = true) : e.isM = true := by simp [Ev.isM, h]
theorem isM_of_isW {e : Ev} (h : e.isW = true) : e.isM = true := by simp [Ev.isM, h]

theorem not_isR_of_isW {e : Ev} (h : e.isW = true) : e.isR = false := by
  simp only [Ev.isW, Ev.isR, beq_iff_eq] at h ⊢; simp [h]

/-! ## Forced coherence -/

theorem uniprocXl_cycle (hX : x.Xl) {v w : Fin x.n} (h1 : x.uniprocXl v w = true)
    (h2 : x.uniprocXl w v = true) : False :=
  hX.2.1 v (.tail (.single h1) h2)

theorem smT_refl (a : Fin x.n) : x.smT a a = true := by simp [Exec.smT]

theorem comSmT {a b : Fin x.n} (h : x.com a b = true) : (x.com.seq x.smT) a b = true := by
  simp only [BRel.seq, List.any_eq_true]
  exact ⟨b, List.mem_finRange b, by simp [h, smT_refl]⟩

/-- **Forced coherence**: in an XL-consistent candidate, two writes of one thread to a byte are
in program order in its coherence order. -/
theorem before_of_coF (hw : WfParts x) (hX : x.Xl) {y : Nat} {v w : Fin x.n}
    (h : coF x.evs y v.val w.val = true) : before (x.co y) v.val w.val = true := by
  simp only [coF, evAt_eq, evN_fin, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hvW, hwW⟩, hvy⟩, hwy⟩, htid⟩, hpos⟩ := h
  have hy := mem_touched hwW hwy
  obtain ⟨hn, _, hall⟩ := hw.co y hy
  have hvm := hall v hvW hvy
  have hwm := hall w hwW hwy
  have hne : v.val ≠ w.val := by
    intro he; have : v = w := Fin.ext he; subst this; omega
  rcases before_total _ hvm hwm hne with h | h
  · exact h
  · exfalso
    apply uniprocXl_cycle hX (v := v) (w := w)
    · simp only [Exec.uniprocXl, BRel.union, Bool.or_eq_true]
      left
      simp only [Exec.poLoc, BRel.inter, Exec.po, Exec.loc, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq, List.any_eq_true]
      exact ⟨⟨htid, hpos⟩, ⟨isM_of_isW hvW, isM_of_isW hwW⟩, y, (covers_iff _ _).mp hvy, hwy⟩
    · simp only [Exec.uniprocXl, BRel.union, Bool.or_eq_true]
      right
      apply comSmT
      simp only [Exec.com, BRel.union, Bool.or_eq_true, Exec.coR, Bool.and_eq_true,
        List.any_eq_true]
      exact .inr (.inl ⟨⟨hwW, hvW⟩, y, (covers_iff _ _).mp hwy, hvy, h⟩)

/-! ## Forced edges are `ghbXl` edges -/

theorem ghbXl_of_ppoXl {a b : Fin x.n} (h : x.ppoXl a b = true) : x.ghbXl a b = true := by
  simp [Exec.ghbXl, BRel.union, h]

theorem ghbXl_of_part {a b : Fin x.n} (h : (x.rfe.union (x.frR.union x.coR)) a b = true) :
    x.ghbXl a b = true := by
  have : x.comGhbXl a b = true := by
    simp only [Exec.comGhbXl, BRel.seq, List.any_eq_true]
    exact ⟨b, List.mem_finRange b, by simp [h, smT_refl]⟩
  simp [Exec.ghbXl, BRel.union, this]

theorem ppoE_iff (a b : Fin x.n) : ppoE (x.ev a) (x.ev b) = x.ppoXl a b := by
  simp only [ppoE, Exec.ppoXl, Exec.ppo, Exec.po]

/-- A read's key-byte source and the forced edges out of it. -/
theorem readEdges_ghbXl (hw : WfParts x) (hX : x.Xl) {r : Nat} (hr : r < x.n)
    (hR : (x.evN r).isR = true) {p : Nat × Nat}
    (h : p ∈ readEdges x.evs r (x.rf r (key x.evs r))) :
    ∃ (ha : p.1 < x.n) (hb : p.2 < x.n), x.ghbXl ⟨p.1, ha⟩ ⟨p.2, hb⟩ = true := by
  have hR' : (x.ev ⟨r, hr⟩).isR = true := by rwa [← evN_fin]
  have hsz := size_pos hw ⟨r, hr⟩ (isM_of_isR hR')
  have hkey : key x.evs r ∈ (x.ev ⟨r, hr⟩).bytes := by
    simp only [key, evAt_eq, evN_eq x hr]; exact addr_mem_bytes hsz
  simp only [readEdges, List.mem_append, List.mem_map, List.mem_filter, List.mem_range] at h
  rcases h with h | ⟨w, ⟨hwn, hc⟩, he⟩
  · -- rfe
    split at h
    · rename_i w hsrc
      split at h
      · rename_i hext
        simp only [List.mem_singleton] at h
        subst h
        obtain ⟨hwn, hwW, hwc⟩ := hw.rf ⟨r, hr⟩ hR' _ hkey w hsrc
        refine ⟨hwn, hr, ghbXl_of_part ?_⟩
        simp only [BRel.union, Bool.or_eq_true]
        left
        simp only [Exec.rfe, BRel.inter, Exec.rfR, Exec.ext, Bool.and_eq_true, List.any_eq_true,
          beq_iff_eq]
        rw [← evN_fin x ⟨w, hwn⟩, ← evN_fin x ⟨r, hr⟩]
        refine ⟨⟨⟨hwW, hR⟩, key x.evs r, by rwa [evN_fin], hsrc, hwc⟩, ?_⟩
        simpa [evAt_eq] using hext
      · simp at h
    · simp at h
  · -- fr
    subst he
    simp only [Bool.and_eq_true, evAt_eq] at hc
    obtain ⟨⟨hwW, hwc⟩, hs⟩ := hc
    refine ⟨hr, hwn, ghbXl_of_part ?_⟩
    simp only [BRel.union, Bool.or_eq_true]
    right; left
    simp only [Exec.frR, Bool.and_eq_true, List.any_eq_true]
    rw [← evN_fin x ⟨w, hwn⟩, ← evN_fin x ⟨r, hr⟩]
    refine ⟨⟨hR, hwW⟩, key x.evs r, by rwa [evN_fin], hwc, ?_⟩
    revert hs
    cases hsrc : x.rf r (key x.evs r) with
    | none => intro; rfl
    | some v =>
      intro hs
      obtain ⟨hvn, _, _⟩ := hw.rf ⟨r, hr⟩ hR' _ hkey v hsrc
      exact before_of_coF hw hX (v := ⟨v, hvn⟩) (w := ⟨w, hwn⟩) hs

/-- The key-byte source of a read is one of `srcs`. -/
theorem rf_mem_srcs (hw : WfParts x) {t : Test} {exps : List (List Byte)} (hro : ReadsOk t x exps)
    {r : Nat} (hr : r < x.n) (hR : (x.evN r).isR = true) :
    x.rf r (key x.evs r) ∈ srcs t x.evs exps r := by
  have hR' : (x.ev ⟨r, hr⟩).isR = true := by rwa [← evN_fin]
  have hsz := size_pos hw ⟨r, hr⟩ (isM_of_isR hR')
  have hkey : key x.evs r ∈ (x.ev ⟨r, hr⟩).bytes := by
    simp only [key, evAt_eq, evN_eq x hr]; exact addr_mem_bytes hsz
  have hb : expB exps r = x.readByte t.initB r (key x.evs r) := by
    have := hro r hr hR
    simp only [Exec.readBytes] at this
    simp only [expB, ← this]
    rw [evN_fin x ⟨r, hr⟩]
    have : (x.ev ⟨r, hr⟩).bytes = (x.ev ⟨r, hr⟩).addr :: List.range' ((x.ev ⟨r, hr⟩).addr + 1)
        ((x.ev ⟨r, hr⟩).size - 1) := by
      simp only [Ev.bytes]
      conv => lhs; rw [show (x.ev ⟨r, hr⟩).size = ((x.ev ⟨r, hr⟩).size - 1) + 1 by omega]
      rfl
    rw [this]
    simp [key, evAt_eq, evN_eq x hr]
  simp only [srcs, List.mem_append, List.mem_map, List.mem_filter, List.mem_range]
  cases hsrc : x.rf r (key x.evs r) with
  | none =>
    left
    have : expB exps r = t.initB (key x.evs r) := by simp [hb, Exec.readByte, hsrc]
    simp [this]
  | some w =>
    right
    obtain ⟨hwn, hwW, hwc⟩ := hw.rf ⟨r, hr⟩ hR' _ hkey w hsrc
    refine ⟨w, ⟨hwn, ?_⟩, rfl⟩
    have : expB exps r = (x.evN w).byte (key x.evs r) := by simp [hb, Exec.readByte, hsrc]
    simp [evAt_eq, hwW, hwc, this]

/-- **A refuted choice of traces has no XL-consistent well-formed candidate.** -/
theorem refuteCombo_sound {t : Test} {trs : List XTrace} (h : refuteCombo t trs = true)
    {x : Exec} (hx : x.evs = (units trs).map Prod.fst) (hW : x.Wf = true)
    (hro : ReadsOk t x ((units trs).map Prod.snd)) (hX : x.Xl) : False := by
  have hw := wfParts hW
  simp only [refuteCombo, List.all_eq_true] at h
  rw [← hx] at h
  let f := fun r => x.rf r (key x.evs r)
  have hc := h ((readIdx x.evs).map f) (mem_seqL_map _ f _ fun r hr => by
    simp only [readIdx, List.mem_filter, List.mem_range, evAt_eq] at hr
    exact rf_mem_srcs hw hro hr.1 hr.2)
  obtain ⟨a, ha⟩ := hasCycle_sound hc
  have hE : ∀ a b, ER (edges x.evs ((readIdx x.evs).zip ((readIdx x.evs).map f))) a b →
      ∃ (ha : a < x.n) (hb : b < x.n), x.ghbXl ⟨a, ha⟩ ⟨b, hb⟩ = true := by
    intro a b hab
    simp only [ER, edges, List.mem_append, List.mem_flatMap] at hab
    rcases hab with hab | ⟨p, hp, hab⟩
    · simp only [ppoEdges, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
        Prod.mk.injEq] at hab
      obtain ⟨a', ha', b', ⟨hb', hp⟩, rfl, rfl⟩ := hab
      refine ⟨ha', hb', ghbXl_of_ppoXl ?_⟩
      rw [← ppoE_iff, ← evN_fin, ← evN_fin]; exact hp
    · obtain ⟨hp1, hp2⟩ := mem_zip_map f _ hp
      simp only [readIdx, List.mem_filter, List.mem_range, evAt_eq] at hp1
      rw [hp2] at hab
      exact readEdges_ghbXl hw hX hp1.1 hp1.2 (p := (a, b)) hab
  obtain ⟨ha1, _, hcyc⟩ := transGen_fin hE ha
  exact hX.2.2.2 _ hcyc

/-! ## Final memory -/

theorem mem_writers {evs : List Ev} {y w : Nat} :
    w ∈ writers evs y ↔ w < evs.length ∧ (evAt evs w).isW = true ∧ (evAt evs w).covers y = true := by
  simp [writers, Bool.and_eq_true]

theorem finalAx_mem {t : Test} {trs : List XTrace} (hW : x.Wf = true) {y : Nat}
    {v : Option Byte} (hg : guess t x.evs y = some v) : (finalAx t trs x).mem y = v := by
  have hw := wfParts hW
  simp only [finalAx, finalOf]
  simp only [guess] at hg
  split at hg
  · rename_i hnil
    simp only [Option.some.injEq] at hg
    subst hg
    have : writtenByte x y = false := by
      simp only [writtenByte, List.any_eq_false, Bool.and_eq_true, not_and]
      intro e he hwe hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      have : i ∈ writers x.evs y := mem_writers.mpr ⟨hi, by
        simp [evAt_eq, Exec.evN, List.getD_eq_getElem?_getD, hi, hwe], by
        simp [evAt_eq, Exec.evN, List.getD_eq_getElem?_getD, hi, hc]⟩
      rw [hnil] at this; simp at this
    simp [this]
  · rename_i w hone
    simp only [Option.some.injEq] at hg
    subst hg
    have hwm : w ∈ writers x.evs y := by rw [hone]; exact List.mem_singleton_self _
    obtain ⟨hwn, hwW, hwc⟩ := mem_writers.mp hwm
    rw [evAt_eq, evN_eq x hwn] at hwW hwc
    have hwr : writtenByte x y = true := by
      simp only [writtenByte, List.any_eq_true, Bool.and_eq_true]
      exact ⟨_, List.getElem_mem hwn, hwW, hwc⟩
    have hy := mem_touched hwW hwc
    obtain ⟨hn, hall, hcon⟩ := hw.co y hy
    have hco : x.co y = [w] := eq_single_of_nodup hn (fun z hz => by
      obtain ⟨hzn, hzW, hzc⟩ := hall z hz
      have : z ∈ writers x.evs y := mem_writers.mpr ⟨hzn, hzW, hzc⟩
      rw [hone] at this; simpa using this) (hcon _ hwW hwc)
    simp [hwr, Exec.finalByte, hco, evAt_eq]
  · simp at hg

theorem leValue_congr {m m' : Nat → Option Byte} : ∀ (n a : Nat),
    (∀ y ∈ List.range' a n, m y = m' y) → leValue m a n = leValue m' a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [leValue]
    rw [h a (by simp [List.mem_range']), leValue_congr n (a + 1) (fun y hy => h y (by
      simp only [List.mem_range'] at hy ⊢; obtain ⟨i, hi, rfl⟩ := hy; exact ⟨i + 1, by omega, by omega⟩))]

theorem cond_congr {f g : Final} (hr : f.regs = g.regs) :
    ∀ (p : Cond), (∀ y ∈ condBytes p, f.mem y = g.mem y) → p.eval f = p.eval g
  | .tt, _ => rfl
  | .atom (.reg ..), _ => by simp [Cond.eval, Atom.eval, hr]
  | .atom (.mem a n v), h => by
    simp only [Cond.eval, Atom.eval]
    rw [leValue_congr n a h]
  | .not p, h => by simp only [Cond.eval]; rw [cond_congr hr p h]
  | .and p q, h => by
    simp only [Cond.eval]
    rw [cond_congr hr p (fun y hy => h y (List.mem_append_left _ hy)),
      cond_congr hr q (fun y hy => h y (List.mem_append_right _ hy))]
  | .or p q, h => by
    simp only [Cond.eval]
    rw [cond_congr hr p (fun y hy => h y (List.mem_append_left _ hy)),
      cond_congr hr q (fun y hy => h y (List.mem_append_right _ hy))]

end Exec

/-- **The safety check is sound under XL.** -/
theorem safe_of_check {t : Test} {T : List (List XTrace)} {good : Cond}
    (h : safeCheck t T good = true) {f : Final} (hf : AxReach t T Exec.Xl f) :
    good.eval f = true := by
  obtain ⟨trs, htrs, x, hx, _, hW, hro, hX, rfl⟩ := hf
  simp only [safeCheck, List.all_eq_true] at h
  rcases Bool.or_eq_true_iff.mp (h trs (mem_seqL_of_forall₂ htrs)) with hg | hr
  · simp only [goodCombo, Bool.and_eq_true, List.all_eq_true] at hg
    obtain ⟨hk, he⟩ := hg
    rw [← hx] at hk he
    rw [← he]
    refine cond_congr (f := finalAx t trs x) (g := finalOf trs fun y => (guess t x.evs y).getD none) rfl good (fun y hy => ?_)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hk y hy)
    rw [finalAx_mem hW hv]
    simp [finalOf, hv]
  · exact (refuteCombo_sound hr hx hW hro hX).elim

/-! ## Witnesses -/

theorem forall₂_of_mapM {α : Type} : ∀ {T : List (List α)} {ks : List Nat} {trs : List α},
    T.length = ks.length → (T.zip ks).mapM (fun p => p.1[p.2]?) = some trs →
      List.Forall₂ (· ∈ ·) trs T
  | [], [], trs, _, h => by simp at h; subst h; exact .nil
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | A :: T, k :: ks, trs, hl, h => by
    simp only [List.zip_cons_cons, List.mapM_cons, Option.bind_eq_bind] at h
    cases ha : A[k]? with
    | none => simp [ha] at h
    | some a =>
      cases hr : (T.zip ks).mapM (fun p => p.1[p.2]?) with
      | none => simp [ha, hr] at h
      | some rest =>
        simp [ha, hr] at h
        subst h
        exact .cons (List.mem_of_getElem? ha) (forall₂_of_mapM (by simpa using hl) hr)

theorem readsOk_of_B {t : Test} {x : Exec} {exps : List (List Byte)}
    (h : Silmaril.X86.MemoryModel.Litmus.readsOkB t x exps = true) : ReadsOk t x exps := by
  intro r hr hR
  simp only [Silmaril.X86.MemoryModel.Litmus.readsOkB, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  rcases h r hr with h | h
  · simp [hR] at h
  · exact h

/-- **A passing witness check gives an SC behaviour satisfying the condition.** -/
theorem witness_sound {t : Test} {T : List (List XTrace)} {ks : List Nat}
    {rfA : List (Nat × Option Nat)} {coA : List ((Nat × Nat) × List Nat)} {w : Cond}
    (h : witnessCheck t T ks rfA coA w = true) :
    ∃ f, AxReach t T Exec.Sc f ∧ w.eval f = true := by
  unfold witnessCheck at h
  split at h
  · rename_i trs htrs
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hl, hW⟩, hro⟩, hsc⟩, hw⟩ := h
    exact ⟨_, ⟨trs, forall₂_of_mapM hl htrs, _, rfl, rfl, hW, readsOk_of_B hro, hsc, rfl⟩, hw⟩
  · simp at h

end Silmaril.Proofs.X86.Concurrency.Cir.Refute

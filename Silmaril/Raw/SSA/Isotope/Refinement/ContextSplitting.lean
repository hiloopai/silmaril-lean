module

public import Silmaril.Raw.SSA.Isotope.Refinement.Weakening

@[expose] public section

noncomputable section

namespace Silmaril.Isotope.Refinement.QCtx

universe u
variable {τ : Type u} [HasQuantity τ] {n : Nat}

omit [HasQuantity τ] in
theorem exists_snoc_type (Γ : QCtx τ (n + 1)) (A : τ) (h : (Γ 0).1 = A) :
    ∃ (Δ : QCtx τ n) (q : Usage), Γ = Δ.snoc A q := by
  refine ⟨(fun i => Γ i.succ), (Γ 0).2, ?_⟩
  rw [← h]
  exact (snoc_tail Γ).symm

theorem linearity_tail_top {Γ : QCtx τ n} {A : τ} {q : Usage}
    (h : (Γ.snoc A q).linearity = ⊤) : Γ.linearity = ⊤ := by
  apply top_le_iff.mp
  apply le_linearity_iff.mpr
  intro i
  rw [← h]
  exact (le_linearity_iff.mp le_rfl) i.succ

theorem quantity_top_of_snoc_linearity_top {Γ : QCtx τ n} {A : τ} {q : Quantity}
    (h : (Γ.snoc A (.used q)).linearity = ⊤) : q = ⊤ := by
  have hh : (Γ.snoc A (.used q)).linearity ≤ Usage.linearity (.used q) (quantity A) :=
    (le_linearity_iff.mp le_rfl) 0
  have hq : Usage.linearity (.used q) (quantity A) ≤ q := inf_le_right
  rw [h] at hh
  exact top_le_iff.mp (hh.trans hq)

/-- Keep the types of all slots, marking every variable unused. -/
def zero (Γ : QCtx τ n) : QCtx τ n := fun i => ((Γ i).1, .zero)

theorem zero_discardable (Γ : QCtx τ n) : Γ.zero.Discardable := fun _ => le_rfl

@[simp] theorem zero_linearity (Γ : QCtx τ n) : Γ.zero.linearity = ⊤ := by
  apply top_le_iff.mp
  exact le_linearity_iff.mpr fun _ => le_rfl

theorem Split.zero_right (Γ : QCtx τ n) : Γ.Split Γ Γ.zero := fun _ => ⟨rfl, rfl, .left _⟩
theorem Split.zero_left (Γ : QCtx τ n) : Γ.Split Γ.zero Γ := (Split.zero_right Γ).symm

theorem discardable_iff_linearity {Γ : QCtx τ n} :
    Γ.Discardable ↔ Quantity.affine ≤ Γ.linearity := by
  rw [le_linearity_iff]
  exact forall_congr' fun _ => Usage.zero_le_effective_iff _ _

/-- Pointwise effective allowance comparison realizes an identity renaming. -/
theorem Weakening.ofPointwise {Γ Δ : QCtx τ n}
    (ht : ∀ i, (Δ i).1 = (Γ i).1) (hq : ∀ i, Δ.effective i ≤ Γ.effective i) :
    Weakening Γ Δ id := by
  induction n with
  | zero =>
    have hΓ : Γ = QCtx.nil := funext (fun i => Fin.elim0 i)
    have hΔ : Δ = QCtx.nil := funext (fun i => Fin.elim0 i)
    subst Γ
    subst Δ
    exact .refl QCtx.nil
  | succ n ih =>
    have htail := ih (fun i => ht i.succ) (fun i => hq i.succ)
    have hhead : Usage.effective (Δ 0).2 (quantity (Γ 0).1) ≤
        Usage.effective (Γ 0).2 (quantity (Γ 0).1) := by
      simpa only [effective, ht 0] using hq 0
    have h := Weakening.cons htail hhead
    rw [snoc_tail Γ] at h
    have hd : snoc (fun i => Δ i.succ) (Γ 0).1 (Δ 0).2 = Δ := by
      rw [← ht 0]
      exact snoc_tail Δ
    rw [hd] at h
    convert h using 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem SlotSplit.effective_right_le {A : τ} {q ql qr : Usage} (h : SlotSplit A q ql qr)
    (hd : Usage.zero ≤ Usage.effective ql (quantity A)) :
    Usage.effective qr (quantity A) ≤ Usage.effective q (quantity A) := by
  cases h with
  | left => exact hd
  | right => exact le_rfl
  | both => exact le_rfl

theorem Split.weakenRight {Γ Γl Γr : QCtx τ n} (h : Γ.Split Γl Γr)
    (hd : Γl.Discardable) : Weakening Γ Γr id := by
  apply Weakening.ofPointwise (fun i => (h i).2.1)
  intro i
  have hdi := hd i
  have hi := (h i).2.2
  simp only [effective, (h i).1] at hdi
  simp only [effective, (h i).2.1]
  exact hi.effective_right_le hdi

theorem Split.weakenLeft {Γ Γl Γr : QCtx τ n} (h : Γ.Split Γl Γr)
    (hd : Γr.Discardable) : Weakening Γ Γl id := h.symm.weakenRight hd

theorem SlotSplit.linearity {A : τ} {q ql qr : Usage} (h : SlotSplit A q ql qr) :
    Usage.linearity q (quantity A) =
      Usage.linearity ql (quantity A) ⊓ Usage.linearity qr (quantity A) := by
  cases h with
  | left => exact (inf_top_eq _).symm
  | right => exact (top_inf_eq _).symm
  | both => exact (inf_idem _).symm

theorem Split.le_linearity {Γ Γl Γr : QCtx τ n} (h : Γ.Split Γl Γr) {q : Quantity}
    (hl : q ≤ Γl.linearity) (hr : q ≤ Γr.linearity) : q ≤ Γ.linearity := by
  apply le_linearity_iff.mpr
  intro i
  obtain ⟨htl, htr, hs⟩ := h i
  rw [hs.linearity]
  apply le_inf
  · simpa only [htl] using (le_linearity_iff.mp hl) i
  · simpa only [htr] using (le_linearity_iff.mp hr) i

theorem SlotSplit.diagonal {A : τ} (q : Usage)
    (h : Quantity.relevant ≤ Usage.linearity q (quantity A)) : SlotSplit A q q q := by
  by_cases hz : q = .zero
  · subst q
    exact .left .zero
  · exact .both q ((Usage.relevant_le_effective_iff q (quantity A)).2 ⟨h, hz⟩)

theorem Split.diagonal (Γ : QCtx τ n) (h : Quantity.relevant ≤ Γ.linearity) : Γ.Split Γ Γ :=
  fun i => ⟨rfl, rfl, .diagonal _ ((le_linearity_iff.mp h) i)⟩

/-- Reassociate three resource groups while exchanging the last two. -/
theorem SlotSplit.swapAssoc {A : τ} {q qab qc qa qb : Usage}
    (h : SlotSplit A q qab qc) (k : SlotSplit A qab qa qb) :
    ∃ qac, SlotSplit A q qac qb ∧ SlotSplit A qac qa qc := by
  cases h with
  | left => exact ⟨qa, k, .left _⟩
  | right =>
    cases k with
    | left => exact ⟨q, .left q, .right q⟩
    | right => exact ⟨q, .left q, .right q⟩
    | both hc => exact False.elim hc
  | both hc =>
    cases k with
    | left => exact ⟨q, .left q, .both q hc⟩
    | right => exact ⟨q, .both q hc, .right q⟩
    | both => exact ⟨q, .both q hc, .both q hc⟩

theorem Split.swapAssoc {Γ Γab Γc Γa Γb : QCtx τ n}
    (h : Γ.Split Γab Γc) (k : Γab.Split Γa Γb) :
    ∃ Γac, Γ.Split Γac Γb ∧ Γac.Split Γa Γc := by
  have hs : ∀ i, ∃ qac, SlotSplit (Γ i).1 (Γ i).2 qac (Γb i).2 ∧
      SlotSplit (Γ i).1 qac (Γa i).2 (Γc i).2 := by
    intro i
    have ki := (k i).2.2
    rw [(h i).1] at ki
    exact (h i).2.2.swapAssoc ki
  let Γac : QCtx τ n := fun i => ((Γ i).1, Classical.choose (hs i))
  refine ⟨Γac, ?_, ?_⟩
  · intro i
    exact ⟨rfl, (k i).2.1.trans (h i).1, (Classical.choose_spec (hs i)).1⟩
  · intro i
    exact ⟨(k i).1.trans (h i).1, (h i).2.1, (Classical.choose_spec (hs i)).2⟩

theorem Split.assoc {Γ Γa Γbc Γb Γc : QCtx τ n}
    (h : Γ.Split Γa Γbc) (k : Γbc.Split Γb Γc) :
    ∃ Γab, Γ.Split Γab Γc ∧ Γab.Split Γa Γb := by
  obtain ⟨Γab, h, k⟩ := h.symm.swapAssoc k
  exact ⟨Γab, h, k.symm⟩

/-- A relevant resource group can be shared between both resulting contexts. -/
theorem Split.distribute {Γ Γab Γc Γa Γb : QCtx τ n}
    (h : Γ.Split Γab Γc) (k : Γab.Split Γa Γb)
    (hc : Quantity.relevant ≤ Γc.linearity) :
    ∃ Γac Γbc, Γ.Split Γac Γbc ∧ Γac.Split Γa Γc ∧ Γbc.Split Γb Γc := by
  obtain ⟨Γac, hp, ha⟩ := h.swapAssoc k
  obtain ⟨Γac', ha', hva⟩ := ha.assoc (Split.diagonal Γc hc)
  obtain ⟨Γbc, hg, hvb⟩ := hp.swapAssoc ha'.symm
  exact ⟨Γac', Γbc, hg.symm, hva, hvb.symm⟩

theorem SlotSplit.weakenSelf {A : τ} {q q' ql qr : Usage}
    (h : SlotSplit A q' ql qr) (heq : qr = q')
    (hq : Usage.effective q' (quantity A) ≤ Usage.effective q (quantity A)) :
    ∃ qL, SlotSplit A q qL q ∧
      Usage.effective ql (quantity A) ≤ Usage.effective qL (quantity A) ∧
      Usage.linearity ql (quantity A) ≤ Usage.linearity qL (quantity A) := by
  cases h with
  | left =>
    subst q'
    exact ⟨.zero, .right q, le_rfl, le_rfl⟩
  | right => exact ⟨.zero, .right q, le_rfl, le_rfl⟩
  | both hc =>
    have hz : q' ≠ .zero := by intro hz; subst q'; exact hc
    exact ⟨q, .both q (hc.trans hq), hq,
      Usage.linearity_le_of_effective_le _ _ _ hz hq⟩

/-- Transport a split that retains its whole context on the right. The
repeated context remains literally the weakening's source, as required by
elimination and effectful uniformity. -/
theorem Weakening.selfSplit {n m : Nat} {Γ : QCtx τ n} {Δ Δl : QCtx τ m}
    {ρ : Fin m → Fin n} (h : Weakening Γ Δ ρ) (s : Δ.Split Δl Δ) :
    ∃ Γl, Γ.Split Γl Γ ∧ Weakening Γl Δl ρ ∧ Δl.linearity ≤ Γl.linearity := by
  induction h with
  | nil =>
    have hl : Δl = QCtx.nil := funext (fun i => Fin.elim0 i)
    subst Δl
    exact ⟨QCtx.nil, .nil, .nil, le_rfl⟩
  | @cons n m Γ Δ ρ A q q' h hq ih =>
    have hs : (Δl 0).1 = A ∧ SlotSplit A q' (Δl 0).2 q' := ⟨(s 0).1, (s 0).2.2⟩
    obtain ⟨qL, hsplit, hl, hlin⟩ := hs.2.weakenSelf rfl hq
    obtain ⟨Γl, sg, wl, ht⟩ := ih (fun i => s i.succ)
    refine ⟨Γl.snoc A qL, sg.snoc hsplit, ?_, ?_⟩
    · have he : snoc (fun i => Δl i.succ) A (Δl 0).2 = Δl := by
        rw [← hs.1]
        exact snoc_tail Δl
      rw [← he]
      exact .cons wl hl
    · rw [linearity_snoc]
      apply le_inf
      · apply le_trans _ hlin
        simpa only [hs.1] using
          ((le_linearity_iff.mp (le_rfl : Δl.linearity ≤ Δl.linearity)) (0 : Fin (m + 1)))
      · apply le_trans _ ht
        exact le_linearity_iff.mpr fun i => (le_linearity_iff.mp le_rfl) i.succ
  | @skip n m Γ Δ ρ A q h hq ih =>
    obtain ⟨Γl, sg, wl, ht⟩ := ih s
    exact ⟨Γl.snoc A .zero, sg.snoc (.right q), .skip wl le_rfl, by
      rw [linearity_snoc, Usage.linearity_zero]
      exact ht⟩

end Silmaril.Isotope.Refinement.QCtx

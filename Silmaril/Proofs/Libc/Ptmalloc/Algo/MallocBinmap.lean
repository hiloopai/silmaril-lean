module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocFit

/-!
# ptmalloc algorithm: the large-bin best fit and the bin-map scan

* **`Algo.mallocLargeBody`** (= `Task.algo.mallocLargeBody`): `largeFit` picks a chunk of the
  request's bin of at least `nb` bytes, so `takeFit` lends it (`Algo.takeFit_body`);
* **`Algo.mallocBinmapBody`** (= `Task.algo.mallocBinmapBody`): the bin-map scan only unmarks
  empty bins (an `MStep`), and the last chunk of a later bin is larger than `nb`
  (`Config.binIndex_mono`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

theorem foldl_min_ge {m : Nat} : ∀ (xs : List Nat) (init : Nat), m ≤ init → (∀ x ∈ xs, m ≤ x) →
    m ≤ xs.foldl min init
  | [], _, h, _ => h
  | x :: xs, init, h, hx => by
    rw [List.foldl_cons]
    exact foldl_min_ge xs _ (Nat.le_min.mpr ⟨h, hx x (List.mem_cons_self ..)⟩)
      fun y hy => hx y (List.mem_cons_of_mem _ hy)

theorem findIdx_some {α : Type} (p : α → Bool) :
    ∀ (L : List α) (v : α), L[L.findIdx p]? = some v → p v = true
  | [], _, h => by simp at h
  | x :: xs, v, h => by
    rw [List.findIdx_cons] at h
    by_cases hx : p x
    · simp [hx] at h
      subst h; exact hx
    · simp [hx] at h
      exact findIdx_some p xs v h

/-- **The large-bin best fit** returns a chunk of the bin with at least `nb` bytes. -/
theorem largeFit_spec {l : Local} {nb v : Nat} (h : largeFit C l nb = some v) :
    v ∈ l.av.bins.lists (C.binIndex nb) ∧ nb ≤ l.av.tiles.sizeAt v := by
  unfold largeFit at h
  generalize hL : l.av.bins.lists (C.binIndex nb) = L at h ⊢
  generalize hsz : l.av.tiles.sizeAt = sz at h ⊢
  cases L with
  | nil => cases h
  | cons hd tl =>
    simp only at h
    split at h
    · cases h
    · rename_i hge
      have hs : nb ≤ ((hd :: tl).filter (fun b => nb ≤ sz b) |>.map sz).foldl min (sz hd) :=
        foldl_min_ge _ _ (by omega) (fun x hx => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          simpa using (List.mem_filter.mp hb).2)
      generalize hS : (((hd :: tl).filter (fun b => nb ≤ sz b)).map sz).foldl min (sz hd) = S at h hs
      have hj : ∀ w, (hd :: tl)[(hd :: tl).findIdx (fun b => sz b = S)]? = some w → v = w → v ∈ hd :: tl ∧ nb ≤ sz v := by
        intro w hw hvw
        subst hvw
        refine ⟨List.mem_of_getElem? hw, ?_⟩
        have := findIdx_some _ _ _ hw
        simp only [decide_eq_true_eq] at this
        omega
      split at h
      · rename_i b' hb'
        split at h
        · rename_i hb's
          simp only [Option.some.injEq] at h; subst h
          exact ⟨List.mem_of_getElem? hb', by omega⟩
        · exact hj v h rfl
      · exact hj v h rfl

/-- **`Algo.mallocLargeBody`**: `Task.algo.mallocLargeBody`. -/
theorem mallocLargeBody (C : Config) : Task.algo.mallocLargeBody C := by
  intro hC l n nb v hw hs hnb _ hfit
  obtain ⟨hv, hsz⟩ := largeFit_spec hfit
  exact takeFit_body hC hnb hw hs hv hsz false

theorem binmapScan_spec : ∀ (fuel j : Nat) (l : Local), ∃ bs : BinsSt,
    (binmapScan C fuel j l).2 = { l with av := { l.av with bins := bs } } ∧ bs.lists = l.av.bins.lists ∧
    (∀ i, bs.binmap i = false → l.av.bins.binmap i = false ∨ l.av.bins.lists i = []) ∧
    ∀ v j', (binmapScan C fuel j l).1 = some (v, j') → j ≤ j' ∧ (l.av.bins.lists j').getLast? = some v
  | 0, _, l => ⟨l.av.bins, rfl, rfl, fun _ h => .inl h, fun _ _ h => by cases h⟩
  | fuel + 1, j, l => by
    unfold binmapScan
    by_cases hj : C.nBins ≤ j
    · simp only [hj, ite_true]
      exact ⟨l.av.bins, rfl, rfl, fun _ h => .inl h, fun _ _ h => by cases h⟩
    · simp only [hj, ite_false]
      by_cases hm : l.av.bins.binmap j = true
      · simp only [hm, ite_true]
        cases hl : l.av.bins.last? j with
        | some v =>
          simp only
          refine ⟨l.av.bins, rfl, rfl, fun _ h => .inl h, fun v' j' h => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨Nat.le_refl _, hl⟩
        | none =>
          simp only
          obtain ⟨bs, h1, h2, h3, h4⟩ := binmapScan_spec fuel (j + 1)
            { l with av := { l.av with bins := l.av.bins.unmark j } }
          refine ⟨bs, h1, h2, fun i hi => ?_, fun v j' h => ?_⟩
          · rcases h3 i hi with h | h
            · by_cases hij : i = j
              · subst hij; right; simpa [BinsSt.last?] using hl
              · left; simpa [BinsSt.unmark, hij] using h
            · right; simpa [BinsSt.unmark] using h
          · obtain ⟨h5, h6⟩ := h4 v j' h
            exact ⟨by omega, by simpa [BinsSt.unmark] using h6⟩
      · simp only [hm, Bool.false_eq_true, ite_false]
        obtain ⟨bs, h1, h2, h3, h4⟩ := binmapScan_spec fuel (j + 1) l
        exact ⟨bs, h1, h2, h3, fun v j' h => by obtain ⟨h5, h6⟩ := h4 v j' h; exact ⟨by omega, h6⟩⟩

theorem _root_.Silmaril.Libc.Ptmalloc.BinsWF.of_lists {bs bs' : BinsSt} {cs : List Chunk} {sz : Nat → Nat} (h : BinsWF C bs cs sz)
    (hl : bs'.lists = bs.lists) (hm : ∀ i, bs'.binmap i = false → bs.binmap i = false ∨ bs.lists i = []) :
    BinsWF C bs' cs sz where
  exact := by rw [hl]; exact h.exact
  outside := by rw [hl]; exact h.outside
  nodup := by rw [hl]; exact h.nodup
  size := h.size
  sorted := by rw [hl]; exact h.sorted
  binmap i hi := by
    rw [hl] at hi
    cases hb : bs'.binmap i with
    | true => rfl
    | false =>
      rcases hm i hb with h' | h'
      · have := h.binmap i hi; rw [h'] at this; cases this
      · exact absurd h' hi

/-- **`Algo.mallocBinmapBody`**: `Task.algo.mallocBinmapBody`. -/
theorem mallocBinmapBody (C : Config) : Task.algo.mallocBinmapBody C := by
  intro hC l l₁ n nb o hw hs hnb hscan
  obtain ⟨bs, h1, h2, h3, h4⟩ := binmapScan_spec (C := C) C.nBins (C.binIndex nb + 1) l
  rw [hscan] at h1 h4
  simp only at h1 h4
  subst h1
  have hbw : BinsWF C bs l.av.sortedView l.av.tiles.sizeAt := hw.arena.bins.of_lists h2 h3
  have hav : ArenaWF C { l.av with bins := bs } := { hw.arena with bins := hbw }
  have hw₁ := hw.withAv _ hav rfl rfl rfl rfl Iff.rfl rfl
  have hst : MStep C l { l with av := { l.av with bins := bs } } :=
    MStep.of_arena hw₁ hs (SpansIn.refl _) rfl (List.Perm.refl _) (fun _ hc _ => hc)
  cases o with
  | none => exact ⟨hst, rfl⟩
  | some r =>
    obtain ⟨v, j⟩ := r
    obtain ⟨hj, hv⟩ := h4 v j rfl
    have hvm : v ∈ bs.lists j := by rw [h2]; exact List.mem_of_getLast? hv
    obtain ⟨hj2, d, hd, rfl, hdu⟩ := mem_bin_chunk hw₁ hvm
    have hbi := (hbw.size d (List.mem_filter.mpr ⟨hd, by rw [hdu]; simp [Use.isSorted, hj2]⟩) j hdu).2.2
    have hsz : nb ≤ (({ l with av := { l.av with bins := bs } } : Local).av.tiles.sizeAt d.addr) := by
      show nb ≤ l.av.tiles.sizeAt d.addr
      rw [TopSt.sizeAt_of_mem hw.arena.tiles.nodup hd]
      refine Nat.le_of_not_lt fun hlt => ?_
      have := Config.binIndex_mono hC (Nat.le_of_lt hlt)
      omega
    exact MBody.of_step hC hw hs hst
      (takeFit_body hC hnb hw₁ (MStep.sp hC hw hs hst) hvm hsz (C.inSmallRange nb))

end Silmaril.Libc.Ptmalloc.Algo

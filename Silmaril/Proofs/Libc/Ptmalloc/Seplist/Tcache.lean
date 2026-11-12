module

public import Silmaril.Libc.Ptmalloc.Rep.Defs
public import Silmaril.Data.Cells.Thms

/-!
# ptmalloc, representation: `tcache_get`'s stores

The tcache fragment is the bins' fragments in order; bin `i`'s changes (count, head, the popped
entry's `key`), the other bins and the rest of bin `i`'s list are framed by the separation of
the old fragment.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Libc.Ptmalloc.Seplist

open Silmaril.Data
open Silmaril.Data.SepList (slist)

/-- One tcache bin's fragment (the body of `tcacheFrag`). -/
def tcBinFrag (C : Config) (L : Layout) (key : Nat) (tc : TcacheSt) (i : Nat) : Frag :=
  let ps := (tc.bins i).map fun c => c.1 + C.hdr
  ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length⟩ ::
    Cell.w (tc.addr + L.tcEntries + 8 * i) (ps.headD 0) ::
    (slist (tcLinks C) ps ++ ps.map fun p => Cell.w (p + 8) key)

theorem tcacheFrag_eq (C : Config) (L : Layout) (key : Nat) (tc : TcacheSt) :
    tcacheFrag C L key tc = (List.range C.tcacheBins).flatMap (tcBinFrag C L key tc) := rfl

theorem range_split {n i : Nat} (h : i < n) :
    List.range n = List.range' 0 i ++ i :: List.range' (i + 1) (n - i - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = i + (k + 1) := ⟨n - i - 1, by omega⟩
  rw [show i + (k + 1) - i - 1 = k by omega, List.range_eq_range', ← List.range'_append_1,
    List.range'_succ]
  simp

theorem flatMap_congr_mem {f g : Nat → Frag} : ∀ {l : List Nat}, (∀ j ∈ l, f j = g j) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self ..), flatMap_congr_mem fun j hj => h j (List.mem_cons_of_mem _ hj)]

theorem leafTcacheGet : Task.seplist.leafTcacheGet := by
  intro C L key tc tc' i p v hok hwf hi hget hw0 hwc hfit hf hS
  unfold TcacheSt.get at hget
  split at hget
  · exact nomatch hget
  rename_i c rest hbi
  simp only [Option.some.injEq, Prod.mk.injEq] at hget
  obtain ⟨rfl, rfl⟩ := hget
  have hlen : (c :: rest).length ≤ C.tcacheCount := hbi ▸ (hwf.nodup i).2
  have hrest : ∀ j ∈ List.range' 0 i ++ List.range' (i + 1) (C.tcacheBins - i - 1),
      tcBinFrag C L key { tc with bins := fun j => if j = i then rest else tc.bins j } j =
        tcBinFrag C L key tc j := by
    intro j hj
    have : j ≠ i := by
      rcases List.mem_append.1 hj with h | h <;> (rw [List.mem_range'] at h; omega)
    simp [tcBinFrag, this]
  rw [tcacheFrag_eq, range_split hi, List.flatMap_append, List.flatMap_cons] at hf hS ⊢
  rw [flatMap_congr_mem fun j hj => hrest j (List.mem_append_left _ hj),
    flatMap_congr_mem (l := List.range' (i + 1) _) fun j hj => hrest j (List.mem_append_right _ hj)]
  generalize (List.range' 0 i).flatMap (tcBinFrag C L key tc) = A at hf hS ⊢
  generalize (List.range' (i + 1) (C.tcacheBins - i - 1)).flatMap (tcBinFrag C L key tc) = B
    at hf hS ⊢
  simp only [tcBinFrag, hbi, ↓reduceIte, List.map_cons, List.length_cons, List.headD_cons, slist,
    List.cons_append, List.append_assoc, Nat.add_sub_cancel] at hf hS ⊢
  have hpfit : ∀ x ∈ rest.map (fun c => c.1 + C.hdr), x < 256 ^ 8 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
    exact hfit d (by rw [hbi]; exact List.mem_cons_of_mem _ hd)
  have hheadfit : (rest.map (fun c => c.1 + C.hdr)).headD 0 < 256 ^ 8 := by
    cases h : rest.map (fun c => c.1 + C.hdr) with
    | nil => simp
    | cons x xs => exact hpfit x (by rw [h]; exact List.mem_cons_self ..)
  have hcntfit : rest.length < 256 ^ C.tcacheCountWidth := by
    simp only [List.length_cons] at hlen; omega
  generalize rest.map (fun c => c.1 + C.hdr) = ps at hf hS hheadfit ⊢
  -- the separation facts
  rw [Frag.sep_append] at hS
  obtain ⟨_, hSPB, hAPB⟩ := hS
  obtain ⟨hS2, hc1⟩ := Frag.sep_cons.1 hSPB
  obtain ⟨hS3, he1⟩ := Frag.sep_cons.1 hS2
  obtain ⟨hS4, _⟩ := Frag.sep_cons.1 hS3
  obtain ⟨_, hS6, hSK⟩ := Frag.sep_append.1 hS4
  obtain ⟨_, hk⟩ := Frag.sep_cons.1 hS6
  have hcntH := hf ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth,
    rest.length + 1⟩ (by simp)
  have hentH := hf (Cell.w (tc.addr + L.tcEntries + 8 * i) (c.fst + C.hdr)) (by simp)
  have hkeyH := hf (Cell.w (c.fst + C.hdr + 8) key) (by simp)
  have hce := hc1 (Cell.w (tc.addr + L.tcEntries + 8 * i) (c.fst + C.hdr)) (by simp)
  have hck := hc1 (Cell.w (c.fst + C.hdr + 8) key) (by simp)
  have hek := he1 (Cell.w (c.fst + C.hdr + 8) key) (by simp)
  intro x hx
  refine Cell.holds_storeAll ?_ ?_ ?_
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨hcntfit, hcntH.2⟩
    · exact ⟨hheadfit, hentH.2⟩
    · exact ⟨by simp [Cell.w], hkeyH.2⟩
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact hce.of_eq rfl rfl rfl rfl
      · exact hck.of_eq rfl rfl rfl rfl
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact hek.of_eq rfl rfl rfl rfl
  · simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | rfl | hx | hx | hx
    · refine .inr ⟨hf x (by simp [hx]), fun d hd => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact (hAPB x hx ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, rest.length + 1⟩ (by simp)).of_eq rfl rfl rfl rfl
      · exact (hAPB x hx (Cell.w (tc.addr + L.tcEntries + 8 * i) (c.fst + C.hdr)) (by simp)).of_eq
          rfl rfl rfl rfl
      · exact (hAPB x hx (Cell.w (c.fst + C.hdr + 8) key) (by simp)).of_eq rfl rfl rfl rfl
    · exact .inl (by simp)
    · exact .inl (by simp)
    all_goals
      refine .inr ⟨hf x (by simp [hx]), fun d hd => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact (hc1 x (by simp [hx])).symm.of_eq rfl rfl rfl rfl
      · exact (he1 x (by simp [hx])).symm.of_eq rfl rfl rfl rfl
      · first
          | exact (hSK x hx (Cell.w (c.fst + C.hdr + 8) key) (by simp)).of_eq rfl rfl rfl rfl
          | exact (hk x (by simp [hx])).symm.of_eq rfl rfl rfl rfl


end Silmaril.Libc.Ptmalloc.Seplist

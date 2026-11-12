module

public import Silmaril.Libc.Ptmalloc.Tcache.Defs

/-!
# ptmalloc component: the tcache's lemmas

`get` and `put` keep `TcacheWF` (`TcacheSt.wf_get`, `TcacheSt.wf_put`) and move exactly one
entry between the bin and the caller (`TcacheSt.payloads_get`, `TcacheSt.payloads_put`: the
parked payloads up to permutation). Nothing here mentions an arena.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

namespace TcacheSt

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {L : List α}, (∀ x ∈ L, f x = g x) → L.flatMap f = L.flatMap g
  | [], _ => rfl
  | x :: L, h => by
    simp only [List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- Flattening a family of lists over distinct indices, after replacing index `i`'s list
`c :: rest` by `rest`, loses exactly `c`. -/
theorem flatMap_update_perm {α : Type} (g : Nat → List α) (i : Nat) (c : α) (rest : List α)
    (hg : g i = c :: rest) :
    ∀ L : List Nat, L.Nodup → i ∈ L →
      (L.flatMap g).Perm (c :: L.flatMap fun j => if j = i then rest else g j)
  | [], _, h => absurd h (List.not_mem_nil)
  | j :: L, hn, hi => by
    rw [List.nodup_cons] at hn
    simp only [List.flatMap_cons]
    by_cases hji : j = i
    · subst hji
      have : (L.flatMap fun k => if k = j then rest else g k) = L.flatMap g := by
        apply flatMap_congr'
        intro k hk
        have : k ≠ j := fun h => hn.1 (h ▸ hk)
        simp [this]
      rw [hg, this]; simp
    · have hiL : i ∈ L := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm hji
        · exact h
      have ih := flatMap_update_perm g i c rest hg L hn.2 hiL
      simp only [hji, ite_false]
      exact (List.Perm.append_left (g j) ih).trans List.perm_middle

/-- Flattening after pushing `c` on index `i`'s list gains exactly `c`. -/
theorem flatMap_push_perm {α : Type} (g : Nat → List α) (i : Nat) (c : α) :
    ∀ L : List Nat, L.Nodup → i ∈ L →
      (L.flatMap fun j => if j = i then c :: g j else g j).Perm (c :: L.flatMap g) := by
  intro L hn hi
  have h := flatMap_update_perm (fun j => if j = i then c :: g j else g j) i c (g i) (by simp) L hn hi
  have : (L.flatMap fun j => if j = i then g i else if j = i then c :: g j else g j) = L.flatMap g := by
    apply flatMap_congr'; intro k _; by_cases hk : k = i <;> simp [hk]
  rw [this] at h; exact h

variable {C : Config} {tc : TcacheSt}

theorem get_eq {i p : Nat} {tc' : TcacheSt} (h : tc.get C i = some (p, tc')) :
    ∃ c rest, tc.bins i = c :: rest ∧ p = c.1 + C.hdr ∧
      tc' = { tc with bins := fun j => if j = i then rest else tc.bins j } := by
  unfold get at h
  split at h
  · cases h
  · rename_i c rest hb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨c, rest, hb, h.1.symm, h.2.symm⟩

/-- **`tcache_get` keeps the tcache's invariant.** -/
theorem wf_get {i p : Nat} {tc' : TcacheSt} (hw : TcacheWF C tc) (h : tc.get C i = some (p, tc')) :
    TcacheWF C tc' := by
  obtain ⟨c, rest, hb, -, rfl⟩ := get_eq h
  have hsub : ∀ j, ∀ x, x ∈ (if j = i then rest else tc.bins j) → x ∈ tc.bins j := by
    intro j x hx; by_cases hj : j = i
    · subst hj; simp only [ite_true] at hx; rw [hb]; exact List.mem_cons_of_mem _ hx
    · simpa [hj] using hx
  refine ⟨?_, ?_, ?_, ?_, hw.struct⟩
  · intro j hj; by_cases hji : j = i
    · subst hji; have := hw.bins j hj; rw [hb] at this; cases this
    · simp [hji, hw.bins j hj]
  · intro j; by_cases hji : j = i
    · subst hji; have := hw.nodup j; rw [hb] at this
      simp only [ite_true]
      exact ⟨(List.nodup_cons.mp this.1).2, by simp at this; omega⟩
    · simp only [hji, ite_false]; exact hw.nodup j
  · intro j x hx; exact hw.size j x (hsub j x hx)
  · intro j x hx; exact hw.nonNull j x (hsub j x hx)

/-- **`tcache_put` keeps the tcache's invariant** when the chunk fits the bin, is not in it, and
the bin has room. -/
theorem wf_put {c : Nat × Nat} {i : Nat} (hw : TcacheWF C tc) (hi : i < C.tcacheBins)
    (hidx : C.tidx c.2 = i) (hal : c.2 % C.align = 0) (hmin : C.minSize ≤ c.2)
    (hnn : c.1 ≠ 0) (hca : c.1 % C.align = 0) (hnot : c ∉ tc.bins i)
    (hroom : (tc.bins i).length < C.tcacheCount) : TcacheWF C (tc.put c i) := by
  refine ⟨?_, ?_, ?_, ?_, hw.struct⟩
  · intro j hj; have : j ≠ i := by omega
    simp [put, this, hw.bins j hj]
  · intro j; by_cases hji : j = i
    · subst hji; simp only [put, ite_true]
      exact ⟨List.nodup_cons.mpr ⟨hnot, (hw.nodup j).1⟩, by simp; omega⟩
    · simp only [put, hji, ite_false]; exact hw.nodup j
  · intro j x hx; by_cases hji : j = i
    · subst hji; simp only [put, ite_true, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨hidx, hal, hmin⟩
      · exact hw.size j x hx
    · simp only [put, hji, ite_false] at hx; exact hw.size j x hx
  · intro j x hx; by_cases hji : j = i
    · subst hji; simp only [put, ite_true, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨hnn, hca⟩
      · exact hw.nonNull j x hx
    · simp only [put, hji, ite_false] at hx; exact hw.nonNull j x hx

/-- **`tcache_get` parks one payload less**: the payload it returns, with the usable size. -/
theorem payloads_get {i p : Nat} {tc' : TcacheSt} (hw : TcacheWF C tc)
    (h : tc.get C i = some (p, tc')) :
    ∃ u, (tc.payloads C).Perm ((p, u) :: tc'.payloads C) := by
  obtain ⟨c, rest, hb, rfl, rfl⟩ := get_eq h
  have hi : i < C.tcacheBins := by
    refine Nat.lt_of_not_le fun hle => ?_
    have := hw.bins i hle; rw [hb] at this; cases this
  refine ⟨c.2 - C.sizeSz, ?_⟩
  unfold payloads
  have hp := flatMap_update_perm tc.bins i c rest hb (List.range C.tcacheBins) List.nodup_range
    (List.mem_range.mpr hi)
  exact (hp.map _).trans (by simp)

/-- **`tcache_put` parks one payload more.** -/
theorem payloads_put {c : Nat × Nat} {i : Nat} (hi : i < C.tcacheBins) :
    ((tc.put c i).payloads C).Perm ((c.1 + C.hdr, c.2 - C.sizeSz) :: tc.payloads C) := by
  unfold payloads put
  have hp := flatMap_push_perm tc.bins i c (List.range C.tcacheBins) List.nodup_range
    (List.mem_range.mpr hi)
  exact (hp.map _).trans (by simp)

end TcacheSt

end Silmaril.Libc.Ptmalloc

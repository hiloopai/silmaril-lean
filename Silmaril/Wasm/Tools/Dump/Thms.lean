module

public import Silmaril.Wasm.Tools.Dump.Defs

/-!
# `wasm-tools dump`: every byte is printed once, in order

`tilesFrom_offsets`: lines that tile `[c, n)` stand for the offsets `c, c+1, …, n-1`, in
order, each exactly once. `dump_tiles`: the lines of a dump that ends without an error stand
for every offset of the input, in order, each once (upstream's `assert_eq!(self.cur,
self.bytes.len())`, plus the order). The operator lines among them are those of the certified
decoder whenever it reads the whole body (`DumpOps.Thms.dExpr_erase`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Dump

/-- Two adjacent ranges of offsets make one. -/
theorem range'_join (s t n : Nat) (hst : s ≤ t) (htn : t ≤ n) :
    List.range' s (t - s) ++ List.range' t (n - t) = List.range' s (n - s) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = s + k := ⟨t - s, by omega⟩
  have h1 : s + k - s = k := by omega
  have h2 : n - s = k + (n - (s + k)) := by omega
  rw [h1, h2, List.range'_append_1]

/-- Lines that tile `[c, n)` stand for the offsets `[c, n)`, in order. -/
theorem tilesFrom_offsets (ls : List Line) (c n : Nat) (h : tilesFrom ls c n = true) :
    ls.flatMap Line.offsets = List.range' c (n - c) ∧ c ≤ n := by
  induction ls generalizing c with
  | nil =>
    have hc : c = n := by simpa [tilesFrom] using h
    subst hc; simp
  | cons l ls ih =>
    cases l with
    | raw _ => simpa [tilesFrom, Line.offsets] using ih c (by simpa [tilesFrom] using h)
    | bytes _ s t _ _ =>
      simp only [tilesFrom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hlt⟩, hr⟩ := h
      obtain ⟨ih1, ih2⟩ := ih t hr
      exact ⟨by simp only [List.flatMap_cons, Line.offsets, ih1, range'_join s t n (by omega) ih2],
        by omega⟩
    | data _ s t _ =>
      simp only [tilesFrom, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hle⟩, hr⟩ := h
      obtain ⟨ih1, ih2⟩ := ih t hr
      exact ⟨by simp only [List.flatMap_cons, Line.offsets, ih1, range'_join s t n hle ih2],
        by omega⟩

/-- **Every byte once, in order**: a dump without an error prints lines that stand for the
offsets `0, 1, …, b.size - 1` of the input, in order, each exactly once. -/
theorem dump_tiles (b : ByteArray) (h : (dumpLines b).2 = none) :
    (dumpLines b).1.toList.flatMap Line.offsets = List.range b.size := by
  unfold dumpLines at h ⊢
  revert h
  split
  · split
    · rename_i ht
      intro _
      simpa [List.range_eq_range'] using (tilesFrom_offsets _ 0 b.size ht).1
    · intro h; simp at h
  · intro h; simp at h

end Silmaril.Wasm.Tools.Dump

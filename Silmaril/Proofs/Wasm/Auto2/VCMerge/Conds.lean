module

public import Silmaril.Wasm.Auto2.VCMerge.Defs
public import Silmaril.Wasm.Auto2.VCGen.Thms
public import Silmaril.Wasm.Logic.Words.Thms

/-!
# `merge` through the VC generator: the conditions

The 33 conditions of `merge` against `mergeSpecV`: the merge loop's entry and exit, the bounds of
its loads and stores, the step and the variant of each of its six paths (the left or the right
element taken, after one of the three ways of choosing; the paths whose flag contradicts the
branch taken are closed by their path condition), and the copy loop's exit, bounds, step and
variant. Each is a lemma over the words of the memories, closed with the hand proof's facts
(`left_facts`, `right_facts`, `merge_done`, `copy_facts`, `read_halves` of
`Silmaril.WasmSpec.MergeSort`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCMerge

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.MergeSort (Sorts Bounds MFacts half₁ half₂ merged left_facts right_facts
  merge_done copy_facts read_halves)

/-! ## Memory accesses -/

theorem ldW_wd (B : ByteArray) (a : Nat) : ldW 32 4 .unsigned B a = wd B a := by
  simp [ldW, rd, wd]

theorem stW_wr {B : ByteArray} {a : Nat} (v : BitVec 32) (h : a + 4 ≤ B.size) :
    stW 32 4 B a v = wr B a v := by
  simp [stW, store_wr v h]

/-- A word `k < n` of a segment `[q, q + 4 n)` of a memory of the size of `B`. -/
theorem bound_of {B B' : ByteArray} {q n k : BitVec 32} (hb : q.toNat + 4 * n.toNat ≤ B.size)
    (hw : q.toNat + 4 * n.toNat < 2 ^ 32) (hs : B'.size = B.size) (hk : k.toNat < n.toNat) :
    (q + k * 4#32).toNat + 4 ≤ B'.size := by
  rw [addr_toNat hk hw, hs]
  omega

theorem var_dec {n k : BitVec 32} (hk : ¬n.toNat ≤ k.toNat) :
    (n - (k + 1#32)).toNat < (n - k).toNat := by
  bv_omega

/-! ## The copy loop -/

theorem c_entry {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : n.toNat ≤ k.toNat) : mergeFns.pr2 2 M M0 [p, n, t, 0#32] := by
  obtain ⟨hl, hmn, -, -⟩ := hp
  have hf' : MFacts M0 M p m n t i j k := hf
  obtain ⟨hs, hperm⟩ := merge_done hmn hf' hk
  have hso := hf'.2.2.2.2.1
  have hwp : words M p.toNat n.toNat = words M0 p.toNat n.toNat :=
    hso.words_eq (by have := hl.2.2.2.2; omega)
  exact ⟨by simp, hso.two' _ _, hs, hperm, by simp [hwp]⟩

theorem c_exit {M M0 : ByteArray} {p n t k : BitVec 32} (hc : mergeFns.pr2 2 M M0 [p, n, t, k])
    (hk : n.toNat ≤ k.toNat) : mergeFns.pr2 0 M M0 [p, n, t] := by
  obtain ⟨-, hso, hs, hperm, hwp⟩ := hc
  have hdone : words M p.toNat n.toNat = words M t.toNat n.toNat := by
    rw [hwp, List.take_of_length_le (by simp; omega), List.drop_of_length_le (by simp; omega),
      List.append_nil]
  show Sorts M0 M p.toNat n.toNat t.toNat
  exact ⟨hso, hdone ▸ hs, hdone ▸ hperm⟩

theorem c_bound_t {M M0 : ByteArray} {p m n t k : BitVec 32}
    (hc : mergeFns.pr2 2 M M0 [p, n, t, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : ¬n.toNat ≤ k.toNat) : (t + k * 4#32).toNat + 4 ≤ M.size :=
  bound_of hp.1.2.1 hp.1.2.2.2.1 hc.2.1.1 (by omega)

theorem c_bound_p {M M0 : ByteArray} {p m n t k : BitVec 32}
    (hc : mergeFns.pr2 2 M M0 [p, n, t, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : ¬n.toNat ≤ k.toNat) : (p + k * 4#32).toNat + 4 ≤ M.size :=
  bound_of hp.1.1 hp.1.2.2.1 hc.2.1.1 (by omega)

theorem c_step {M M0 : ByteArray} {p m n t k : BitVec 32}
    (hc : mergeFns.pr2 2 M M0 [p, n, t, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : ¬n.toNat ≤ k.toNat) :
    mergeFns.pr2 2 (stW 32 4 M ((p + k * 4#32).toNat + 0)
      (ldW 32 4 .unsigned M ((t + k * 4#32).toNat + 0))) M0 [p, n, t, k + 1#32] := by
  have hbp := c_bound_p hc hp hk
  obtain ⟨-, hso, hs, hperm, hwp⟩ := hc
  have hl : Bounds M0 p n t := hp.1
  have hlt : k.toNat < n.toNat := by omega
  obtain ⟨hso', hwt', hwp'⟩ := copy_facts (W := words M t.toNat n.toNat) hl hlt (by simp) hso
    rfl hwp
  have hld : ldW 32 4 .unsigned M ((t + k * 4#32).toNat + 0) =
      (words M t.toNat n.toNat).getD k.toNat 0 := by
    rw [Nat.add_zero, ldW_wd, wd_addr hlt hl.2.2.2.1]
  rw [hld, Nat.add_zero, stW_wr _ hbp]
  show CFacts M0 _ p n t (k + 1#32)
  have hk1 : (k + 1#32).toNat ≤ n.toNat := by bv_omega
  refine ⟨hk1, hso', ?_, ?_, ?_⟩
  · rw [hwt']
    exact hs
  · rw [hwt']
    exact hperm
  · rw [hwt']
    exact hwp'

/-! ## The merge loop -/

theorem m_entry {M0 : ByteArray} {p m n t : BitVec 32} (hp : mergeFns.pr 0 M0 [p, m, n, t]) :
    mergeFns.pr2 1 M0 M0 [p, m, n, t, 0#32, m, 0#32] := by
  obtain ⟨-, hmn, -, -⟩ := hp
  show MFacts M0 M0 p m n t 0#32 m 0#32
  exact ⟨by simp, le_refl _, hmn, by simp, SameOutside.refl _ _ _, by simp [merged],
    by simp [merged], by simp [merged, Silmaril.WasmSpec.MergeSort.Cross]⟩

theorem m_size {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) : M.size = M0.size :=
  hf.2.2.2.2.1.1

theorem m_bound_t {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : ¬n.toNat ≤ k.toNat) : (t + k * 4#32).toNat + 4 ≤ M.size :=
  bound_of hp.1.2.1 hp.1.2.2.2.1 (m_size hf) (by omega)

/-- In the merge loop, `i < m` if `k < n` and the right half is exhausted. -/
theorem m_i_lt {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hk : ¬n.toNat ≤ k.toNat)
    (hj : n.toNat ≤ j.toNat) : i.toNat < m.toNat := by
  obtain ⟨-, hj₁, hj₂, hk', -⟩ := (hf : MFacts M0 M p m n t i j k)
  omega

theorem m_bound_i {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hi : ¬m.toNat ≤ i.toNat) : (p + i * 4#32).toNat + 4 ≤ M.size :=
  bound_of hp.1.1 hp.1.2.2.1 (m_size hf) (by have := hp.2.1; omega)

theorem m_bound_i' {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : ¬n.toNat ≤ k.toNat) (hj : n.toNat ≤ j.toNat) : (p + i * 4#32).toNat + 4 ≤ M.size :=
  m_bound_i hf hp (by have := m_i_lt hf hk hj; omega)

theorem m_bound_j {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hj : ¬n.toNat ≤ j.toNat) : (p + j * 4#32).toNat + 4 ≤ M.size :=
  bound_of hp.1.1 hp.1.2.2.1 (m_size hf) (by omega)

/-- The words read at `i < m` and at `m ≤ j < n` are the halves' elements. -/
theorem m_reads {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t]) :
    (i.toNat < m.toNat → ldW 32 4 .unsigned M ((p + i * 4#32).toNat + 0) =
      (half₁ M0 p m).getD i.toNat 0) ∧
    (j.toNat < n.toNat → ldW 32 4 .unsigned M ((p + j * 4#32).toNat + 0) =
      (half₂ M0 p m n).getD (j.toNat - m.toNat) 0) := by
  have hf' : MFacts M0 M p m n t i j k := hf
  obtain ⟨hr₁, hr₂⟩ := read_halves hp.1 hp.2.1 hf'.2.2.2.2.1
  refine ⟨fun hi => ?_, fun hj => ?_⟩
  · rw [Nat.add_zero, ldW_wd, hr₁ i hi]
  · rw [Nat.add_zero, ldW_wd, hr₂ j hf'.2.1 hj]

/-- **Taking the left element**, given that it may be taken. -/
theorem m_left {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : ¬n.toNat ≤ k.toNat) (hi : i.toNat < m.toNat)
    (hle : n.toNat ≤ j.toNat ∨
      ((half₁ M0 p m).getD i.toNat 0).toInt ≤ ((half₂ M0 p m n).getD (j.toNat - m.toNat) 0).toInt) :
    mergeFns.pr2 1 (stW 32 4 M ((t + k * 4#32).toNat + 0)
      (ldW 32 4 .unsigned M ((p + i * 4#32).toNat + 0))) M0 [p, m, n, t, i + 1#32, j, k + 1#32] := by
  have hbt := m_bound_t hf hp hk
  rw [(m_reads hf hp).1 hi, Nat.add_zero, stW_wr _ hbt]
  exact left_facts hp.1 hp.2.2.1 hp.2.2.2 hf (by omega) hi hle

/-- **Taking the right element**, given that it may be taken. -/
theorem m_right {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : ¬n.toNat ≤ k.toNat) (hj : ¬n.toNat ≤ j.toNat)
    (hlt : m.toNat ≤ i.toNat ∨
      ((half₂ M0 p m n).getD (j.toNat - m.toNat) 0).toInt < ((half₁ M0 p m).getD i.toNat 0).toInt) :
    mergeFns.pr2 1 (stW 32 4 M ((t + k * 4#32).toNat + 0)
      (ldW 32 4 .unsigned M ((p + j * 4#32).toNat + 0))) M0 [p, m, n, t, i, j + 1#32, k + 1#32] := by
  have hbt := m_bound_t hf hp hk
  rw [(m_reads hf hp).2 (by omega), Nat.add_zero, stW_wr _ hbt]
  exact right_facts hp.1 hp.2.2.1 hp.2.2.2 hf (by omega) (by omega) hlt

/-- The left element when the right half is exhausted (`l := 1`). -/
theorem m_left_jn {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : ¬n.toNat ≤ k.toNat) (hj : n.toNat ≤ j.toNat) :
    mergeFns.pr2 1 (stW 32 4 M ((t + k * 4#32).toNat + 0)
      (ldW 32 4 .unsigned M ((p + i * 4#32).toNat + 0))) M0 [p, m, n, t, i + 1#32, j, k + 1#32] :=
  m_left hf hp hk (m_i_lt hf hk hj) (.inl hj)

/-- The left element after the comparison (`l := (a[i] ≤ a[j]) ≠ 0`). -/
theorem m_left_cmp {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : ¬n.toNat ≤ k.toNat) (hi : ¬m.toNat ≤ i.toNat) (hj : ¬n.toNat ≤ j.toNat)
    (hc : (if (ldW 32 4 .unsigned M ((p + i * 4#32).toNat + 0)).toInt ≤
        (ldW 32 4 .unsigned M ((p + j * 4#32).toNat + 0)).toInt then (1 : BitVec 32) else 0) ≠ 0) :
    mergeFns.pr2 1 (stW 32 4 M ((t + k * 4#32).toNat + 0)
      (ldW 32 4 .unsigned M ((p + i * 4#32).toNat + 0))) M0 [p, m, n, t, i + 1#32, j, k + 1#32] := by
  refine m_left hf hp hk (by omega) (.inr ?_)
  rw [← (m_reads hf hp).1 (by omega), ← (m_reads hf hp).2 (by omega)]
  split at hc
  · assumption
  · exact absurd rfl hc

/-- The right element when the left half is exhausted (`l := 0`). -/
theorem m_right_im {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : ¬n.toNat ≤ k.toNat) (hi : m.toNat ≤ i.toNat) (hj : ¬n.toNat ≤ j.toNat) :
    mergeFns.pr2 1 (stW 32 4 M ((t + k * 4#32).toNat + 0)
      (ldW 32 4 .unsigned M ((p + j * 4#32).toNat + 0))) M0 [p, m, n, t, i, j + 1#32, k + 1#32] :=
  m_right hf hp hk hj (.inl hi)

/-- The right element after the comparison (`l := (a[i] ≤ a[j]) = 0`). -/
theorem m_right_cmp {M M0 : ByteArray} {p m n t i j k : BitVec 32}
    (hf : mergeFns.pr2 1 M M0 [p, m, n, t, i, j, k]) (hp : mergeFns.pr 0 M0 [p, m, n, t])
    (hk : ¬n.toNat ≤ k.toNat) (hi : ¬m.toNat ≤ i.toNat) (hj : ¬n.toNat ≤ j.toNat)
    (hc : ¬(if (ldW 32 4 .unsigned M ((p + i * 4#32).toNat + 0)).toInt ≤
        (ldW 32 4 .unsigned M ((p + j * 4#32).toNat + 0)).toInt then (1 : BitVec 32) else 0) ≠ 0) :
    mergeFns.pr2 1 (stW 32 4 M ((t + k * 4#32).toNat + 0)
      (ldW 32 4 .unsigned M ((p + j * 4#32).toNat + 0))) M0 [p, m, n, t, i, j + 1#32, k + 1#32] := by
  refine m_right hf hp hk hj (.inr ?_)
  rw [← (m_reads hf hp).1 (by omega), ← (m_reads hf hp).2 (by omega)]
  split at hc
  · exact absurd (by decide) hc
  · omega

/-- Close one computed condition of `merge` (after `vcgen4`). -/
macro "merge_vc" : tactic => `(tactic| (
  try simp only [and_imp]
  intros
  subst_vars
  first
  | exact absurd ‹¬(1#32 : BitVec 32) ≠ 0› (by decide)
  | exact absurd (rfl : (0#32 : BitVec 32) = 0) ‹_›
  | exact m_entry ‹_›
  | exact c_entry ‹_› ‹_› ‹_›
  | exact c_exit ‹_› ‹_›
  | exact c_bound_t ‹_› ‹_› ‹_›
  | exact c_bound_p ‹_› ‹_› ‹_›
  | exact c_step ‹_› ‹_› ‹_›
  | exact var_dec ‹_›
  | exact m_bound_t ‹_› ‹_› ‹_›
  | exact m_bound_i ‹_› ‹_› ‹_›
  | exact m_bound_i' ‹_› ‹_› ‹_› ‹_›
  | exact m_bound_j ‹_› ‹_› ‹_›
  | exact m_left_jn ‹_› ‹_› ‹_› ‹_›
  | exact m_left_cmp ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  | exact m_right_im ‹_› ‹_› ‹_› ‹_› ‹_›
  | exact m_right_cmp ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›))

set_option maxRecDepth 100000 in
/-- **The 33 conditions of `merge`.** -/
theorem merge_vcs :
    AllValid mergeFns (genFunc mergeSpecV Silmaril.WasmSpec.MergeSort.mergeFunc mergeFuel) := by
  vcgen4
  all_goals merge_vc

end Silmaril.Wasm.Auto2.VCMerge

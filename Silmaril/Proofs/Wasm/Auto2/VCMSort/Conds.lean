module

public import Silmaril.Wasm.Auto2.VCMSort.Defs
public import Silmaril.Wasm.Auto2.VCMerge.Thms

/-!
# Merge sort through the VC generator: the conditions

The 5 conditions of `merge_sort` against `msortSpec` under `msFns N` (for every `N`): the base
case, the preconditions of the two recursive calls and of `merge`, and the postcondition (the hand
proof's `sorts_compose`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCMSort

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.MergeSort (Bounds Sorts sorts_compose sortedS_of_length_le_one)
open Silmaril.Wasm.Auto2.VCMerge (PreM)

theorem shr1 {n : BitVec 32} : (n >>> 1).toNat = n.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- A shorter segment at the same address keeps the layout. -/
theorem bounds_prefix {B : ByteArray} {p n t m : BitVec 32} (h : Bounds B p n t)
    (hm : m.toNat ≤ n.toNat) : Bounds B p m t := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem c_base {N : Nat} {B : ByteArray} {p n t : BitVec 32} (hn : n.toNat < 2)
    (_h : (msFns N).pr 6 B [p, n, t]) : (msFns N).pr2 0 B B [p, n, t] :=
  show Sorts B B p.toNat n.toNat t.toNat from
    ⟨(SameOutside.refl _ _ _).two _ _, sortedS_of_length_le_one (by simp; omega), List.Perm.refl _⟩

theorem c_call1 {N : Nat} {B : ByteArray} {p n t : BitVec 32} (hn : ¬n.toNat < 2)
    (h : (msFns N).pr 6 B [p, n, t]) : (msFns N).pr 5 B [p, n >>> 1, t] := by
  obtain ⟨hb, hN⟩ := h
  have hm : (n >>> 1).toNat = n.toNat / 2 := shr1
  exact ⟨bounds_prefix hb (by omega), by omega⟩

/-- The address and length of the second half. -/
theorem half2 {p n : BitVec 32} (hw : p.toNat + 4 * n.toNat < 2 ^ 32) :
    (p + (n >>> 1) * 4#32).toNat = p.toNat + 4 * (n.toNat / 2) ∧
      (n - n >>> 1).toNat = n.toNat - n.toNat / 2 := by
  have hm : (n >>> 1).toNat = n.toNat / 2 := shr1
  constructor <;> bv_omega

set_option linter.unusedTactic false in
theorem c_call2 {N : Nat} {B B₁ : ByteArray} {p n t : BitVec 32} (hn : ¬n.toNat < 2)
    (h : (msFns N).pr 6 B [p, n, t]) (h₁ : (msFns N).pr2 0 B₁ B [p, n >>> 1, t]) :
    (msFns N).pr 5 B₁ [p + (n >>> 1) * 4#32, n - n >>> 1, t] := by
  obtain ⟨⟨hb₁, hb₂, hw₁, hw₂, hd⟩, hN⟩ := h
  have hs : B₁.size = B.size := (h₁ : Sorts B B₁ _ _ _).1.1
  obtain ⟨ha, hl⟩ := half2 hw₁
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> (try simp only [ha, hl]) <;> omega

theorem c_merge {N : Nat} {B B₁ B₂ : ByteArray} {p n t : BitVec 32} (hn : ¬n.toNat < 2)
    (h : (msFns N).pr 6 B [p, n, t]) (h₁ : (msFns N).pr2 0 B₁ B [p, n >>> 1, t])
    (h₂ : (msFns N).pr2 0 B₂ B₁ [p + (n >>> 1) * 4#32, n - n >>> 1, t]) :
    (msFns N).pr 0 B₂ [p, n >>> 1, n, t] := by
  obtain ⟨⟨hb₁, hb₂, hw₁, hw₂, hd⟩, hN⟩ := h
  have hm : (n >>> 1).toNat = n.toNat / 2 := shr1
  obtain ⟨ha, hl⟩ := half2 hw₁
  have h₁' : Sorts B B₁ p.toNat (n.toNat / 2) t.toNat := by
    have h₁s : Sorts B B₁ p.toNat (n >>> 1).toNat t.toNat := h₁
    rwa [hm] at h₁s
  have h₂' : Sorts B₁ B₂ (p.toNat + 4 * (n.toNat / 2)) (n.toNat - n.toNat / 2) t.toNat := by
    have h₂s : Sorts B₁ B₂ (p + (n >>> 1) * 4#32).toNat (n - n >>> 1).toNat t.toNat := h₂
    rwa [ha, hl] at h₂s
  have hs : B₂.size = B.size := h₂'.1.1.trans h₁'.1.1
  have hw : words B₂ p.toNat (n.toNat / 2) = words B₁ p.toNat (n.toNat / 2) :=
    h₂'.1.words_eq (by omega) (by omega)
  show PreM B₂ p (n >>> 1) n t
  refine ⟨⟨by omega, by omega, hw₁, hw₂, hd⟩, by omega, ?_, ?_⟩
  · show SortedS (words B₂ p.toNat (n >>> 1).toNat)
    rw [hm, hw]
    exact h₁'.2.1
  · show SortedS (words B₂ (p.toNat + 4 * (n >>> 1).toNat) (n.toNat - (n >>> 1).toNat))
    rw [hm]
    exact h₂'.2.1

theorem c_post {N : Nat} {B B₁ B₂ B₃ : ByteArray} {p n t : BitVec 32}
    (h : (msFns N).pr 6 B [p, n, t]) (h₁ : (msFns N).pr2 0 B₁ B [p, n >>> 1, t])
    (h₂ : (msFns N).pr2 0 B₂ B₁ [p + (n >>> 1) * 4#32, n - n >>> 1, t])
    (h₃ : (msFns N).pr2 0 B₃ B₂ [p, n, t]) : (msFns N).pr2 0 B₃ B [p, n, t] := by
  obtain ⟨⟨hb₁, hb₂, hw₁, hw₂, hd⟩, hN⟩ := h
  have hm : (n >>> 1).toNat = n.toNat / 2 := shr1
  obtain ⟨ha, hl⟩ := half2 hw₁
  have h₁' : Sorts B B₁ p.toNat (n.toNat / 2) t.toNat := by
    have h₁s : Sorts B B₁ p.toNat (n >>> 1).toNat t.toNat := h₁
    rwa [hm] at h₁s
  have h₂' : Sorts B₁ B₂ (p.toNat + 4 * (n.toNat / 2)) (n.toNat - n.toNat / 2) t.toNat := by
    have h₂s : Sorts B₁ B₂ (p + (n >>> 1) * 4#32).toNat (n - n >>> 1).toNat t.toNat := h₂
    rwa [ha, hl] at h₂s
  exact sorts_compose (by omega) hd h₁' h₂' h₃

set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
/-- **The 5 conditions of `merge_sort`**, for every bound `N`. -/
theorem msort_vcs (N : Nat) :
    AllValid (msFns N) (genFunc msortSpec Silmaril.WasmSpec.MergeSort.sortFunc msortFuel) := by
  vcgen4
  all_goals (try simp only [and_imp]; intros; subst_vars)
  · exact c_base ‹_› ‹_›
  · exact c_call1 ‹_› ‹_›
  · exact c_call2 ‹_› ‹_› ‹_›
  · exact c_merge ‹_› ‹_› ‹_› ‹_›
  · exact c_post ‹_› ‹_› ‹_› ‹_›

end Silmaril.Wasm.Auto2.VCMSort

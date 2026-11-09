module

public import Silmaril.X86.Ladder.ZlibChecksums.Rfc1950.Defs
public import Silmaril.X86.Ladder.ZlibChecksums.Spec.Thms

/-!
# The reference `adler32` is RFC 1950's Adler-32

* `rawFold_eq`: the unreduced sums (`AccumFold.rawFold`) from `(s1, s2)` are
  `(rfcA s1 bs, rfcB s1 s2 bs)`;
* `adler32_eq_rfcFrom`: `Spec.adler32 a bs = rfcFrom a bs` whenever both 16-bit halves of `a`
  are `< 65521` (the `AdlerOk` condition of the `adler32_z` contract);
* `adler32_one_eq_rfc1950`: `Spec.adler32 1 bs = rfc1950 bs` (the initial value `1`);
* `rfcB_weighted`: RFC 1950's second form, `B = n + Σ (n − i) × D(i+1)` (from `s1 = 1`,
  `s2 = 0`);
* `rfc1950_check`: `rfc1950 "Wikipedia" = 0x11e60398`.
-/

@[expose] public section

namespace Silmaril.X86.Ladder.ZlibChecksums.Rfc1950

open Silmaril.X86 (Byte)

open Silmaril.X86.Stencils.AccumFold (rawFold rawStep modFold red)
open Silmaril.X86.Ladder.ZlibChecksums

theorem rfcA_append (s1 : Nat) (bs : List Byte) (d : Byte) :
    rfcA s1 (bs ++ [d]) = rfcA s1 bs + d.toNat := by
  simp [rfcA, Nat.add_assoc]

theorem rfcB_append (s1 s2 : Nat) (bs : List Byte) (d : Byte) :
    rfcB s1 s2 (bs ++ [d]) = rfcB s1 s2 bs + rfcA s1 (bs ++ [d]) := by
  simp only [rfcB, List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hmap : (List.range bs.length).map (fun j => rfcA s1 ((bs ++ [d]).take (j + 1))) =
      (List.range bs.length).map (fun j => rfcA s1 (bs.take (j + 1))) := by
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    rw [List.take_append_of_le_length (by omega)]
  rw [hmap, List.take_of_length_le (by simp)]
  omega

theorem getD_snoc {bs : List Byte} {d : Byte} {i : Nat} (hi : i < bs.length) :
    (bs ++ [d]).getD i 0 = bs.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem rawFold_eq (s1 s2 : Nat) (bs : List Byte) :
    rawFold (s1, s2) bs = (rfcA s1 bs, rfcB s1 s2 bs) := by
  induction bs using List.reverseRecOn with
  | nil => simp [rawFold, rfcA, rfcB]
  | append_singleton bs d ih =>
    simp only [rawFold, List.foldl_append] at ih ⊢
    rw [ih]
    simp only [List.foldl_cons, List.foldl_nil, rawStep, rfcA_append, rfcB_append, Prod.mk.injEq,
      true_and]
    omega

theorem adler32_eq_rfcFrom (a : Nat) (bs : List Byte) (h1 : a % 65536 < 65521)
    (h2 : a / 65536 % 65536 < 65521) : adler32 a bs = rfcFrom a bs := by
  have hs : adlerStart a = (a % 65536, a / 65536 % 65536) := by
    simp only [adlerStart, red, BASE, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  have hr := Silmaril.X86.Stencils.AccumFold.rawFold_mod BASE (adlerStart a) bs
  have hred : red BASE (adlerStart a) = adlerStart a := by
    rw [hs]; simp only [red, BASE, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  rw [hred] at hr
  rw [adler32, ← hr, hs, rawFold_eq]
  simp [adlerPack, red, rfcFrom, BASE]

theorem adler32_one_eq_rfc1950 (bs : List Byte) : adler32 1 bs = rfc1950 bs := by
  rw [adler32_eq_rfcFrom 1 bs (by decide) (by decide)]; rfl

/-- RFC 1950's weighted form of `B`: `n × D1 + (n − 1) × D2 + … + Dn + n`. -/
theorem rfcB_weighted (bs : List Byte) :
    rfcB 1 0 bs = bs.length +
      ((List.range bs.length).map fun i => (bs.length - i) * (bs.getD i 0).toNat).sum := by
  induction bs using List.reverseRecOn with
  | nil => simp [rfcB]
  | append_singleton bs d ih =>
    rw [rfcB_append, ih]
    simp only [List.length_append, List.length_singleton, List.range_succ, List.map_append,
      List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.add_sub_cancel_left, Nat.one_mul]
    have e : ∀ i ∈ List.range bs.length,
        (bs.length + 1 - i) * ((bs ++ [d]).getD i 0).toNat =
          (bs.length - i) * (bs.getD i 0).toNat + (bs.getD i 0).toNat := by
      intro i hi
      rw [List.mem_range] at hi
      rw [getD_snoc hi, show bs.length + 1 - i = (bs.length - i) + 1 by omega,
        Nat.succ_mul]
    rw [List.map_congr_left e]
    have hsum : ∀ (l : List Nat) (f g : Nat → Nat),
        (l.map fun i => f i + g i).sum = (l.map f).sum + (l.map g).sum := by
      intro l f g; induction l with
      | nil => simp
      | cons x xs ih => simp [List.sum_cons, ih]; omega
    rw [hsum]
    have hA : ((List.range bs.length).map fun i => (bs.getD i 0).toNat).sum =
        (bs.map (·.toNat)).sum := by
      clear e ih
      induction bs using List.reverseRecOn with
      | nil => simp
      | append_singleton bs d' ih' =>
        simp only [List.length_append, List.length_singleton, List.range_succ, List.map_append,
          List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have e' : ∀ i ∈ List.range bs.length,
            ((bs ++ [d']).getD i 0).toNat = (bs.getD i 0).toNat := by
          intro i hi; rw [List.mem_range] at hi; rw [getD_snoc hi]
        rw [List.map_congr_left e', ih']
        simp [List.getD_eq_getElem?_getD]
    rw [hA, rfcA_append]
    simp only [rfcA]
    have : (bs ++ [d]).getD bs.length 0 = d := by simp
    rw [this]; omega

theorem rfc1950_check :
    rfc1950 [0x57, 0x69, 0x6b, 0x69, 0x70, 0x65, 0x64, 0x69, 0x61] = 0x11e60398 := by
  decide +kernel

end Silmaril.X86.Ladder.ZlibChecksums.Rfc1950

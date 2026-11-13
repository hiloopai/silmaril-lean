module

public import Silmaril.Raw.Project.WasmP3Rust.StdioK.Inv

/-!
# Lowering `list<string>` and reading it back

`DenX.lowerArgs` lays a `list<string>` out in the core layer's memory as the Canonical ABI does
(an array of `(ptr, len)` pairs, one block per string, from `realloc`); `argStrs` reads it back
by addresses as the code of `echo` does. With `stdioK`'s bump allocator from `heapA`, the
strings read back are the strings lowered (`lowerArgs_spec`): the array and every non-empty
string are at distinct addresses, and an empty string reads back empty wherever it points.
-/

@[expose] public section

namespace Silmaril.Raw.Project.WasmP3Rust.StdioK

open Silmaril.Project.WasmP3Rust.DenX Silmaril.Project.WasmP3Rust.StdioK
open Silmaril.Project.WasmP3Rust.Den (le32)

variable {P : Plan}

/-- A block stored at `p`. -/
def pushB (c : SConf) (p : Nat) (bs : List (BitVec 8)) : SConf :=
  { c with mem := (p, bs) :: c.mem }

theorem alloc_eq (c : (stdioK P).Conf) (size a : Nat) :
    (stdioK P).alloc c size a =
      if c.next + size < 2 ^ 32 then some ({ c with next := c.next + size }, c.next) else none := rfl

theorem store_eq (c : (stdioK P).Conf) (p : Nat) (bs : List (BitVec 8)) :
    (stdioK P).store c p bs = some (store c p bs) := rfl

theorem store_heap {p : Nat} (hp : heapA ≤ p) (c : SConf) (bs : List (BitVec 8)) :
    store c p bs = pushB c p bs := by
  have h0 : p ≠ 0 := by unfold heapA at hp; omega
  have h1 : p ≠ retA := by unfold heapA at hp; unfold retA; omega
  have h2 : p ≠ futA := by unfold heapA at hp; unfold futA; omega
  simp only [store, h0, h1, h2, ite_false, pushB]

theorem at_push (c : SConf) (p q : Nat) (bs : List (BitVec 8)) :
    (pushB c p bs).at q = if q = p then bs else c.at q := by
  unfold SConf.at pushB
  by_cases h : q = p
  · subst h; simp
  · have h' : ¬ p = q := fun e => h e.symm
    simp [h, h']

theorem at_of_mem {c c' : SConf} (h : c'.mem = c.mem) (q : Nat) : c'.at q = c.at q := by
  unfold SConf.at; rw [h]

/-- **The strings lowered from index `i` on read back.** -/
theorem lowerStrs_spec (arr : Nat) (harr : heapA ≤ arr) :
    ∀ (ss : List (List (BitVec 8))) (i : Nat) (x y : SConf),
      lowerStrs (stdioK P) arr i ss x = some y → arr + 8 * (i + ss.length) ≤ x.next →
      (∀ p, p < x.next → (∀ k, k < ss.length → p ≠ arr + 8 * (i + k)) → y.at p = x.at p) ∧
      (∀ j (hj : j < ss.length),
        (y.at (dec32 ((y.at (arr + 8 * (i + j))).take 4))).take
          (dec32 ((y.at (arr + 8 * (i + j))).drop 4)) = ss[j]) ∧
      x.next ≤ y.next ∧ y.pc = x.pc
  | [], i, x, y, h, _ => by
    obtain rfl : x = y := Option.some.inj h
    exact ⟨fun _ _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _), Nat.le_refl _, rfl⟩
  | s :: ss, i, x, y, h, hb => by
    simp only [List.length_cons] at hb
    have hx1 : heapA ≤ x.next := by omega
    have hai : heapA ≤ arr + 8 * i := by omega
    simp only [lowerStrs] at h
    obtain ⟨⟨x1, q⟩, ha, h1⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨x2, hs2, h2⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨x3, hs3, h3⟩ := Option.bind_eq_some_iff.1 h2
    change (if x.next + s.length < 2 ^ 32 then
      some (({ x with next := x.next + s.length } : SConf), x.next) else none) = some (x1, q) at ha
    split at ha
    · rename_i hlt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ha)
      change some (store _ x.next s) = some x2 at hs2
      have e2 : x2 = pushB ({ x with next := x.next + s.length } : SConf) x.next s := by
        rw [← Option.some.inj hs2]; exact store_heap hx1 _ _
      subst e2
      change some (store _ (arr + 8 * i) (le32 x.next ++ le32 s.length)) = some x3 at hs3
      have hX : pushB (pushB ({ x with next := x.next + s.length } : SConf) x.next s)
          (arr + 8 * i) (le32 x.next ++ le32 s.length) = x3 := by
        rw [← Option.some.inj hs3]; exact (store_heap hai _ _).symm
      have hn3 : x3.next = x.next + s.length := by rw [← hX]; rfl
      have hat3 : ∀ q, x3.at q =
          if q = arr + 8 * i then le32 x.next ++ le32 s.length
          else if q = x.next then s else x.at q := by
        intro q
        rw [← hX, at_push, at_push]; rfl
      obtain ⟨ih1, ih2, ih3, ih4⟩ := lowerStrs_spec arr harr ss (i + 1) x3 y h3 (by omega)
      have hp32 : x.next < 2 ^ 32 := by omega
      have hs32 : s.length < 2 ^ 32 := by omega
      have hpc : x3.pc = x.pc := by rw [← hX]; rfl
      refine ⟨fun p hp hk => ?_, fun j hj => ?_, by omega, ih4.trans hpc⟩
      · simp only [List.length_cons] at hk
        rw [ih1 p (by omega) (fun k hk' => by have := hk (k + 1) (by omega); omega), hat3]
        have h0 := hk 0 (by omega)
        simp only [Nat.add_zero] at h0
        simp only [h0, ite_false, show p ≠ x.next by omega]
      · simp only [List.length_cons] at hj
        cases j with
        | zero =>
          have ha : y.at (arr + 8 * (i + 0)) = le32 x.next ++ le32 s.length := by
            rw [Nat.add_zero, ih1 _ (by omega) (fun k _ => by omega), hat3]
            simp
          rw [ha, dec32_take _ _ hp32, dec32_drop _ _ hs32]
          simp only [List.getElem_cons_zero]
          by_cases hs0 : s.length = 0
          · rw [hs0, List.take_zero, List.eq_nil_of_length_eq_zero hs0]
          · rw [ih1 _ (by omega) (fun k _ => by omega), hat3]
            simp only [show x.next ≠ arr + 8 * i by omega, ite_false, ite_true, List.take_length]
        | succ j =>
          have e : arr + 8 * (i + (j + 1)) = arr + 8 * (i + 1 + j) := by omega
          rw [e, ih2 j (by simpa using hj)]
          simp
    · cases ha

/-- **`echo` reads back the arguments `DenX.den` lowered.** -/
theorem lowerArgs_spec {x z : SConf} {ss : List (List (BitVec 8))}
    (h : lowerArgs (stdioK P) x retA ss = some z) (hn : x.next = heapA) :
    z.pc = x.pc ∧ argStrs z = ss := by
  simp only [lowerArgs] at h
  obtain ⟨⟨x1, arr⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.1 h
  change (if x.next + 8 * ss.length < 2 ^ 32 then
    some (({ x with next := x.next + 8 * ss.length } : SConf), x.next) else none) =
      some (x1, arr) at ha
  split at ha
  · rename_i hlt
    rw [hn] at hlt
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ha)
    change some (store y retA (le32 x.next ++ le32 ss.length)) = some z at h
    obtain rfl := Option.some.inj h
    rw [hn] at hy
    obtain ⟨-, h2, -, h4⟩ := lowerStrs_spec heapA (Nat.le_refl _) ss 0 _ y hy
      (by simp only [Nat.zero_add]; exact Nat.le_refl _)
    have hst : store y retA (le32 x.next ++ le32 ss.length) =
        { y with ret := le32 x.next ++ le32 ss.length } := by
      simp [store, retA]
    rw [hst, hn]
    refine ⟨h4, ?_⟩
    have hh : heapA < 2 ^ 32 := by unfold heapA; omega
    have hl : ss.length < 2 ^ 32 := by omega
    simp only [argStrs, dec32_take _ _ hh, dec32_drop _ _ hl]
    apply List.ext_getElem (by simp)
    intro j hj1 hj2
    simp only [List.getElem_map, List.getElem_range]
    have := h2 j hj2
    simp only [Nat.zero_add] at this
    exact this
  · cases ha

end Silmaril.Raw.Project.WasmP3Rust.StdioK

end

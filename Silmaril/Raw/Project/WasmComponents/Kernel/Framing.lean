module

public import Silmaril.Project.WasmComponents.Kernel.Framing.Defs

/-!
# Kernel decoders: the list framing is the framing (raw proofs)

Valid, unrefined proofs behind `Silmaril.Project.WasmComponents.Kernel.Framing.Thms` (the header
to import): `uAux_of_uAuxL`, `coreSectionsFrom_of_framesL`, `name_of_nameL` and their helpers.
They are long case analyses of the cursor parsers and are not yet in the Isar style of
`docs/projects/wasm-wasi.md`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

open Silmaril.Parse.ByteParse (Parser Res)
open Silmaril.Wasm.Wit.Binary

theorem extract_eq_sliceOf (b : ByteArray) (i j : Nat) : b.extract i j = sliceOf b i j := by
  apply ByteArray.ext
  apply Array.ext'
  rw [ByteArray.data_extract, Array.toList_extract]
  simp only [sliceOf, List.extract_eq_take_drop]

theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := rfl

/-- What `uAuxL` leaves is a proper suffix of its input. -/
theorem uAuxL_suffix : ∀ {w : List UInt8} {bud sh acc v : Nat} {r : List UInt8},
    uAuxL bud sh acc w = some (v, r) → r = w.drop (w.length - r.length) ∧ r.length < w.length
  | [], _, _, _, _, _, h => by simp [uAuxL] at h
  | x :: w, bud, sh, acc, v, r, h => by
    unfold uAuxL at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp
      · cases h
    · split at h
      · obtain ⟨e, hl⟩ := uAuxL_suffix h
        refine ⟨?_, by simp; omega⟩
        have : (x :: w).length - r.length = (w.length - r.length) + 1 := by simp; omega
        rw [this, List.drop_succ_cons]
        exact e
      · cases h

/-- The window `bs[i:s]` starts with `bs[i]` when it is not empty. -/
theorem window_cons {b : ByteArray} {i s : Nat} (hs : i < s) (hb : i < b.size) :
    (b.data.toList.drop i).take (s - i) =
      b[i] :: (b.data.toList.drop (i + 1)).take (s - (i + 1)) := by
  have hl : i < b.data.toList.length := hb
  rw [List.drop_eq_getElem_cons hl, show s - i = (s - (i + 1)) + 1 by omega, List.take_succ_cons]
  rfl

/-- **LEB128 on the window's list is the cursor parser's run.** -/
theorem uAux_of_uAuxL {b : ByteArray} {s : Nat} (hsb : s ≤ b.size) :
    ∀ {w : List UInt8} {i bud sh acc v : Nat} {r : List UInt8},
      w = (b.data.toList.drop i).take (s - i) → i ≤ s → uAuxL bud sh acc w = some (v, r) →
      Silmaril.Parse.ByteParse.uAux bud sh acc b s i = .ok v (s - r.length)
  | [], i, bud, sh, acc, v, r, _, _, h => by simp [uAuxL] at h
  | x :: w, i, bud, sh, acc, v, r, hw, hi, h => by
    have hlen : ((b.data.toList.drop i).take (s - i)).length = s - i := by
      have := size_eq_length b; simp only [List.length_take, List.length_drop]; omega
    have hs : i < s := by
      rcases Nat.lt_or_ge i s with h' | h'
      · exact h'
      · rw [← hw] at hlen; simp at hlen; omega
    have hb : i < b.size := by omega
    rw [window_cons hs hb] at hw
    simp only [List.cons.injEq] at hw
    obtain ⟨rfl, hw'⟩ := hw
    have hwl : w.length = s - (i + 1) := by
      rw [hw']; have := size_eq_length b; simp only [List.length_take, List.length_drop]; omega
    unfold Silmaril.Parse.ByteParse.uAux
    rw [dite_eq_left hs, dite_eq_left hb]
    unfold uAuxL at h
    split at h
    · rename_i h1
      rw [ite_eq_left h1]
      split at h
      · rename_i h2
        rw [ite_eq_left h2]
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        congr 1
        omega
      · cases h
    · rename_i h1
      rw [ite_eq_right h1]
      split at h
      · rename_i h2
        rw [ite_eq_left h2]
        exact uAux_of_uAuxL hsb hw' (by omega) h
      · cases h

/-- The window from `i` to the end is the rest of the list. -/
theorem window_end (b : ByteArray) (i : Nat) :
    (b.data.toList.drop i).take (b.size - i) = b.data.toList.drop i := by
  apply List.take_of_length_le
  simp only [List.length_drop]; have := size_eq_length b; omega

/-- **The list framing is `coreSectionsFrom`.** -/
theorem coreSectionsFrom_of_framesL {b : ByteArray} :
    ∀ {fuel i : Nat} {t : List (UInt8 × Nat × Nat)}, i ≤ b.size →
      framesL fuel i (b.data.toList.drop i) = some t → coreSectionsFrom b fuel i = .ok t
  | 0, _, _, _, h => by simp [framesL] at h
  | fuel + 1, i, t, hi, h => by
    unfold coreSectionsFrom
    rcases hd : b.data.toList.drop i with _ | ⟨x, r⟩
    · rw [hd] at h
      simp only [framesL, Option.some.injEq] at h
      subst h
      have : ¬ i < b.size := by
        intro hlt
        have := congrArg List.length hd
        simp only [List.length_drop, List.length_nil] at this; have := size_eq_length b; omega
      rw [dite_eq_right this]; rfl
    · rw [hd] at h
      have hb : i < b.size := by
        rcases Nat.lt_or_ge i b.size with h' | h'
        · exact h'
        · have := congrArg List.length hd; simp only [List.length_drop, List.length_cons] at this; have := size_eq_length b; omega
      rw [dite_eq_left hb]
      have hl : i < b.data.toList.length := hb
      rw [List.drop_eq_getElem_cons hl] at hd
      simp only [List.cons.injEq] at hd
      obtain ⟨hx, hr⟩ := hd
      have hrl : r.length = b.size - (i + 1) := by
        rw [← hr, List.length_drop]; rfl
      simp only [framesL] at h
      split at h
      · rename_i n r' hu
        split at h
        · rename_i hn
          obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨hsuf, hlt⟩ := uAuxL_suffix hu
          have hu' := uAux_of_uAuxL (le_refl _) (w := r) (i := i + 1)
            (by rw [window_end]; exact hr.symm) (by omega) hu
          show (match Silmaril.Parse.ByteParse.uAux 32 0 0 b b.size (i + 1) with
            | Res.ok n j => if j + n ≤ b.size then ((b[i], j, j + n) :: ·) <$> coreSectionsFrom b fuel (j + n)
                else throw s!"section at offset {i} exceeds the module"
            | Res.err _ => throw s!"malformed section size at offset {i + 1}") = _
          rw [hu']
          dsimp only
          have hj : b.size - r'.length = i + 1 + (r.length - r'.length) := by omega
          rw [hj, ite_eq_left (by omega)]
          have hdrop : r'.drop n = b.data.toList.drop (i + 1 + (r.length - r'.length) + n) := by
            subst hr
            conv_lhs => rw [hsuf]
            rw [List.drop_drop, List.drop_drop]
            congr 1; omega
          rw [hdrop] at ht'
          rw [coreSectionsFrom_of_framesL (by omega) ht']
          have : b[i] = x := by
            rw [← hx]; simp [ByteArray.getElem_eq_getElem_data]
          rw [this]; rfl
        · cases h
      · cases h

/-- **The `name` parser on the window's list.** -/
theorem name_of_nameL {b : ByteArray} {s i : Nat} (hi : i ≤ s) (hs : s ≤ b.size) {str : String}
    {k : Nat} (h : nameL ((b.data.toList.drop i).take (s - i)) = some (str, k)) :
    Silmaril.Parse.ByteParse.name b s i = .ok str (i + k) := by
  unfold nameL at h
  split at h
  · rename_i n r hu
    split at h
    · rename_i hn
      obtain ⟨str', hstr, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hwl : ((b.data.toList.drop i).take (s - i)).length = s - i := by
        have := size_eq_length b; simp only [List.length_take, List.length_drop]; omega
      obtain ⟨hsuf, hlt⟩ := uAuxL_suffix hu
      have hu' := uAux_of_uAuxL hs rfl hi hu
      unfold Silmaril.Parse.ByteParse.name Silmaril.Parse.ByteParse.count Silmaril.Parse.ByteParse.u32
        Silmaril.Parse.ByteParse.uN
      rw [hu']
      dsimp only
      rw [ite_eq_left (by omega)]
      dsimp only
      unfold Silmaril.Parse.ByteParse.utf8
      rw [ite_eq_left (by omega), extract_eq_sliceOf]
      have hsl : sliceOf b (s - r.length) (s - r.length + n) = ⟨⟨r.take n⟩⟩ := by
        unfold sliceOf
        congr 2
        conv_rhs => rw [hsuf]
        rw [List.drop_take, List.drop_drop, List.take_take, hwl]
        have e1 : s - r.length + n - (s - r.length) = n := by omega
        have e2 : min n (s - i - (s - i - r.length)) = n := by omega
        have e3 : i + (s - i - r.length) = s - r.length := by omega
        rw [e1, e2, e3]
      rw [hsl, hstr, hwl]
      dsimp only
      congr 1
      omega
    · cases h
  · cases h

end Silmaril.Project.WasmComponents.Kernel

end

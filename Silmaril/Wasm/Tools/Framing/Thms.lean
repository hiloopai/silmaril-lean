module

public import Silmaril.Wasm.Tools.Framing.Defs

/-!
# Section framing: theorems

* `readUN_sound`, `readUN_complete`: `readUN N` reads exactly silmaril-lean's grammar `UN N`
  (LEB128 bounded to `N` bits), so `readU32` is the specification's `u32`;
* `encUN_un`: the minimal encoding is in the grammar;
* `splitSecsF_sound`, **`splitSecs_sound`**: the sections reassemble to the input and their
  size fields are well formed; **`splitSecs_join`**: conversely, well-formed sections are split
  back exactly (so framing is a bijection between byte strings and well-formed section lists);
* `canon_sizesOk`: minimal size fields are well formed (contents under 4 GiB).

New theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Framing

open Silmaril.Wasm.Binary (Bytes UN U32)

theorem readUN_sound : ∀ {N : Nat} {b : Bytes} {v : Nat} {lb r : Bytes},
    readUN N b = some (v, lb, r) → b = lb ++ r ∧ UN N lb v
  | _, [], _, _, _, h => by simp [readUN] at h
  | N, n :: b, v, lb, r, h => by
    by_cases h1 : n.toNat < 2 ^ 7
    · by_cases h2 : n.toNat < 2 ^ N
      · simp only [readUN, h1, h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, .byte n h1 h2⟩
      · simp [readUN, h1, h2] at h
    · by_cases h7 : 7 < N
      · simp only [readUN, h1, h7, ↓reduceIte] at h
        split at h
        · rename_i m lb' r' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, rfl, rfl⟩ := h
          obtain ⟨rfl, hu⟩ := readUN_sound hr
          subst hv
          exact ⟨rfl, .cont n (by omega) h7 hu⟩
        · cases h
      · simp [readUN, h1, h7] at h

theorem readUN_complete {N : Nat} {lb : Bytes} {v : Nat} (h : UN N lb v) (r : Bytes) :
    readUN N (lb ++ r) = some (v, lb, r) := by
  induction h with
  | byte n h₁ h₂ =>
    simp [readUN, h₁, h₂]
  | cont n h₁ h₂ rest ih =>
    have h₁' : ¬ n.toNat < 2 ^ 7 := by omega
    simp only [List.cons_append, readUN, h₁', ↓reduceIte, h₂, ih]

theorem toNat_toUInt8_of_lt {n : Nat} (h : n < 2 ^ 8) : n.toUInt8.toNat = n := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
  omega

theorem encUN_un : ∀ {N n : Nat}, n < 2 ^ N → UN N (encUN n) n
  | N, n, h => by
    rw [encUN]
    by_cases hn : n < 2 ^ 7
    · simp only [hn, ↓reduceDIte]
      have hb := UN.byte (N := N) n.toUInt8 (by rw [toNat_toUInt8_of_lt (by omega)]; exact hn)
        (by rw [toNat_toUInt8_of_lt (by omega)]; exact h)
      rwa [toNat_toUInt8_of_lt (by omega)] at hb
    · simp only [hn, ↓reduceDIte]
      have h7 : 7 < N := by
        apply Classical.byContradiction
        intro hN
        have : 2 ^ N ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hq : n / 2 ^ 7 < 2 ^ (N - 7) := by
        rw [Nat.div_lt_iff_lt_mul (by decide), ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        exact h
      have hrest := encUN_un hq
      have hm : n % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt _ (by decide)
      have hv : (n % 2 ^ 7 + 2 ^ 7).toUInt8.toNat = n % 2 ^ 7 + 2 ^ 7 :=
        toNat_toUInt8_of_lt (by omega)
      have hc := UN.cont (N := N) (n % 2 ^ 7 + 2 ^ 7).toUInt8 (by rw [hv]; omega) h7 hrest
      have heq : 2 ^ 7 * (n / 2 ^ 7) + ((n % 2 ^ 7 + 2 ^ 7).toUInt8.toNat - 2 ^ 7) = n := by
        rw [hv]
        have := Nat.div_add_mod n (2 ^ 7)
        omega
      rwa [heq] at hc
termination_by _ n => n

theorem atLeast_iff {α : Type} : ∀ (n : Nat) (l : List α), atLeast n l = true ↔ n ≤ l.length
  | 0, _ => by simp [atLeast]
  | _ + 1, [] => by simp [atLeast]
  | n + 1, _ :: r => by simp [atLeast, atLeast_iff n r]

theorem RawSec.bytes_length (s : RawSec) :
    s.bytes.length = 1 + s.size.length + s.content.length := by
  simp [RawSec.bytes]; omega

theorem join_append (a b : List RawSec) : join (a ++ b) = join a ++ join b := by
  induction a with
  | nil => rfl
  | cons s a ih => simp [join, ih]

theorem splitSecsF_sound : ∀ (fuel : Nat) {b : Bytes} {ss : List RawSec},
    splitSecsF fuel b = some ss → join ss = b ∧ SizesOk ss
  | _, [], ss, h => by
    simp only [splitSecsF, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | 0, _ :: _, _, h => by simp [splitSecsF] at h
  | fuel + 1, id :: rest, ss, h => by
    simp only [splitSecsF] at h
    split at h
    · cases h
    · rename_i len lb r hr
      split at h
      · rename_i hlen'
        have hlen : len ≤ r.length := (atLeast_iff len r).mp hlen'
        obtain ⟨ss', hs', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hj, hok⟩ := splitSecsF_sound fuel hs'
        obtain ⟨rfl, hu⟩ := readUN_sound hr
        refine ⟨?_, ?_⟩
        · simp only [join, RawSec.bytes, hj, List.cons_append, List.append_assoc,
            List.take_append_drop]
        · intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · simpa [List.length_take, Nat.min_eq_left hlen] using hu
          · exact hok s hs
      · cases h

/-- **Framing is sound**: the sections reassemble to the input, with well-formed sizes. -/
theorem splitSecs_sound {b : Bytes} {ss : List RawSec} (h : splitSecs b = some ss) :
    join ss = b ∧ SizesOk ss :=
  splitSecsF_sound _ h

theorem splitSecsF_join : ∀ {ss : List RawSec} (fuel : Nat), SizesOk ss → ss.length ≤ fuel →
    splitSecsF fuel (join ss) = some ss
  | [], fuel, _, _ => by cases fuel <;> rfl
  | s :: ss, fuel, hok, hlen => by
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    have hs := hok s (List.mem_cons_self ..)
    have hrest : SizesOk ss := fun t ht => hok t (List.mem_cons_of_mem _ ht)
    have hr := readUN_complete hs (s.content ++ join ss)
    simp only [join, RawSec.bytes, List.cons_append, splitSecsF, readU32, List.append_assoc]
    rw [hr]
    have hat : atLeast s.content.length (s.content ++ join ss) = true :=
      (atLeast_iff _ _).mpr (by simp)
    simp only [hat, ↓reduceIte, List.drop_left, List.take_left]
    rw [splitSecsF_join fuel hrest (by simp at hlen; omega)]
    rfl

theorem length_le_join (ss : List RawSec) : ss.length ≤ (join ss).length := by
  induction ss with
  | nil => simp [join]
  | cons s ss ih => simp [join, RawSec.bytes]; omega

/-- **Framing is complete**: well-formed sections are split back exactly. -/
theorem splitSecs_join {ss : List RawSec} (h : SizesOk ss) : splitSecs (join ss) = some ss :=
  splitSecsF_join _ h (length_le_join ss)

/-- Minimal size fields are well formed. -/
theorem canon_sizesOk {ss : List RawSec} (h : ∀ s ∈ ss, s.content.length < 2 ^ 32) :
    SizesOk (ss.map RawSec.canon) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact encUN_un (h t ht)

end Silmaril.Wasm.Tools.Framing

module

public import Silmaril.X86.Ext.Wire.Prefix

/-!
# Complete byte-faithful image walks

A successful walk consumes the entire input, preserving original instruction
spellings. It establishes coverage in this local model, not execution or
reference-ISA equivalence. `sum_decodeLengths` counts actual consumed bytes.
-/

@[expose] public section

namespace Silmaril.X86.Ext.Wire

open Silmaril.X86 (Byte)

def decodeAll : Nat → List Byte → Option (List Decoded)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, bytes =>
    match decode bytes with
    | none => none
    | some d => (decodeAll fuel (bytes.drop d.length)).map (d :: ·)

def decodeLengths (fuel : Nat) (bytes : List Byte) : Option (List Nat) :=
  (decodeAll fuel bytes).map (·.map Decoded.length)

/-- A successful walk reconstructs every original byte in order. -/
theorem decodeAll_eq_flatten : ∀ (fuel : Nat) {bytes : List Byte} {ds : List Decoded},
    decodeAll fuel bytes = some ds → bytes = (ds.map encode).flatten := by
  intro fuel
  induction fuel with
  | zero =>
    intro bytes ds h
    cases bytes with
    | nil => simp only [decodeAll, Option.some.injEq] at h; subst h; simp
    | cons b t => simp [decodeAll] at h
  | succ fuel ih =>
    intro bytes ds h
    cases bytes with
    | nil => simp only [decodeAll, Option.some.injEq] at h; subst h; simp
    | cons b t =>
      simp only [decodeAll] at h
      split at h
      · simp at h
      · rename_i d hd
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨tail, htail, rfl⟩ := h
        rw [List.map_cons, List.flatten_cons, ← ih htail]
        exact (decode_sound hd).2.2.2

/-- The consumed lengths sum to the byte length, with no skipped prefixes. -/
theorem sum_decodeLengths {fuel : Nat} {bytes : List Byte} {lengths : List Nat}
    (h : decodeLengths fuel bytes = some lengths) : lengths.sum = bytes.length := by
  unfold decodeLengths at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨ds, hall, rfl⟩ := h
  rw [decodeAll_eq_flatten fuel hall]
  clear hall
  induction ds with
  | nil => simp
  | cons d rest ih => simpa [Decoded.length, encode] using ih

/-- All instructions of a successful walk round-trip their original bytes. -/
theorem decodeAll_roundtrip : ∀ (fuel : Nat) {bytes : List Byte} {ds : List Decoded},
    decodeAll fuel bytes = some ds → ∀ d ∈ ds, decode (encode d) = some d := by
  intro fuel
  induction fuel with
  | zero =>
    intro bytes ds h
    cases bytes with
    | nil => simp [decodeAll] at h; subst h; simp
    | cons b t => simp [decodeAll] at h
  | succ fuel ih =>
    intro bytes ds h
    cases bytes with
    | nil => simp [decodeAll] at h; subst h; simp
    | cons b t =>
      simp only [decodeAll] at h
      split at h
      · simp at h
      · rename_i d hd
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨tail, htail, rfl⟩ := h
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact decode_encode hd
        · exact ih htail e he

/-- Successful walks remain successful with additional fuel. -/
theorem decodeAll_mono : ∀ (fuel : Nat) {bytes : List Byte} {ds : List Decoded},
    decodeAll fuel bytes = some ds →
    ∀ more, decodeAll (fuel + more) bytes = some ds := by
  intro fuel
  induction fuel with
  | zero =>
    intro bytes ds h more
    cases bytes with
    | nil => simpa [decodeAll] using h
    | cons b t => simp [decodeAll] at h
  | succ fuel ih =>
    intro bytes ds h more
    cases bytes with
    | nil => simpa [decodeAll] using h
    | cons b t =>
      have hadd : fuel + 1 + more = (fuel + more) + 1 := by omega
      rw [hadd]
      cases hd : decode (b :: t) with
      | none => simp [decodeAll, hd] at h
      | some d =>
        simp only [decodeAll, hd, Option.map_eq_some_iff] at h ⊢
        obtain ⟨tail, htail, rfl⟩ := h
        exact ⟨tail, ih htail more, rfl⟩

/-- Concatenate complete image chunks without re-proving their decoder walks. -/
theorem decodeAll_append : ∀ (fuel : Nat) {bytes : List Byte} {ds : List Decoded},
    decodeAll fuel bytes = some ds → ∀ {moreFuel : Nat} {more : List Byte} {es : List Decoded},
    decodeAll moreFuel more = some es →
    decodeAll (fuel + moreFuel) (bytes ++ more) = some (ds ++ es) := by
  intro fuel
  induction fuel with
  | zero =>
    intro bytes ds h moreFuel more es he
    cases bytes with
    | nil => simp only [decodeAll, Option.some.injEq] at h; subst h; simpa using he
    | cons b t => simp [decodeAll] at h
  | succ fuel ih =>
    intro bytes ds h moreFuel more es he
    cases bytes with
    | nil =>
      simp only [decodeAll, Option.some.injEq] at h
      subst h
      simpa [Nat.add_comm] using decodeAll_mono moreFuel he (fuel + 1)
    | cons b t =>
      cases hd : decode (b :: t) with
      | none => simp [decodeAll, hd] at h
      | some d =>
        simp only [decodeAll, hd, Option.map_eq_some_iff] at h
        obtain ⟨tail, htail, rfl⟩ := h
        have bound : d.length ≤ (b :: t).length := by
          have hx := congrArg List.length (decode_sound hd).2.2.1
          simp only [encode, Decoded.length, List.length_take] at hx
          change d.bytes.length ≤ (b :: t).length
          omega
        have hadd : fuel + 1 + moreFuel = (fuel + moreFuel) + 1 := by omega
        rw [hadd]
        have hdapp : decode (b :: (t ++ more)) = some d := decode_append hd more
        have hdrop : (b :: (t ++ more)).drop d.length = (b :: t).drop d.length ++ more :=
          List.drop_append_of_le_length bound
        simp only [List.cons_append, decodeAll, hdapp, hdrop, ih htail he, Option.map_some]

/-- Length walks of complete chunks compose using actual consumed lengths. -/
theorem decodeLengths_append {fuel moreFuel : Nat} {bytes more : List Byte} {ns ms : List Nat}
    (h : decodeLengths fuel bytes = some ns) (hm : decodeLengths moreFuel more = some ms) :
    decodeLengths (fuel + moreFuel) (bytes ++ more) = some (ns ++ ms) := by
  simp only [decodeLengths, Option.map_eq_some_iff] at h hm
  obtain ⟨ds, hd, rfl⟩ := h
  obtain ⟨es, he, rfl⟩ := hm
  simp [decodeLengths, decodeAll_append fuel hd he]

end Silmaril.X86.Ext.Wire

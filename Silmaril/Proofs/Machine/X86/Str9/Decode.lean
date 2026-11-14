module

public import Silmaril.Machine.X86.Str9.Defs
public import Silmaril.Machine.X86.Ext9.Thms

/-!
# `Str9`: decoder laws

Proofs for `Silmaril/Machine/X86/Str9/Thms.lean`.

* `decodeStr_append`: a decoded string form keeps its reading whatever bytes follow.
* `decodeStr_some`: a decoded form is its own encoding, a prefix of the bytes.
* `decodeStr_none_of_key`: bytes that start with a key of a table disjoint from `table` are
  not a string form.
* `decodeL_spec`, `decodeNew_none_of_bad`: what a listed string form is.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Str9

open Silmaril.X86 (Byte maxInstrLength)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.Str9

/-- A decoded form is its own encoding, at the front of the bytes. -/
theorem decodeStr_some {bytes : List Byte} {i : Str} {n : Nat}
    (h : decodeStr bytes = some (i, n)) : i.bytes <+: bytes ∧ n = i.bytes.length := by
  unfold decodeStr at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp [Str.bytes]

/-- The encoding of a form decodes to it, whatever bytes follow. -/
theorem decodeStr_bytes_append (i : Str) (more : List Byte) :
    decodeStr (i.bytes ++ more) = some (i, i.bytes.length) := by
  cases i <;> rfl

/-- **A decoded string form keeps its reading whatever bytes follow.** -/
theorem decodeStr_append {bytes : List Byte} {i : Str} {n : Nat}
    (h : decodeStr bytes = some (i, n)) (more : List Byte) :
    decodeStr (bytes ++ more) = some (i, n) := by
  obtain ⟨⟨rest, rfl⟩, rfl⟩ := decodeStr_some h
  rw [List.append_assoc]
  exact decodeStr_bytes_append i _

/-- The encodings of the forms are the keys of `table`. -/
theorem bytes_mem_table (i : Str) : i.bytes ∈ table := by
  cases i <;> simp [table]

/-- **Bytes that start with a key of a table disjoint from `Str9.table` are not a string
form.** -/
theorem decodeStr_none_of_key {u : List (List Byte)} (hd : TableDisjoint table u = true)
    {k : List Byte} (hk : k ∈ u) {bytes : List Byte} (hp : k <+: bytes) :
    decodeStr bytes = none := by
  cases h : decodeStr bytes with
  | none => rfl
  | some p =>
    obtain ⟨i, n⟩ := p
    obtain ⟨hi, -⟩ := decodeStr_some h
    unfold TableDisjoint at hd
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hd
    obtain ⟨h1, h2⟩ := hd _ (bytes_mem_table i) k hk
    rcases Nat.le_total i.bytes.length k.length with hl | hl
    · have := List.isPrefixOf_iff_prefix.mpr (List.prefix_of_prefix_length_le hi hp hl)
      simp [h1] at this
    · have := List.isPrefixOf_iff_prefix.mpr (List.prefix_of_prefix_length_le hp hi hl)
      simp [h2] at this

/-- `Ext9`'s new-form decoder rejects every extension of a slice its parser rejects. -/
theorem decodeNew_none_of_bad {w : List Byte} (h : ext9Bad w = true) (more : List Byte) :
    Ext9.decodeNew (w ++ more) = none := by
  unfold ext9Bad at h
  split at h
  · rename_i hb
    unfold Ext9.decodeNew
    rw [Ext9.good_pNew.bad hb more]
  · cases h

/-- What a listed string form is. -/
theorem decodeL_spec {bytes : List Byte} {i : Str} {n : Nat} (h : decodeL bytes = some (i, n)) :
    Silmaril.X86.Ext.decode bytes = none ∧ Open9.newBad bytes = true ∧
      Open9.rawNotEof bytes = true ∧ ext9Bad bytes = true ∧ decodeStr bytes = some (i, n) ∧
      n ≤ maxInstrLength := by
  unfold decodeL at h
  split at h
  · rename_i i' n' hd
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hd, hc.2.2.2.2⟩
    · cases h
  · cases h

end Silmaril.Proofs.Machine.X86.Str9

module

public import Silmaril.X86.Str9.Defs
public import Silmaril.X86.Ext9.Thms

/-!
# `Str9`: decoder laws

* `decodeStr_some`, `decodeStr_bytes_append`, `decodeStr_append`: a decoded form is its own
  encoding, a prefix of the bytes, and keeps its reading whatever bytes follow.
* `decodeNew_none_of_bad`: `Ext9` rejects every extension of a slice its parser rejects.
* `decodeL_spec`: what a listed string form is.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Str9

open Silmaril.X86 (Byte maxInstrLength)
open Silmaril.X86.Str9

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

/-- A decoded string form keeps its reading whatever bytes follow. -/
theorem decodeStr_append {bytes : List Byte} {i : Str} {n : Nat}
    (h : decodeStr bytes = some (i, n)) (more : List Byte) :
    decodeStr (bytes ++ more) = some (i, n) := by
  obtain ⟨⟨rest, rfl⟩, rfl⟩ := decodeStr_some h
  rw [List.append_assoc]
  exact decodeStr_bytes_append i _

/-- `Ext9`'s new-form decoder rejects every extension of a slice its parser rejects. -/
theorem decodeNew_none_of_bad {w : List Byte} (h : ext9Bad w = true) (more : List Byte) :
    Silmaril.X86.Ext9.decodeNew (w ++ more) = none := by
  unfold ext9Bad at h
  split at h
  · rename_i hb
    unfold Silmaril.X86.Ext9.decodeNew
    rw [Silmaril.X86.Ext9.good_pNew.bad hb more]
  · cases h

/-- What a listed string form is. -/
theorem decodeL_spec {bytes : List Byte} {i : Str} {n : Nat} (h : decodeL bytes = some (i, n)) :
    Silmaril.X86.Ext.decode bytes = none ∧ Silmaril.X86.Open9.newBad bytes = true ∧
      Silmaril.X86.Open9.rawNotEof bytes = true ∧ ext9Bad bytes = true ∧
      decodeStr bytes = some (i, n) ∧ n ≤ maxInstrLength := by
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

end Silmaril.Proofs.X86.Str9

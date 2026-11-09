module

public import Silmaril.X86.Ext9.Defs

/-!
# `Ext9` decoder laws

`good_pNew`: the parser of the new forms has the prefix laws of `Ext.ByteParser.Good`, so a
decoded form keeps its reading whatever bytes follow (`decodeNew_append`) and a rejection
stays a rejection (`pNew_bad_append`). `decode_of_ext8` and `decode_ext8_iff`: the variant's
decoder agrees with `Ext8.decode` wherever that decodes.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ext9

open Silmaril.X86 (Byte)
open Silmaril.X86.Ext (PResult ByteParser)
open Silmaril.X86.Ext.ByteParser
open Silmaril.X86.Ext9

theorem good_pIb32 : Good pIb32 := good_map _ good_byte

theorem good_pIb16 : Good pIb16 := good_map _ good_byte

/-- Discharge `Good` goals of parsers built from the combinators. -/
macro "good_tac" : tactic => `(tactic| repeat (first
  | exact good_fail | exact good_byte | exact Silmaril.X86.Ext8.good_pM
  | exact Silmaril.X86.Ext.good_pImm32 | exact Silmaril.X86.Ext.good_pImm16
  | exact good_pIb32 | exact good_pIb16 | exact good_pure _
  | exact Silmaril.X86.Ext.good_pHead | exact good_pNotrack
  | exact Silmaril.X86.Ext8.good_optP _
  | apply good_ite | apply good_map | apply good_bind | intro _))

theorem good_pNotrack : Good pNotrack := by
  unfold pNotrack
  refine good_bind Silmaril.X86.Ext.good_pHead fun _ => good_ite ?_ good_fail
  exact good_bind Silmaril.X86.Ext8.good_pM fun _ => good_ite (good_pure _) good_fail

theorem good_pBody (rex : Option Silmaril.X86.Ext.Rex) (opc : Silmaril.X86.Ext.Opc) :
    Good (pBody rex opc) := by
  cases opc <;> simp only [pBody] <;> good_tac

theorem good_pBody16 (rex : Option Silmaril.X86.Ext.Rex) (opc : Silmaril.X86.Ext.Opc) :
    Good (pBody16 rex opc) := by
  cases opc <;> simp only [pBody16] <;> good_tac

theorem good_pNew : Good pNew := by
  refine good_bind Silmaril.X86.Ext.good_pHead fun h => ?_
  refine good_ite good_fail ?_
  split
  · exact good_pBody _ _
  · exact good_ite good_fail (good_pBody16 _ _)
  · exact good_ite (good_pure _) good_fail
  · exact good_fail

/-- A decoded new form keeps its reading whatever bytes follow. -/
theorem decodeNew_append {bytes : List Byte} {i : New} {n : Nat}
    (h : decodeNew bytes = some (i, n)) (more : List Byte) :
    decodeNew (bytes ++ more) = some (i, n) := by
  unfold decodeNew at h ⊢
  split at h
  · rename_i j rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, ext⟩ := good_pNew.ok hp
    rw [ext more]
    simp only [List.length_append, Option.some.injEq, Prod.mk.injEq, true_and]
    omega
  · simp at h

/-- A decoded new form consumes at most its input. -/
theorem decodeNew_le {bytes : List Byte} {i : New} {n : Nat}
    (h : decodeNew bytes = some (i, n)) : n ≤ bytes.length := by
  unfold decodeNew at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  · simp at h

/-- **Decoder agreement**: wherever `Ext8` decodes, so does the variant, to the same
instruction and length. -/
theorem decode_of_ext8 {bytes : List Byte} {i : Silmaril.X86.Ext8.Instr} {n : Nat}
    (h : Silmaril.X86.Ext8.decode bytes = some (i, n)) : decode bytes = some (.ext8 i, n) := by
  simp [decode, h]

/-- The variant's decoder returns an `ext8` instruction exactly when `Ext8` decodes. -/
theorem decode_ext8_iff {bytes : List Byte} {i : Silmaril.X86.Ext8.Instr} {n : Nat} :
    decode bytes = some (.ext8 i, n) ↔ Silmaril.X86.Ext8.decode bytes = some (i, n) := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · rename_i i' n' he
      simp only [Option.some.injEq, Prod.mk.injEq, Instr.ext8.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact he
    · cases hd : decodeNew bytes with
      | none => simp [hd] at h
      | some r => simp [hd] at h
  · exact decode_of_ext8

/-- The variant's decoder returns a new form exactly when `Ext8` rejects and `decodeNew`
reads it. -/
theorem decode_new_iff {bytes : List Byte} {i : New} {n : Nat} :
    decode bytes = some (.new i, n) ↔
      Silmaril.X86.Ext8.decode bytes = none ∧ decodeNew bytes = some (i, n) := by
  unfold decode
  split
  · rename_i he; simp [he]
  · rename_i he
    cases hd : decodeNew bytes with
    | none => simp [he]
    | some r =>
      obtain ⟨j, k⟩ := r
      simp [he, and_comm]

end Silmaril.Proofs.X86.Ext9

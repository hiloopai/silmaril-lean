module

public import Silmaril.X86.Atomic9.Defs
public import Silmaril.X86.Ext9.Thms

/-!
# `Atomic9` decoder laws

Proofs for `Silmaril/X86/Atomic9/Thms.lean`.

* `good_pNew`: the parser of the atomic forms has the prefix laws of `Ext.ByteParser.Good`,
  so a decoded form keeps its reading whatever bytes follow (`decodeNew_append`).
* `decodeL_spec`: what a listed atomic form is.
* `ext9_decodeNew_none_of_bad`: `Ext9`'s new-form decoder rejects every extension of a slice
  its parser rejects.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Atomic9

open Silmaril.X86 (Byte maxInstrLength)
open Silmaril.X86.Ext (PResult ByteParser)
open Silmaril.X86.Ext.ByteParser
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Atomic9

theorem good_memP (rex : Option Silmaril.X86.Ext.Rex) (mp : Silmaril.X86.Ext.ModrmPart) :
    Good (memP rex mp) := by
  unfold memP
  split
  · exact good_pure _
  · exact good_fail

theorem good_rmP (l : Bool) (rex : Option Silmaril.X86.Ext.Rex)
    (mp : Silmaril.X86.Ext.ModrmPart) : Good (rmP l rex mp) := by
  unfold rmP
  exact good_ite (good_map _ (good_memP _ _)) (good_pure _)

theorem good_rm8P (l : Bool) (rex : Option Silmaril.X86.Ext.Rex)
    (mp : Silmaril.X86.Ext.ModrmPart) : Good (rm8P l rex mp) := by
  unfold rm8P
  refine good_ite ?_ (good_pure _)
  split
  · exact good_pure _
  · exact good_fail

theorem good_pIb32 : Good Ext9.pIb32 := good_map _ good_byte

/-- Discharge `Good` goals of parsers built from the combinators. -/
macro "good_tac" : tactic => `(tactic| repeat (first
  | exact good_fail | exact good_byte | exact Silmaril.X86.Ext8.good_pM
  | exact Silmaril.X86.Ext.good_pImm32 | exact good_pIb32 | exact good_pure _
  | exact Silmaril.X86.Ext8.good_optP _
  | exact good_memP _ _ | exact good_rmP _ _ _ | exact good_rm8P _ _ _
  | apply good_ite | apply good_map | apply good_bind | intro _))

theorem good_pBody (l : Bool) (rex : Option Silmaril.X86.Ext.Rex) (opc : Silmaril.X86.Ext.Opc) :
    Good (pBody l rex opc) := by
  cases opc <;> simp only [pBody] <;> good_tac

theorem good_pLocked : Good pLocked :=
  good_bind Silmaril.X86.Ext.good_pHead fun _ => good_ite (good_pBody _ _ _) good_fail

theorem good_pNew : Good pNew := by
  refine good_bind Silmaril.X86.Ext.good_pHead fun h => ?_
  refine good_ite good_fail ?_
  split
  · exact good_ite good_pLocked (good_pBody _ _ _)
  · exact good_ite (good_pure _) good_fail
  · exact good_fail

/-- A decoded atomic form keeps its reading whatever bytes follow. -/
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

/-- `Ext9`'s new-form decoder rejects every extension of a slice its parser rejects. -/
theorem ext9_decodeNew_none_of_bad {w : List Byte} (h : Sse9.ext9Bad w = true)
    (more : List Byte) : Ext9.decodeNew (w ++ more) = none := by
  unfold Sse9.ext9Bad at h
  split at h
  · rename_i hb
    unfold Ext9.decodeNew
    rw [Ext9.good_pNew.bad hb more]
  · cases h

/-- What a listed atomic form is. -/
theorem decodeL_spec {bytes : List Byte} {i : New} {n : Nat} (h : decodeL bytes = some (i, n)) :
    Silmaril.X86.Ext.decode bytes = none ∧ Open9.newBad bytes = true ∧
      Open9.rawNotEof bytes = true ∧ Sse9.ext9Bad bytes = true ∧ decodeNew bytes = some (i, n) ∧
      0 < n ∧ n ≤ maxInstrLength := by
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

/-- What the machine's listing decoder reads: an `Open9` listing, or (where `Open9.decode`
rejects) a listed atomic form. -/
theorem decode_cases {bytes : List Byte} {i : Instr} {n : Nat} (h : decode bytes = some (i, n)) :
    (∃ j, i = .open9 j ∧ Open9.decode bytes = some (j, n)) ∨
      (∃ j, i = .new j ∧ Open9.decode bytes = none ∧ decodeL bytes = some (j, n)) := by
  unfold decode at h
  split at h
  · rename_i j n' hd
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨j, rfl, hd⟩
  · rename_i hd
    cases hl : decodeL bytes with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨j, n'⟩ := p
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨j, rfl, hd, rfl⟩

end Silmaril.Proofs.X86.Atomic9

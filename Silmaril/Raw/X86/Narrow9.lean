module

public import Silmaril.X86.Narrow9.Defs
public import Silmaril.X86.Ext9.Thms

/-!
# `Narrow9`: the decoder laws

* `good_pNew`: the parser has the prefix laws of `Ext.ByteParser.Good`, so
  `decodeNew_append`: a decoded form keeps its reading whatever bytes follow, and
  `pNew_bad_append`: a rejection stays a rejection.
* `decodeNew_le`: a decoded form consumes at most its input.
-/

@[expose] public section

namespace Silmaril.X86.Narrow9

open Silmaril.X86 (Byte)
open Silmaril.X86.Ext (PResult ByteParser)
open Silmaril.X86.Ext.ByteParser

theorem good_pIb16' : Good Silmaril.X86.Ext9.pIb16 := good_map _ good_byte

/-- Discharge `Good` goals of the parsers built from the combinators. -/
macro "narrow_good_tac" : tactic => `(tactic| repeat (first
  | exact good_fail | exact good_byte | exact Silmaril.X86.Ext8.good_pM
  | exact Silmaril.X86.Ext.good_pImm16 | exact good_pIb16'
  | exact good_pure _ | exact Silmaril.X86.Ext8.good_optP _
  | apply good_ite | apply good_map | apply good_bind | intro _))

theorem good_pBody8 (rex : Option Silmaril.X86.Ext.Rex) (opc : Silmaril.X86.Ext.Opc) :
    Good (pBody8 rex opc) := by
  cases opc <;> simp only [pBody8] <;> narrow_good_tac

theorem good_pBody16 (rex : Option Silmaril.X86.Ext.Rex) (opc : Silmaril.X86.Ext.Opc) :
    Good (pBody16 rex opc) := by
  cases opc <;> simp only [pBody16] <;> narrow_good_tac

/-- **The parser has the prefix laws.** -/
theorem good_pNew : Good pNew := by
  refine good_bind Silmaril.X86.Ext.good_pHead fun h => good_ite good_fail ?_
  split
  · exact good_pBody8 _ _
  · exact good_pBody16 _ _
  · exact good_fail

/-- A rejection stays a rejection whatever bytes follow. -/
theorem pNew_bad_append {w : List Byte} (h : pNew w = .bad) (more : List Byte) :
    pNew (w ++ more) = .bad :=
  good_pNew.bad h more

/-- **A decoded form keeps its reading whatever bytes follow.** -/
theorem decodeNew_append {w : List Byte} {i : New} {n : Nat} (h : decodeNew w = some (i, n))
    (more : List Byte) : decodeNew (w ++ more) = some (i, n) := by
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

/-- A decoded form consumes at most its input. -/
theorem decodeNew_le {w : List Byte} {i : New} {n : Nat} (h : decodeNew w = some (i, n)) :
    n ≤ w.length := by
  unfold decodeNew at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  · simp at h

end Silmaril.X86.Narrow9

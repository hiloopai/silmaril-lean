module

public import Silmaril.Process.LPS.NativeX86All
public import Silmaril.Process.LPS.Lattice

/-! # The native x86-64 variants in the process lattice

Two variants of the complete native table exist:

* `exactTable`: the families' x86-64 arms as they are (the `TASK_SIZE_MAX` band answered by
  the families' whole-range `access_ok`, `sigaltstack` non-strict);
* `nativeTable`: the same arms with boundary, configuration and version chaos (`chaos`), the variant
  the statements use.

`nativeTable_restricts_exact` proves `Lattice.Restricts (dispatch nativeTable)
(dispatch exactTable)`: at every input the chaos variant is the exact one or only declines.
So, by `Lattice.obsTrace_mono` and `Lattice.obsTrace_eq_of_errorFree`, the chaos variant has
fewer traces, and an error-free result proved against it holds against the exact variant
with the same traces. The general form `tableWith_restricts` covers any arm transformer that
keeps numbers, names and statuses and only declines.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.NativeX86.All

open Silmaril.Process.LPS

theorem installArm_restricts (g : SpecArm → SpecArm) (hg : ∀ a, (g a).no = a.no)
    (hname : ∀ a, (g a).name = a.name)
    (hr : ∀ a i m, (∀ o, (g a).spec i m o ↔ a.spec i m o) ∨
      (∀ o, (g a).spec i m o ↔ o = .unmodeled))
    (overrides : List SpecArm) (s : SpecArm) (i : SyscallInput) (m : Model) :
    (∀ o, (installArm (overrides.map g) s).spec i m o ↔ (installArm overrides s).spec i m o) ∨
      (∀ o, (installArm (overrides.map g) s).spec i m o ↔ o = .unmodeled) := by
  unfold installArm
  rw [lookupArm_map g hg]
  cases h : lookupArm overrides s.no with
  | none => exact .inl fun _ => Iff.rfl
  | some native =>
    simp only [Option.map_some, hname]
    split
    · exact hr native i m
    · exact .inl fun _ => Iff.rfl

theorem tableWith_restricts (g : SpecArm → SpecArm) (hg : ∀ a, (g a).no = a.no)
    (hname : ∀ a, (g a).name = a.name)
    (hr : ∀ a i m, (∀ o, (g a).spec i m o ↔ a.spec i m o) ∨
      (∀ o, (g a).spec i m o ↔ o = .unmodeled)) :
    Restricts (dispatch (tableWith g)) (dispatch exactTable) := by
  intro i m
  unfold dispatch exactTable tableWith
  rw [lookupArm_append, lookupArm_append, lookupArm_map g hg, lookupArm_tableWithFamilies,
    lookupArm_tableWithFamilies, List.map_id]
  simp only [List.map_id_fun, id_eq]
  cases he : lookupArm extensionArms i.sysno.toNat with
  | some e => exact hr e i m
  | none =>
    simp only [Option.map_none, Option.none_or]
    cases hs : lookupArm (table specTable) i.sysno.toNat with
    | none => exact .inl fun _ => Iff.rfl
    | some s => exact installArm_restricts g hg hname hr familyReferenceArms s i m

/-- The chaos variant restricts the exact one (`Lattice.Restricts`). -/
theorem nativeTable_restricts_exact : Restricts (dispatch nativeTable) (dispatch exactTable) :=
  tableWith_restricts chaos chaos_no chaos_name chaos_restricts

end Silmaril.Process.LPS.NativeX86.All

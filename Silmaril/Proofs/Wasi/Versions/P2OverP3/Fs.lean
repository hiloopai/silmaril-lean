module

public import Silmaril.Wasi.Versions.P2OverP3.Comp.Defs

/-!
# Proofs: the exports are not filesystem functions

`fsOk_of_mem`: the base WASI theory's filesystem typing does not constrain the answers of the exports.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions.P2

/-! ## The exports are not filesystem functions -/

theorem not_fs_of_mem {f : FnName} (hf : f ∈ exp2) :
    f ≠ getDirs ∧ f ≠ openAt ∧ f ≠ fdWrite ∧ f ≠ fdRead ∧ f ≠ fdDrop := by
  rw [exp2, ioImports_eq, cliImports_eq, clockImports_eq] at hf
  rcases hf with ((h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h) | (h | h | h | h | h | h | h | h | h | h)) | (h | h | h | h | h | h) <;> subst h <;>
    decide

theorem fsOk_of_mem {f : FnName} (hf : f ∈ exp2) (a : List Val) (r : Option (List Val)) :
    fsOk (.imp f a r) = true := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := not_fs_of_mem hf
  unfold fsOk
  dsimp only
  rw [ite_eq_right n1, ite_eq_right n2, ite_eq_right n3, ite_eq_right n4, ite_eq_right n5]

end Silmaril.Wasi.Versions.P2OverP3

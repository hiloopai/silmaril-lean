module

public import Silmaril.Net.Http.OpenApiPetstore.Defs

/-! Proofs for `Silmaril.Net.Http.OpenApiPetstore.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Http.Proofs.OpenApiPetstore

open Silmaril.Net.Http Silmaril.Net.Http.OpenApi Silmaril.Net.Http.OpenApi.Petstore

theorem handlers_conform :
    ∀ p ∈ doc.paths, ∀ op ∈ p.operations, ∀ vs r, ResponseConforms op (handlers op vs r) ∧
      Documented op (handlers op vs r).status := by
  intro p hp op hop vs r
  simp only [doc, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop <;>
  rcases hop with rfl | rfl <;>
  simp only [handlers, listPets, createPet, myPets, showPetById] <;>
  simp only [String.reduceEq, ↓reduceIte] <;>
  (try split_ifs) <;> decide

end Silmaril.Net.Http.Proofs.OpenApiPetstore

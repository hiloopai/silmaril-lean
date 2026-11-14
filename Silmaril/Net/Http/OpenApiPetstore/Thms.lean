module

public import Silmaril.Net.Http.OpenApiPetstore.Defs
public import Silmaril.Net.Http.OpenApi.Thms
import Silmaril.Proofs.Net.Http.OpenApiPetstore

/-!
# The pet store: laws

* `doc_valid`: the document is well formed (version, methods, responses, declared path
  parameters).
* `service_conforms`, `service_closed`: the service conforms to the document and answers every
  routed request with a documented status.
* `route_mine`, `route_pet`: `/pets/mine` goes to `myPets` (concrete before templated) and
  `/pets/7` to `showPetById` with `petId = 7`.
-/

@[expose] public section

namespace Silmaril.Net.Http.OpenApi.Petstore

open Silmaril.Net.Http

theorem doc_valid : doc.Valid := by decide

theorem handlers_conform :
    ∀ p ∈ doc.paths, ∀ op ∈ p.operations, ∀ vs r, ResponseConforms op (handlers op vs r) ∧
      Documented op (handlers op vs r).status :=
  Proofs.OpenApiPetstore.handlers_conform

theorem service_conforms : Conforms doc service :=
  ofHandlers_conforms fun p hp op hop vs r => (handlers_conform p hp op hop vs r).1

theorem service_closed : Closed doc service :=
  ofHandlers_closed fun p hp op hop vs r => (handlers_conform p hp op hop vs r).2

/-- A `GET` request for a path. -/
def getReq (path : String) : Request := ⟨⟨.get, ⟨some .http, some (ascii "a"), some (ascii path)⟩⟩, [], [], []⟩

theorem route_mine : (route doc (getReq "/pets/mine")).map (·.1.operationId) = some "myPets" := by
  decide

theorem route_pet : (route doc (getReq "/pets/7")).map (fun r => (r.1.operationId, r.2.2)) =
    some ("showPetById", [ascii "7"]) := by
  decide

end Silmaril.Net.Http.OpenApi.Petstore

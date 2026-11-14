module

public import Silmaril.Net.Http1.Service.Defs
public import Silmaril.Net.Http1.Institution.Thms
public import Silmaril.Net.Http.OpenApiPetstore.Defs
import Silmaril.Proofs.Net.Http1.Service
import Silmaril.Net.Http.OpenApiPetstore.Thms

/-!
# REST services over HTTP/1.1: laws

Proofs in `Silmaril/Proofs/Net/Http1/Service.lean`.

* `serviceHandler_wellFramed`: a service with valid responses gives a well-framed handler. The
  server frames content by `Content-Length` (computed by `decDigits`, read back by
  `contentLength?`), and the service's own framing and hop-by-hop fields are dropped.
* `serviceModel_vanilla`: so the service behind the reference server is a **vanilla HTTP/1.1
  implementation** (its reduct to the standard vocabulary satisfies `rfcCore`).
* `closed_satisfies_theory`: a service **closed** for a valid OpenAPI document satisfies the
  document's theory `toTheory d` in the HTTP/1.1 institution. The OpenAPI semantics (routing
  with concrete paths first, path templates, documented statuses) and the HTTP/1.1 request
  checks agree.
* `serviceModel_extensionCompliant`: together, the service is **extension-compliant** for its
  document's theory over `ApiSig` (`PATCH` as the extension method).
* `petstore_extensionCompliant`: the pet store service of `Silmaril.Net.Http.OpenApiPetstore`
  is an instance.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Net.Http1.Inst

theorem serviceHandler_wellFramed {S : Http.OpenApi.Service} (hS : ServiceValid S) :
    Handler.WellFramed (serviceHandler S) :=
  Proofs.Service.serviceHandler_wellFramed hS

namespace Inst

theorem serviceModel_reduct (S : Http.OpenApi.Service) :
    (serviceModel S).reduct (Std.incl Unit Empty Empty) = refModel {} (serviceHandler S) := rfl

theorem serviceModel_vanilla {S : Http.OpenApi.Service} (hS : ServiceValid S) :
    Vanilla ((serviceModel S).reduct (Std.incl Unit Empty Empty)) := by
  rw [serviceModel_reduct]
  exact refModel_vanilla (by decide) (serviceHandler_wellFramed hS)

theorem closed_satisfies_theory {d : Http.OpenApi.Document} {S : Http.OpenApi.Service}
    (hd : d.Valid) (hc : Http.OpenApi.Closed d S) : SatAll (serviceModel S) (toTheory d) :=
  Proofs.Service.closed_satisfies_theory hd hc

theorem serviceModel_extensionCompliant {d : Http.OpenApi.Document} {S : Http.OpenApi.Service}
    (hd : d.Valid) (hc : Http.OpenApi.Closed d S) (hS : ServiceValid S) :
    ExtensionCompliant (toTheory d) (serviceModel S) := by
  refine ⟨(serviceModel_vanilla hS).1, fun φ hφ => ?_, closed_satisfies_theory hd hc⟩
  obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hφ
  exact (sat_map_iff _ _ _).2 ((serviceModel_vanilla hS).2 ψ hψ)

theorem petstore_extensionCompliant :
    ExtensionCompliant (toTheory Http.OpenApi.Petstore.doc)
      (serviceModel Http.OpenApi.Petstore.service) :=
  serviceModel_extensionCompliant Http.OpenApi.Petstore.doc_valid
    Http.OpenApi.Petstore.service_closed Proofs.Service.petstore_valid

theorem petstore_theory_length : (toTheory Http.OpenApi.Petstore.doc).length = 4 := by decide

end Inst

end Silmaril.Net.Http1

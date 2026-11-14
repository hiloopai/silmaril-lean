module

public import Silmaril.Servers.OpenApi.Defs
public import Silmaril.Servers.Core.Thms
public import Silmaril.Net.Http.OpenApiPetstore.Thms
public import Silmaril.Net.Http1.Service.Thms
public import Silmaril.Servers.Http1Bridge.Thms
import Silmaril.Proofs.Servers.OpenApi.Basic

/-!
# The OpenAPI institution: theorems

* **The satisfaction condition** (`sat_map_iff`): a model satisfies a translated obligation iff
  its reduct satisfies the obligation. Sentence translation is functorial (`Sen.map_id`,
  `Sen.map_comp`), so `inst` is an institution (`classic`).
* **Refinement**: a server refining another satisfies its positive obligations
  (`sat_of_refines`, for sentences without negation, `Sen.Pos`).
* **Agreement with the OpenAPI service model**: for a service (a function), the response
  obligations of all the document's operations hold iff the service conforms
  (`respOk_all_iff_conforms`), and the closed-world obligations iff it is closed
  (`closed_all_iff`).
* **Down to HTTP/1.1 octets**: a service closed for a valid document, behind the HTTP/1.1
  reference server, satisfies each status obligation of the document's HTTP/1.1 theory as a
  trace sentence of its wire-level server (`closed_wire_sat`, through
  `Silmaril.Net.Http1.Service` and `Silmaril.Servers.Http1Bridge`).
* **Example**: the Petstore service meets every response and closed-world obligation of its
  document (`petstore_respOk`, `petstore_closed`).
-/

@[expose] public section

namespace Silmaril.Servers.OpenApiInst

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Net.Http (Request Response)
open Silmaril.Net.Http.OpenApi

/-- **The satisfaction condition.** -/
theorem sat_map_iff {A B : Sig} (σ : A ⟶ B) (M : Model B) (φ : Sen A) :
    Sat M (φ.map σ) ↔ Sat (M.reduct σ) φ :=
  Proofs.Servers.OpenApiInst.sat_map_iff σ M φ

theorem Sen.map_id {A : Sig} (φ : Sen A) : φ.map (𝟙 A) = φ :=
  Proofs.Servers.OpenApiInst.map_id φ

theorem Sen.map_comp {A B C : Sig} (σ : A ⟶ B) (τ : B ⟶ C) (φ : Sen A) :
    φ.map (σ ≫ τ) = (φ.map σ).map τ :=
  Proofs.Servers.OpenApiInst.map_comp σ τ φ

/-- The room of a signature: obligations, models (discrete), satisfaction. -/
def room (A : Sig) : Room.{0, 0, 0} :=
  ⟨Sen A, Cat.of (Discrete (Model A)), fun M φ => Sat (Discrete.as M) φ⟩

/-- The corridor of a signature morphism. -/
def corridor {A B : Sig} (σ : A ⟶ B) : room A ⟶ room B :=
  ⟨Sen.map σ, Discrete.functor fun (M : Model B) => Discrete.mk (M.reduct σ),
    fun M φ => sat_map_iff σ (Discrete.as M) φ⟩

/-- **The OpenAPI institution of servers**, as a functor into rooms. -/
def inst : Sig ⥤ Room.{0, 0, 0} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext fun φ => Sen.map_id φ)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))
  map_comp σ τ := Room.hom_ext (funext fun φ => Sen.map_comp σ τ φ)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))

/-- The institution in the direct form. -/
def classic : ClassicInstitution.{1, 0, 0, 0, 0} Sig := ClassicInstitution.ofRoomFunctor inst

/-- **A refining server satisfies the positive obligations of the server it refines.** -/
theorem sat_of_refines {A : Sig} {M : Model A} {N : Servers.Model Http.sig}
    (h : N.Refines M.server) (φ : Sen A) (hp : φ.Pos) (hM : Sat M φ) :
    Sat { M with server := N } φ :=
  Proofs.Servers.OpenApiInst.sat_of_refines h φ hp hM

/-- **The response obligations of a document's operations hold iff the service conforms.** -/
theorem respOk_all_iff_conforms (d : Document) (S : Service) :
    (∀ o : DocOp d, Sat (docModel d S) (.respOk o)) ↔ Conforms d S :=
  Proofs.Servers.OpenApiInst.conforms_iff d S

/-- **The closed-world obligations hold iff the service is closed.** -/
theorem closed_all_iff (d : Document) (S : Service) :
    (∀ o : DocOp d, Sat (docModel d S) (.closed o)) ↔ Closed d S :=
  Proofs.Servers.OpenApiInst.closed_iff d S

/-- **Down to octets**: behind the HTTP/1.1 reference server, a service closed for a valid
document meets each status obligation of the document's HTTP/1.1 theory as a trace sentence of
its wire-level server. -/
theorem closed_wire_sat {d : Document} {S : Service} (hd : d.Valid) (hc : Closed d S)
    {φ : Silmaril.Net.Http1.Inst.Sen Silmaril.Net.Http1.Inst.ApiSig}
    (hφ : φ ∈ Silmaril.Net.Http1.Inst.toTheory d) {R} (hR : Http1Bridge.respRel
      (Silmaril.Net.Http1.Inst.serviceModel S) φ = some R) :
    (Http1Bridge.implServer (Silmaril.Net.Http1.Inst.serviceModel S).impl).Sat
      (Servers.Sen.atomic (A := Http1Bridge.wireSig) R) :=
  (Http1Bridge.sat_iff_server_sat _ hR).1
    (Silmaril.Net.Http1.Inst.closed_satisfies_theory hd hc φ hφ)

theorem petstore_respOk (o : DocOp Petstore.doc) : Sat (docModel Petstore.doc Petstore.service) (.respOk o) :=
  (respOk_all_iff_conforms _ _).2 Petstore.service_conforms o

theorem petstore_closed (o : DocOp Petstore.doc) : Sat (docModel Petstore.doc Petstore.service) (.closed o) :=
  (closed_all_iff _ _).2 Petstore.service_closed o

end Silmaril.Servers.OpenApiInst

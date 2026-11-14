module

public import Silmaril.Net.Http.OpenApi.Defs
import Silmaril.Proofs.Net.Http.OpenApi

/-!
# A REST service model (OpenAPI 3.1 subset): laws

Proofs in `Silmaril/Proofs/Net/Http/OpenApi.lean`.

* **Path templates**: `matchTemplate_sound` (a match renders back to the path),
  `matchTemplate_render` (rendering nonempty values matches back to them),
  `matchTemplate_length` (one value per expression).
* **Routing**: `route_mem`, `route_sound`: a routed request addresses an operation of a path
  of the document with its own method, and its path is the template rendered with the values.
* **Services**: `ofHandlers_conforms`, `ofHandlers_closed`: a service built from per-operation
  handlers conforms to (is closed for) the document when each operation's handler does.
-/

@[expose] public section

namespace Silmaril.Net.Http.OpenApi

theorem matchTemplate_sound {t : PathTemplate} {ss vs : List Bytes}
    (h : matchTemplate t ss = some vs) : render t vs = ss :=
  Proofs.OpenApi.matchTemplate_sound t ss vs h

theorem matchTemplate_length {t : PathTemplate} {ss vs : List Bytes}
    (h : matchTemplate t ss = some vs) : vs.length = t.params.length :=
  Proofs.OpenApi.matchTemplate_length t ss vs h

theorem matchTemplate_render {t : PathTemplate} {vs : List Bytes}
    (hl : vs.length = t.params.length) (hv : ∀ v ∈ vs, v ≠ []) :
    matchTemplate t (render t vs) = some vs :=
  Proofs.OpenApi.matchTemplate_render t vs hl hv

theorem routePath_mem {d : Document} {path : Bytes} {p : PathItem} {vs : List Bytes}
    (h : routePath d path = some (p, vs)) :
    p ∈ d.paths ∧ matchTemplate p.template (segments path) = some vs :=
  Proofs.OpenApi.routePath_mem h

theorem route_mem {d : Document} {r : Request} {op : Operation} {p : PathItem} {vs : List Bytes}
    (h : route d r = some (op, p, vs)) :
    p ∈ d.paths ∧ op ∈ p.operations ∧ op.method = r.method ∧
      matchTemplate p.template (segments (pathPart (targetPq r.target))) = some vs :=
  Proofs.OpenApi.route_mem h

theorem route_sound {d : Document} {r : Request} {op : Operation} {p : PathItem} {vs : List Bytes}
    (h : route d r = some (op, p, vs)) :
    render p.template vs = segments (pathPart (targetPq r.target)) :=
  matchTemplate_sound (route_mem h).2.2.2

theorem ofHandlers_conforms {d : Document} {H : Operation → List Bytes → Request → Response}
    (hH : ∀ p ∈ d.paths, ∀ op ∈ p.operations, ∀ vs r, ResponseConforms op (H op vs r)) :
    Conforms d (Service.ofHandlers d H) := by
  intro r op p vs hr _
  have hm := route_mem hr
  simp only [Service.ofHandlers, hr]
  exact hH p hm.1 op hm.2.1 vs r

theorem ofHandlers_closed {d : Document} {H : Operation → List Bytes → Request → Response}
    (hH : ∀ p ∈ d.paths, ∀ op ∈ p.operations, ∀ vs r, Documented op (H op vs r).status) :
    Closed d (Service.ofHandlers d H) := by
  intro r op p vs hr
  have hm := route_mem hr
  simp only [Service.ofHandlers, hr]
  exact hH p hm.1 op hm.2.1 vs r

end Silmaril.Net.Http.OpenApi

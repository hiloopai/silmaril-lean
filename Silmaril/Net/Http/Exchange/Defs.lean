module

public import Silmaril.Net.Http.Message.Defs

@[expose] public section

/-!
# HTTP exchanges and origin semantics (RFC 9110 §3, §9, §15)

An HTTP exchange is a request and the responses to it: zero or more interim (1xx) responses
then one final response (§15.2, `Exchange`). An **origin server** (§3.6, §7.4) is modelled as a
relation `Origin σ` between a resource state `σ`, a request, a response and the next state:
nondeterministic and stateful, so that the method properties of §9.2 become properties of the
origin:

* `Origin.RespectsSafe`: a safe method (§9.2.1) does not change the resource state ("the client
  does not request, and does not expect, any state change on the origin server");
* `Origin.RespectsIdempotent`: repeating an idempotent request (§9.2.2) leaves the state of the
  first ("the intended effect on the server of multiple identical requests with that method is
  the same as the effect for a single such request");
* `Origin.HeadLikeGet`: `HEAD` answers as `GET` without content (§9.3.2, "identical to GET
  except that the server MUST NOT send content in the response");
* `Origin.ValidResponses`: every response is valid (`Response.isValid`).

Instances:

* `Origin.ofFun`: a deterministic origin of a step function;
* `Origin.ofTargets W`: a stateless origin of a web `W : Target → Response` that answers
  every method from the target, with `HEAD` stripped (the shape of the WASI webs of
  `Silmaril.Wasi.Versions.Net` and `HttpBody`, which answer an authority and path-with-query);
* `storeStep`: a resource store (`Store`: a representation per target), with `GET`, `HEAD`,
  `PUT`, `DELETE` and `OPTIONS` per §9.3.1, §9.3.2, §9.3.4, §9.3.5, §9.3.7; other known
  methods are answered 405 (§15.5.6) and unrecognized ones 501 (§9.1).

The theorems (`Exchange/Thms.lean`) prove that the instances have the properties.

Not modelled yet: conditional requests (§13), range requests (§14), content negotiation
(§12), redirects and their client semantics (§15.4), authentication (§11), intermediaries
(§3.7) and caching (RFC 9111).
-/

namespace Silmaril.Net.Http

open Silmaril.Net.Http.Field

/-! ## Exchanges -/

/-- An exchange: a request, interim responses and the final response (§15.2). -/
structure Exchange where
  request : Request
  interim : List Response
  final : Response

/-- The interim responses are informational and the final response is final (§15.2). -/
def Exchange.isWellFormed (e : Exchange) : Bool :=
  e.interim.all (fun r => !Status.isFinal r.status && Status.isValid r.status) &&
    Status.isFinal e.final.status && Status.isValid e.final.status

/-! ## Origins -/

/-- An origin server: in resource state `s`, the request `r` may be answered `resp` with next
state `s'`. -/
def Origin (σ : Type) : Type := σ → Request → Response → σ → Prop

namespace Origin

variable {σ : Type}

/-- Safe methods do not change the resource state (§9.2.1). -/
def RespectsSafe (O : Origin σ) : Prop :=
  ∀ s r resp s', r.method.isSafe = true → O s r resp s' → s' = s

/-- Repeating an idempotent request keeps the state of the first (§9.2.2). -/
def RespectsIdempotent (O : Origin σ) : Prop :=
  ∀ s r resp₁ s₁ resp₂ s₂, r.method.isIdempotent = true →
    O s r resp₁ s₁ → O s₁ r resp₂ s₂ → s₂ = s₁

/-- The request with another method. -/
def _root_.Silmaril.Net.Http.Request.withMethod (r : Request) (m : Method) : Request :=
  { r with control := { r.control with method := m } }

/-- `HEAD` answers as `GET` without content (§9.3.2). -/
def HeadLikeGet (O : Origin σ) : Prop :=
  ∀ s r resp s', r.method = .head →
    (O s r resp s' ↔ ∃ g, O s (r.withMethod .get) g s' ∧ resp = g.stripContent)

/-- Every response is valid. -/
def ValidResponses (O : Origin σ) : Prop :=
  ∀ s r resp s', O s r resp s' → resp.isValid = true

/-- The origin of a step function. -/
def ofFun (f : σ → Request → Response × σ) : Origin σ :=
  fun s r resp s' => f s r = (resp, s')

/-- A web: the response for each target. -/
abbrev Web : Type := Target → Response

/-- The answer of a web to a request: `HEAD` without content (§9.3.2). -/
def webAnswer (W : Web) (r : Request) : Response :=
  if r.method = .head then (W r.target).stripContent else W r.target

/-- The stateless origin of a web. -/
def ofTargets (W : Web) : Origin Unit := ofFun (fun _ r => (webAnswer W r, ()))

end Origin

/-! ## A resource store -/

/-- A resource store: the current representation of each target (§3.2, §8). -/
abbrev Store : Type := Target → Option (List UInt8)

/-- The store with the target `t` set to `v`. -/
def Store.update (S : Store) (t : Target) (v : Option (List UInt8)) : Store :=
  fun t' => if t' = t then v else S t'

/-- `Allow: GET, HEAD, PUT, DELETE, OPTIONS` (§10.2.1). -/
def allowLine : Line :=
  ⟨Method.ascii "Allow", Method.ascii "GET, HEAD, PUT, DELETE, OPTIONS"⟩

/-- The `GET` answer of a store (§9.3.1): the representation, or 404 (§15.5.5). -/
def Store.get (S : Store) (t : Target) : Response :=
  match S t with
  | some c => Response.simple Status.ok c
  | none => Response.simple Status.notFound []

/-- One step of the store origin. -/
def storeStep (S : Store) (r : Request) : Response × Store :=
  match r.method with
  | .get => (S.get r.target, S)
  | .head => ((S.get r.target).stripContent, S)
  | .put =>
    -- §9.3.4: "201 (Created)" if created, "200 (OK) or a 204 (No Content)" if modified
    (Response.simple (if (S r.target).isSome then Status.noContent else Status.created) [],
      S.update r.target (some r.content))
  | .delete =>
    -- §9.3.5: 204 when the action has been enacted
    match S r.target with
    | some _ => (Response.simple Status.noContent [], S.update r.target none)
    | none => (Response.simple Status.notFound [], S)
  | .options => (⟨Status.noContent, [allowLine], [], []⟩, S)
  | .post | .connect | .trace | .patch =>
    (⟨Status.methodNotAllowed, [allowLine], [], []⟩, S)
  | .other _ => (Response.simple Status.notImplemented [], S)

/-- The resource-store origin. -/
def storeOrigin : Origin Store := Origin.ofFun storeStep

end Silmaril.Net.Http

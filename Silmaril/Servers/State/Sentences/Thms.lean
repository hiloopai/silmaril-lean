module

public import Silmaril.Servers.State.Sentences.Defs
public import Silmaril.Servers.State.Traces.Thms
public import Silmaril.Servers.State.SharedFs.Thms
public import Silmaril.Servers.WasiFs.Thms
import Silmaril.Proofs.Servers.State.Sentences

/-!
# The state models' results as sentences of the server core: theorems

PROVED (standard axioms), namespace `Silmaril.Servers.State`. Every result is about the core
model `Server.model M` of a state server (`Silmaril.Servers.State.Traces`): its histories read
as core traces, one connection per request.

**The bridges.**

* `closed_model_refines`: the core model of a closed server refines the core's
  atomic-handler server of its handler (from `closed_model_tr_iff`);
* **`model_refines_server`**: a state server that refines a closed server `Server.closed A s₀`
  has a core model that refines `A`'s atomic-handler server, so it satisfies `A`'s
  linearizability sentence (`model_sat_lin`); this is how every refinement result below is
  read (`Abstraction.model_refines` gives the same from an abstraction);
* `model_sat_atomic`: a statement about the calls and returns of every history is the core
  atomic sentence of the model; `model_sat_distinct`: distinct answers are `Sen.distinct`.

**(a) Component state** (`Component`).

* `counter_model_refines`, `counter_model_sat_lin` (from `counter_linearizable`);
  `kv_model_refines`, **`kv_model_sat_origin`** (from `kv_linearizable`): the store satisfies
  the trace sentence of its origin, `Http.originSen kv S₀`;
* **`counter_model_distinct`**, `decimalCounter_model_distinct` (from `counter_distinct`,
  `decimalCounter_distinct`);
* **`perRequest_counter_model`**, `perRequest_kv_get_model` (from `perRequest_counter`,
  `perRequest_kv_get`): with a fresh instance per request, the counter is the function server
  of `f 0`, and every `GET` is answered from the initial store.

**(b) Files the server alone edits** (`OwnedFs`).

* **`fileStore_model_refines`**, `fileStore_model_sat_origin` (from `fileStore_refines`,
  `fileStore_linearizable`): the file-backed store refines the core server of the component
  store `kv` from `view enc fs₀`;
* `static_model_refines`, **`static_model_sat`** (from `static_refines`, `static_answer`): the
  static file server is the function server of `staticAnswer loc fs₀` (`Sen.ofFun`).

**(c) Shared files** (`SharedFs`).

* **`static_model_safe`**, `static_model_untouched`, `store_model_safe` (from `static_safe`,
  `static_untouched`, `store_safe`): atomic sentences whatever the environment does;
* `store_model_refines`, `store_model_sat_origin` (from `store_refines`,
  `store_linearizable`); **`store_model_refines_on`**, `store_model_sat_lin_on` (from
  `store_refines_on`, `store_linearizable_on`): linearizable on the keys nobody else touches.

**The `wasi:http` store over `wasi:filesystem`** (`WasiFs`).

* **`wasiStore_model_refines`**, `wasiStore_model_sat_lin` (from `wasiStore_refines`,
  `wasiStore_linearizable`); `wasiStoreSmall_model_refines` (from `wasiStoreSmall_refines`).

Not restated: the results about states rather than traces (`fileStore_frame`,
`wasiStore_frame`, `Abstraction.reach_inv`), and the run-level checks of `WasiFs`.
-/

@[expose] public section

namespace Silmaril.Servers.State

open Silmaril.Net.Http Silmaril.Cli

variable {σ Req Resp : Type}

/-! ## The bridges -/

theorem closed_model_refines (A : Atomic σ Req Resp) (s₀ : σ) :
    (Server.closed A s₀).model.Refines (A.machine.server s₀) :=
  fun t ht => ((closed_model_tr_iff A s₀ t).1 ht).1

/-- **A refinement of a closed server refines its core atomic-handler server.** -/
theorem model_refines_server {M : Server Req Resp} {A : Atomic σ Req Resp} {s₀ : σ}
    (h : M.Refines (Server.closed A s₀)) : M.model.Refines (A.machine.server s₀) :=
  Model.Refines.trans h.model (closed_model_refines A s₀)

theorem model_sat_lin {M : Server Req Resp} {A : Atomic σ Req Resp} {s₀ : σ}
    (h : M.Refines (Server.closed A s₀)) : M.model.Sat (Sen.lin (A.machine.Hist s₀)) :=
  Model.sat_lin_of_refines_server (model_refines_server h)

theorem model_sat_atomic {M : Server Req Resp} {R : Req → Resp → Prop}
    (h : ∀ H, M.Hists H → ∀ i r s, Ev.call i r ∈ H → Ev.ret i s ∈ H → R r s) :
    M.model.Sat (Sen.atomic R) :=
  Proofs.Servers.State.Sentences.model_sat_atomic h

theorem model_sat_distinct {M : Server Req Resp}
    (h : ∀ H, M.Hists H → ∀ i j a b, Ev.ret i a ∈ H → Ev.ret j b ∈ H → i ≠ j → a ≠ b) :
    M.model.Sat Sen.distinct :=
  Proofs.Servers.State.Sentences.model_sat_distinct h

/-! ## (a) Component state -/

namespace Component

theorem counter_model_refines (f : Nat → Resp) :
    (counterServer (Req := Req) f).model.Refines ((counterBy f).machine.server 0) :=
  closed_model_refines _ _

theorem counter_model_sat_lin (f : Nat → Resp) :
    (counterServer (Req := Req) f).model.Sat (Sen.lin ((counterBy f).machine.Hist 0)) :=
  Model.sat_lin_of_refines_server (counter_model_refines f)

theorem kv_model_refines (S₀ : Store) : (kvServer S₀).model.Refines (kv.machine.server S₀) :=
  closed_model_refines _ _

/-- The component store satisfies the trace sentence of its origin. -/
theorem kv_model_sat_origin (S₀ : Store) : (kvServer S₀).model.Sat (Http.originSen kv S₀) :=
  Model.sat_lin_of_refines_server (kv_model_refines S₀)

/-- **Different requests to a counter with an injective rendering get different answers.** -/
theorem counter_model_distinct {f : Nat → Resp} (hf : Function.Injective f) :
    (counterServer (Req := Req) f).model.Sat Sen.distinct :=
  model_sat_distinct fun _ hH _ _ _ _ hi hj hij => counter_distinct hf hH hi hj hij

theorem decimalCounter_model_distinct :
    (Server.closed (httpCounter decimal) 0).model.Sat Sen.distinct :=
  model_sat_distinct fun _ hH _ _ _ _ hi hj hij => decimalCounter_distinct hH hi hj hij

/-- **With a fresh instance per request, the counter is the function server of `f 0`.** -/
theorem perRequest_counter_model (f : Nat → Resp) :
    (Server.perRequest (counterBy (Req := Req) f) 0).model.Sat (Sen.ofFun fun _ => f 0) :=
  model_sat_atomic fun _ hH _ _ _ hc hr => perRequest_counter hH hc hr

theorem perRequest_kv_get_model (S₀ : Store) :
    (Server.perRequest kv S₀).model.Sat
      (Sen.atomic fun r s => r.method = .get → s = S₀.get r.target) :=
  model_sat_atomic fun _ hH _ _ _ hc hr hm => perRequest_kv_get hH hc hr hm

end Component

/-! ## (b) Files the server alone edits -/

namespace OwnedFs

open Component

theorem fileStore_model_refines {enc : Target → FPath} (hinj : Function.Injective enc)
    (fs₀ : Fs) : (fileStore enc fs₀).model.Refines (kv.machine.server (view enc fs₀)) :=
  model_refines_server (fileStore_refines hinj fs₀)

theorem fileStore_model_sat_origin {enc : Target → FPath} (hinj : Function.Injective enc)
    (fs₀ : Fs) : (fileStore enc fs₀).model.Sat (Http.originSen kv (view enc fs₀)) :=
  model_sat_lin (fileStore_refines hinj fs₀)

theorem static_model_refines (loc : Target → Option FPath) (fs₀ : Fs) :
    (staticServer loc fs₀).model.Refines ((staticSpec loc fs₀).machine.server ()) :=
  model_refines_server (static_refines loc fs₀)

/-- **The static file server is the function server of `staticAnswer loc fs₀`.** -/
theorem static_model_sat (loc : Target → Option FPath) (fs₀ : Fs) :
    (staticServer loc fs₀).model.Sat (Sen.ofFun (A := Http.sig) (staticAnswer loc fs₀)) :=
  model_sat_atomic fun _ hH _ _ _ hc hr => static_answer hH hc hr

end OwnedFs

/-! ## (c) Shared files -/

namespace SharedFs

open OwnedFs Component

/-- **Safety over shared files**: each answer is the static answer of some files satisfying
the environment's invariant. -/
theorem static_model_safe (loc : Target → Option FPath) {fs₀ : Fs} {E : Fs → Fs → Prop}
    {I : Fs → Prop} (h₀ : I fs₀) (hE : Keeps E I) :
    (sharedStatic loc fs₀ E).model.Sat
      (Sen.atomic (A := Http.sig) fun r s => ∃ fs, I fs ∧ s = staticAnswer loc fs r) :=
  model_sat_atomic fun _ hH _ _ _ hc hr => static_safe h₀ hE hH hc hr

theorem static_model_untouched (loc : Target → Option FPath) (fs₀ : Fs) {E : Fs → Fs → Prop}
    {P : FPath → Prop} (hE : Untouched E P) :
    (sharedStatic loc fs₀ E).model.Sat (Sen.atomic (A := Http.sig) fun r s =>
      (∀ p, loc r.target = some p → P p) → s = staticAnswer loc fs₀ r) :=
  model_sat_atomic fun _ hH _ _ _ hc hr hP => static_untouched hE hH hc hr hP

theorem store_model_safe {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs)
    (E : Fs → Fs → Prop) :
    (sharedStore enc fs₀ E).model.Sat
      (Sen.atomic (A := Http.sig) fun r s => ∃ S S', storeStep S r = (s, S')) :=
  model_sat_atomic fun _ hH _ _ _ hc hr => store_safe hinj hH hc hr

theorem store_model_refines {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs)
    {E : Fs → Fs → Prop} (hE : Untouched E fun p => ∃ t, enc t = p) :
    (sharedStore enc fs₀ E).model.Refines (kv.machine.server (view enc fs₀)) :=
  model_refines_server (store_refines hinj fs₀ hE)

theorem store_model_sat_origin {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs)
    {E : Fs → Fs → Prop} (hE : Untouched E fun p => ∃ t, enc t = p) :
    (sharedStore enc fs₀ E).model.Sat (Http.originSen kv (view enc fs₀)) :=
  model_sat_lin (store_refines hinj fs₀ hE)

/-- **Over shared files, the store refines the core server of the store on the keys nobody
else touches.** -/
theorem store_model_refines_on {enc : Target → FPath} (hinj : Function.Injective enc)
    (fs₀ : Fs) (K : Target → Prop) [DecidablePred K] {E : Fs → Fs → Prop}
    (hE : Untouched E fun p => ∃ t, K t ∧ enc t = p) :
    (sharedStore enc fs₀ E).model.Refines
      ((kvOn K).machine.server (restrictKeys K (view enc fs₀))) :=
  model_refines_server (store_refines_on hinj fs₀ K hE)

theorem store_model_sat_lin_on {enc : Target → FPath} (hinj : Function.Injective enc)
    (fs₀ : Fs) (K : Target → Prop) [DecidablePred K] {E : Fs → Fs → Prop}
    (hE : Untouched E fun p => ∃ t, K t ∧ enc t = p) :
    (sharedStore enc fs₀ E).model.Sat
      (Sen.lin ((kvOn K).machine.Hist (restrictKeys K (view enc fs₀)))) :=
  model_sat_lin (store_refines_on hinj fs₀ K hE)

end SharedFs

end Silmaril.Servers.State

/-! ## The `wasi:http` store over `wasi:filesystem` -/

namespace Silmaril.Servers.WasiFs

open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Cli

/-- **The store component refines the core server of its specification.** -/
theorem wasiStore_model_refines (root : String) {fs₀ : Fs} (h₀ : Small fs₀) :
    (wasiStore root fs₀).model.Refines ((Atomic.ofFun (specStep root)).machine.server fs₀) :=
  model_refines_server (wasiStore_refines root h₀)

theorem wasiStore_model_sat_lin (root : String) {fs₀ : Fs} (h₀ : Small fs₀) :
    (wasiStore root fs₀).model.Sat (Sen.lin ((Atomic.ofFun (specStep root)).machine.Hist fs₀)) :=
  model_sat_lin (wasiStore_refines root h₀)

theorem wasiStoreSmall_model_refines (root : String) {fs₀ : Fs} (h₀ : Small fs₀) :
    (wasiStoreSmall root fs₀).model.Refines
      ((((Atomic.ofFun (fileStoreStep (keyFile root))).mapResp noFields).guard smallReq).machine.server
        fs₀) :=
  model_refines_server (wasiStoreSmall_refines root h₀)

end Silmaril.Servers.WasiFs

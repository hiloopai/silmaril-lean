module

public import Silmaril.Wasm.Resource.Component.Defs
public import Silmaril.Wasm.Spec.Component.RefMulti.Defs

@[expose] public section

/-!
# Components defining a resource, over several calls on one instance

`refSem` observes one call per fresh instance, so the component handle sentences hold of it
vacuously (`refSem_compProvider`). Over `refMultiSem` (several calls threading the machine
configuration) they do not: a component whose constructor returns a live representation again
is rejected. This file states verification conditions under which they hold.

* `MultiInv prof h σ0 p π Inv`: an **invariant method** for a protocol `π` over the multi-call
  traces of `p`. `Inv es q m` relates a protocol state `q` to a machine configuration `m`
  between calls (`es`: the instance's function exports). It must hold after every
  instantiation, every resolved call must step `π` and re-establish it, every last call (any
  behaviour) must be accepted, call events must never be rejected (they are the environment's)
  and a trap or divergence of the instantiation must be accepted.
* `CtrVC prof h p new ctr`: a **counter verification condition** for `compProviderSpec new
  drop`, the guest VC "the representations of live `own` handles are distinct" in its usual
  implementation: a measure `ctr` of configurations (for a counter-based guest, the value of
  its counter) that no resolved call decreases, such that every resolved call of the
  constructor `new` that returns `own n` returns `n ≥ ctr m` and ends with `ctr m' > n`.
  Under it every representation returned by `new` is above every representation returned
  before, so never live.
* `ctrInv ctr`: the invariant of `CtrVC`: every live representation is below the counter.
* `CtrVCOn prof h σ0 p new ctr R`, `ctrInvOn`: the same condition asked only from
  configurations satisfying a **reachability invariant** `R` (it holds after instantiation and
  is kept by resolved calls). `CtrVC` quantifies over all configurations, so it cannot hold for
  a `ctr` that reads a concrete component's store; `CtrVCOn` is the form to discharge.

The theorems (`multiInv_accepts`, `compProvider_of_ctr`, `compProvider_of_ctrOn`) are in
`Silmaril.Wasm.Resource.CompProvider.Thms`.

What the VC does not cover: discharging `CtrVC` for a concrete component needs the machine
runs of its export calls (`canon lift` of an `own` result reading the representation that the
guest passed to `resource.new`); this is not done here (see `docs/projects/wasm-components.md`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component (Calls)
open Silmaril.Wasm.Component.Runtime (FuncId CallId)
open Silmaril.Wasm.Component.Machine (Config)

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- An invariant method for a protocol over the multi-call traces of a reference component. -/
structure MultiInv (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ)
    {X : CIface} (p : RefProg E X) {S : Type} (π : Protocol S (CEvent X))
    (Inv : List (String × FuncId) → S → Config E σ → Prop) : Prop where
  /-- Call events (the environment's) are never rejected. -/
  calls : ∀ q j a, (π.step q (Event.call j a)).isSome
  /-- The invariant holds after every instantiation. -/
  init : ∀ m₀ inst es,
    InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) p.comp p.args →
    Inv es π.init m₀
  /-- A resolved call steps the protocol and re-establishes the invariant. -/
  done : ∀ es q m k j a f m' r, Inv es q m → es.lookup (p.names j) = some f →
    Calls prof h.hr h.dispatch m ⟨k⟩ f a m' (.resolved r) →
    ∃ q', π.run q [Event.call j a, Event.ret j (.returns r)] = some q' ∧ Inv es q' m'
  /-- Every behaviour of a last call is accepted. -/
  last : ∀ es q m k j a f b, Inv es q m → es.lookup (p.names j) = some f →
    b ∈ callBehaviours prof h m ⟨k⟩ f a → (π.run q [Event.call j a, Event.ret j b]).isSome
  /-- A trap or divergence of the instantiation is accepted. -/
  instFail : ∀ j a, (π.run π.init [Event.call j a, Event.ret j .traps]).isSome ∧
    (π.run π.init [Event.call j a, Event.ret j .diverges]).isSome

/-- The counter verification condition for a component defining a resource with constructor
`new`: no resolved call decreases `ctr`, and every resolved call of `new` returning `own n`
returns a representation at or above the counter and moves the counter past it. -/
structure CtrVC (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) {X : CIface}
    (p : RefProg E X) (new : X.Exp) (ctr : Config E σ → ℕ) : Prop where
  /-- Resolved calls do not decrease the counter. -/
  mono : ∀ (es : List (String × FuncId)) m k j f a m' r, es.lookup (p.names j) = some f →
    Calls prof h.hr h.dispatch m ⟨k⟩ f a m' (.resolved r) → ctr m ≤ ctr m'
  /-- The constructor returns fresh representations. -/
  fresh : ∀ (es : List (String × FuncId)) m k f a m' n, es.lookup (p.names new) = some f →
    Calls prof h.hr h.dispatch m ⟨k⟩ f a m' (.resolved (some [.own n])) → ctr m ≤ n ∧ n < ctr m'

/-- The invariant of `CtrVC`: the environment was blamed, or every live representation is below
the counter. -/
def ctrInv (ctr : Config E σ → ℕ) (_es : List (String × FuncId)) (q : Option (List ℕ))
    (m : Config E σ) : Prop :=
  q = none ∨ ∃ L, q = some L ∧ ∀ r ∈ L, r < ctr m

/-- The counter verification condition **on reachable configurations**: `CtrVC` asked only of
calls from configurations `m` with `R es m`, where `R` holds after every instantiation and is
kept by every resolved export call. `CtrVC` quantifies over every configuration, also
unreachable ones whose store holds other code, so it cannot be discharged for a concrete
component whose `ctr` reads its store; this form can. -/
structure CtrVCOn (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ)
    {X : CIface} (p : RefProg E X) (new : X.Exp) (ctr : Config E σ → ℕ)
    (R : List (String × FuncId) → Config E σ → Prop) : Prop where
  /-- `R` holds after every instantiation. -/
  init : ∀ m₀ inst es,
    InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) p.comp p.args →
    R es m₀
  /-- Resolved export calls keep `R`. -/
  step : ∀ es m k j f a m' r, R es m → es.lookup (p.names j) = some f →
    Calls prof h.hr h.dispatch m ⟨k⟩ f a m' (.resolved r) → R es m'
  /-- Resolved export calls from `R` do not decrease the counter. -/
  mono : ∀ es m k j f a m' r, R es m → es.lookup (p.names j) = some f →
    Calls prof h.hr h.dispatch m ⟨k⟩ f a m' (.resolved r) → ctr m ≤ ctr m'
  /-- The constructor called from `R` returns fresh representations. -/
  fresh : ∀ es m k f a m' n, R es m → es.lookup (p.names new) = some f →
    Calls prof h.hr h.dispatch m ⟨k⟩ f a m' (.resolved (some [.own n])) → ctr m ≤ n ∧ n < ctr m'

/-- The invariant of `CtrVCOn`: `ctrInv` on configurations satisfying `R`. -/
def ctrInvOn (ctr : Config E σ → ℕ) (R : List (String × FuncId) → Config E σ → Prop)
    (es : List (String × FuncId)) (q : Option (List ℕ)) (m : Config E σ) : Prop :=
  R es m ∧ ctrInv ctr es q m

end Silmaril.Wasm.Resource

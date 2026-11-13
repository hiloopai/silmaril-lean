module

public import Silmaril.Wasm.Component.Reference.Defs

/-!
# Determinism and statelessness modulo traps and imports for components

The component-level notions, over the reference Component Model machine
(`Silmaril.Wasm.Component.Reference`): its relations `Calls` (a top-level call of a component
function value) and `Instantiates` (root instantiation), at a component choice profile `prof`,
for an arbitrary core engine `E`. With `E = core3P P` the core modules run Core 3.0 at the
arbitrary profile `P` (`core3P` uses the relational step `Silmaril.Wasm.Game.InternalP P`).

**Imports.** In the component machine the host functions are part of the machine (`Host E σ`,
with host state `σ`); the import answers are whatever the host computes. The notions below are
stated **against a fixed host `h`**: two runs against the same host from the same machine
configuration (which includes the host state). "Modulo imports" is read as: for every host of
the class one considers (for example hosts whose functions are deterministic), the component is
deterministic against that host. A nondeterministic host can of course make every component
nondeterministic; that is not the component's nondeterminism.

**Traps.** Outcomes `CallOutcome.trap` are exempt; resolved values, cancellation and deadlock
are compared.

* per function value: `CallDet prof h m c f args` (two calls `c` of `f` on `args` from `m` that
  do not trap end with the same outcome in the same configuration), `CallAgree` (two calls from
  two configurations have the same non-trapping outcome);
* instantiation: `InstDet` (non-trapping instantiations coincide);
* per component: `CompReach prof h σ0 comp args m es` (configurations reachable by
  instantiating `comp` from the empty store, then any calls of its exports `es`),
  `CompDet` (instantiation and every export call from every reachable configuration are
  deterministic), `CompStateless` (calls of the same export on the same values from any two
  reachable configurations agree).

Theorems: `Silmaril.Wasm.Det.Core.Component.Thms`. New definitions. The Silmaril component IR
(`Silmaril.Wasm.Component`, `Comp.den`) is not covered here.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Core.Component

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference (Host initConfig Engine)

variable {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

/-- **Per function value**: two top-level calls `c` of `f` on `args` from `m` against the host
`h` that do not trap end with the same outcome in the same configuration. -/
def CallDet (prof : ProfileKind) (h : Host E σ) (m : Config E σ) (c : CallId) (f : FuncId)
    (args : List Value.Val) : Prop :=
  ∀ m₁ m₂ out₁ out₂, Calls prof h.hr h.dispatch m c f args m₁ out₁ →
    Calls prof h.hr h.dispatch m c f args m₂ out₂ → out₁ ≠ .trap → out₂ ≠ .trap →
      out₁ = out₂ ∧ m₁ = m₂

/-- Two top-level calls, of `f₁` from `m₁` and of `f₂` from `m₂`, on the same values, that do
not trap end with the same outcome. -/
def CallAgree (prof : ProfileKind) (h : Host E σ) (m₁ m₂ : Config E σ) (c : CallId)
    (f₁ f₂ : FuncId) (args : List Value.Val) : Prop :=
  ∀ m₁' m₂' out₁ out₂, Calls prof h.hr h.dispatch m₁ c f₁ args m₁' out₁ →
    Calls prof h.hr h.dispatch m₂ c f₂ args m₂' out₂ → out₁ ≠ .trap → out₂ ≠ .trap → out₁ = out₂

/-- Non-trapping instantiations of `comp` with `args` from `m` coincide. -/
def InstDet (prof : ProfileKind) (h : Host E σ) (m : Config E σ) (comp : Syntax.Component E.Module)
    (args : Instantiate.Exports E) : Prop :=
  ∀ m₁ m₂ i₁ i₂ es₁ es₂, Instantiates prof h.hr h.dispatch m comp args m₁ i₁ es₁ →
    Instantiates prof h.hr h.dispatch m comp args m₂ i₂ es₂ → m₁ = m₂ ∧ i₁ = i₂ ∧ es₁ = es₂

/-- The call states of a component: the configurations reached by instantiating `comp` from
the empty store with host state `σ0`, then by any sequence of finished top-level calls of its
function exports `es` (any outcome; the configuration persists across calls). -/
inductive CompReach (prof : ProfileKind) (h : Host E σ) (σ0 : σ)
    (comp : Syntax.Component E.Module) (args : Instantiate.Exports E) :
    Config E σ → List (String × FuncId) → Prop where
  | inst {m : Config E σ} {i : InstId} {es : List (String × FuncId)}
      (hi : Instantiates prof h.hr h.dispatch (initConfig σ0) comp args m i es) :
      CompReach prof h σ0 comp args m es
  | call {m m' : Config E σ} {es : List (String × FuncId)} {name : String} {f : FuncId}
      {c : CallId} {vals : List Value.Val} {out : CallOutcome}
      (hm : CompReach prof h σ0 comp args m es) (hf : es.lookup name = some f)
      (hc : Calls prof h.hr h.dispatch m c f vals m' out) : CompReach prof h σ0 comp args m' es

/-- **Per component**: instantiation is deterministic, and every call of every export from
every reachable configuration is deterministic, against the host `h`. -/
def CompDet (prof : ProfileKind) (h : Host E σ) (σ0 : σ) (comp : Syntax.Component E.Module)
    (args : Instantiate.Exports E) : Prop :=
  InstDet prof h (initConfig σ0) comp args ∧
    ∀ m es, CompReach prof h σ0 comp args m es → ∀ name f, es.lookup name = some f →
      ∀ c vals, CallDet prof h m c f vals

/-- **Per component, statelessness**: calls of the same export on the same values from any two
reachable configurations have the same non-trapping outcome, against the host `h`. -/
def CompStateless (prof : ProfileKind) (h : Host E σ) (σ0 : σ)
    (comp : Syntax.Component E.Module) (args : Instantiate.Exports E) : Prop :=
  ∀ m₁ es₁ m₂ es₂, CompReach prof h σ0 comp args m₁ es₁ → CompReach prof h σ0 comp args m₂ es₂ →
    ∀ name f₁ f₂, es₁.lookup name = some f₁ → es₂.lookup name = some f₂ →
      ∀ c vals, CallAgree prof h m₁ m₂ c f₁ f₂ vals

end Silmaril.Wasm.Det.Core.Component

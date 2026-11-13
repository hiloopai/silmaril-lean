module

public import Silmaril.Wasm.Det.Core.Component.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs

/-!
# The scratch-buffer discipline on the reference machine: definitions

Observable state and confinement stated over the reference Component Model machine
(`Silmaril.Wasm.Component.Reference`, the configurations and relations of
`Silmaril.Wasm.Det.Core.Component`), not over the hand-written ABI model of
`Silmaril.Wasm.Det.Component`.

* `RefConfined prof h σ0 comp args Obs`: instantiations of `comp` are `Obs`-related, and every
  finished top-level call of an export from a call state (`CompReach`) ends in a configuration
  `Obs`-related to its start (any outcome, traps included);
* `RefObsDetermines prof h σ0 comp args Obs`: calls of the same export on the same values from
  `Obs`-related call states have the same non-trapping outcome;
* `ScratchEqH m lo hi`: two core stores (any host type) are equal except on the bytes `[lo, hi)`
  of memory `m` (the host-generic form of `Silmaril.Wasm.Det.Component.ScratchEq`);
* `ScratchCfg m lo hi` (engine `core3P P`): the observable state of a machine configuration with a
  scratch region: equal configurations once the core store is erased (`eraseCore`) and
  `ScratchEqH`-related core stores.

**Fresh, admissible call sequences.** `CompReach` (and so `CompStateless`) lets the host reuse a
top-level call id. `Calls` reads the outcome of call `c` with `Config.result?`, which finds the
*first* recorded resolution of `c`, so after a resolved call `0` a second call `0` may report
the old result: with id reuse, `CompStateless` is expected to fail for components such as the
adder, whose export returns different results on different arguments. This is a property of
the definitions, not of the components (analysis; the refutation is not formalised here). The
session notions below use the ids `0, 1, …` in order (as `seqBehaviours` does), admissible
arguments only (`Adm name vals`, e.g. well-typed values) and resolved calls only (a trapped call
locks the store down; a deadlocked or cancelled one leaves the session):

* `SeqReach prof h σ0 comp args Adm m es k`: `m` is reached by instantiation, then `k` resolved
  calls `0, …, k-1` of exports on admissible arguments;
* `CompStatelessSeq`: from any two such configurations, the next call (with the next id) of one
  export on the same admissible values has the same non-trapping outcome;
* `RefConfinedSeq`, `RefObsDeterminesSeq`: confinement and observation over these sessions;
* `eraseBook` and `BookCfg m lo hi` (engine `core3P P`): **the scratch observable state ignoring
  the call bookkeeping**. Every top-level call necessarily changes, outside any scratch region,
  the machine's `pending`/`results`/`cancels`, saved continuations and control chain, the
  component store's `tasks`/`threads`/`callers` arenas and the thread tables of the instances
  (a thread slot is allocated and freed); `eraseBook` erases exactly these (and the core store),
  `BookCfg` compares what remains and the core stores up to the bytes `[lo, hi)` of memory `m`.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.CompScratch

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference (Host initConfig Engine core3P)
open Silmaril.Wasm.Det.Core.Component

variable {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

/-- **Confinement on the reference machine**: instantiations are `Obs`-related and every call of
an export from a call state ends `Obs`-related to its start. -/
structure RefConfined (prof : ProfileKind) (h : Host E σ) (σ0 : σ)
    (comp : Syntax.Component E.Module) (args : Instantiate.Exports E)
    (Obs : Config E σ → Config E σ → Prop) : Prop where
  inst : ∀ m₁ m₂ i₁ i₂ es₁ es₂, Instantiates prof h.hr h.dispatch (initConfig σ0) comp args m₁ i₁ es₁ →
    Instantiates prof h.hr h.dispatch (initConfig σ0) comp args m₂ i₂ es₂ → Obs m₁ m₂
  call : ∀ m es, CompReach prof h σ0 comp args m es → ∀ name f c vals m' out,
    es.lookup name = some f → Calls prof h.hr h.dispatch m c f vals m' out → Obs m m'

/-- **Observation on the reference machine**: calls of one export from `Obs`-related call states
agree on non-trapping outcomes. -/
def RefObsDetermines (prof : ProfileKind) (h : Host E σ) (σ0 : σ)
    (comp : Syntax.Component E.Module) (args : Instantiate.Exports E)
    (Obs : Config E σ → Config E σ → Prop) : Prop :=
  ∀ m₁ es₁ m₂ es₂, CompReach prof h σ0 comp args m₁ es₁ → CompReach prof h σ0 comp args m₂ es₂ →
    Obs m₁ m₂ → ∀ name f₁ f₂, es₁.lookup name = some f₁ → es₂.lookup name = some f₂ →
      ∀ c vals, CallAgree prof h m₁ m₂ c f₁ f₂ vals

/-- Core stores equal except on the bytes `[lo, hi)` of memory `m` (any host type). -/
def ScratchEqH {H : Type} (m lo hi : Nat) (s₁ s₂ : Silmaril.Wasm.Execution.Core.Store H) : Prop :=
  { s₁ with mems := [] } = { s₂ with mems := [] } ∧ s₁.mems.length = s₂.mems.length ∧
    (∀ j, j ≠ m → s₁.mems[j]? = s₂.mems[j]?) ∧
    ∀ mi₁ mi₂, s₁.mems[m]? = some mi₁ → s₂.mems[m]? = some mi₂ →
      mi₁.type = mi₂.type ∧ mi₁.bytes.size = mi₂.bytes.size ∧
        ∀ k, (k < lo ∨ hi ≤ k) → mi₁.bytes.data[k]? = mi₂.bytes.data[k]?

/-- A configuration with its core store erased. -/
def eraseCore {E : Engine} {σ : Type} (m : Config E σ) : Config E σ :=
  { m with store := { m.store with core := E.empty _ } }

/-- **The scratch observable state** of reference configurations over `core3P P`: equal up to the
core store, whose stores agree outside the scratch bytes. -/
def ScratchCfg {P : Silmaril.Wasm.Numerics.Profile} {σ : Type} (m lo hi : Nat)
    (c₁ c₂ : Config (core3P P) σ) : Prop :=
  eraseCore c₁ = eraseCore c₂ ∧ ScratchEqH m lo hi c₁.store.core c₂.store.core

/-! ## Fresh, admissible call sequences -/

/-- Configurations of a session: instantiation of `comp` from the empty store, then `k` resolved
top-level calls with the ids `0, …, k-1` of exports on admissible arguments. -/
inductive SeqReach (prof : ProfileKind) (h : Host E σ) (σ0 : σ)
    (comp : Syntax.Component E.Module) (args : Instantiate.Exports E)
    (Adm : String → List Value.Val → Prop) :
    Config E σ → List (String × FuncId) → Nat → Prop where
  | inst {m : Config E σ} {i : InstId} {es : List (String × FuncId)}
      (hi : Instantiates prof h.hr h.dispatch (initConfig σ0) comp args m i es) :
      SeqReach prof h σ0 comp args Adm m es 0
  | call {m m' : Config E σ} {es : List (String × FuncId)} {k : Nat} {name : String}
      {f : FuncId} {vals rs : List Value.Val}
      (hm : SeqReach prof h σ0 comp args Adm m es k) (hf : es.lookup name = some f)
      (ha : Adm name vals)
      (hc : Calls prof h.hr h.dispatch m ⟨k⟩ f vals m' (.resolved (some rs))) :
      SeqReach prof h σ0 comp args Adm m' es (k + 1)

/-- Calls of `f₁` from `m₁` as call `c₁` and of `f₂` from `m₂` as call `c₂`, on the same values,
that do not trap end with the same outcome. -/
def CallAgreeAt (prof : ProfileKind) (h : Host E σ) (m₁ m₂ : Config E σ) (c₁ c₂ : CallId)
    (f₁ f₂ : FuncId) (vals : List Value.Val) : Prop :=
  ∀ m₁' m₂' out₁ out₂, Calls prof h.hr h.dispatch m₁ c₁ f₁ vals m₁' out₁ →
    Calls prof h.hr h.dispatch m₂ c₂ f₂ vals m₂' out₂ → out₁ ≠ .trap → out₂ ≠ .trap → out₁ = out₂

/-- **Statelessness over sessions**: from any two session configurations, the next call of one
export on the same admissible values has the same non-trapping outcome. -/
def CompStatelessSeq (prof : ProfileKind) (h : Host E σ) (σ0 : σ)
    (comp : Syntax.Component E.Module) (args : Instantiate.Exports E)
    (Adm : String → List Value.Val → Prop) : Prop :=
  ∀ m₁ es₁ k₁ m₂ es₂ k₂, SeqReach prof h σ0 comp args Adm m₁ es₁ k₁ →
    SeqReach prof h σ0 comp args Adm m₂ es₂ k₂ → ∀ name f₁ f₂, es₁.lookup name = some f₁ →
      es₂.lookup name = some f₂ → ∀ vals, Adm name vals →
        CallAgreeAt prof h m₁ m₂ ⟨k₁⟩ ⟨k₂⟩ f₁ f₂ vals

/-- **Confinement over sessions**: instantiations are `Obs`-related, and every resolved
admissible call of the session ends `Obs`-related to its start. -/
structure RefConfinedSeq (prof : ProfileKind) (h : Host E σ) (σ0 : σ)
    (comp : Syntax.Component E.Module) (args : Instantiate.Exports E)
    (Adm : String → List Value.Val → Prop) (Obs : Config E σ → Config E σ → Prop) : Prop where
  inst : ∀ m₁ m₂ i₁ i₂ es₁ es₂, Instantiates prof h.hr h.dispatch (initConfig σ0) comp args m₁ i₁ es₁ →
    Instantiates prof h.hr h.dispatch (initConfig σ0) comp args m₂ i₂ es₂ → Obs m₁ m₂
  call : ∀ m es k, SeqReach prof h σ0 comp args Adm m es k → ∀ name f vals m' rs,
    es.lookup name = some f → Adm name vals →
    Calls prof h.hr h.dispatch m ⟨k⟩ f vals m' (.resolved (some rs)) → Obs m m'

/-- **Observation over sessions**: from `Obs`-related session configurations, the next call of
one export on the same admissible values has the same non-trapping outcome. -/
def RefObsDeterminesSeq (prof : ProfileKind) (h : Host E σ) (σ0 : σ)
    (comp : Syntax.Component E.Module) (args : Instantiate.Exports E)
    (Adm : String → List Value.Val → Prop) (Obs : Config E σ → Config E σ → Prop) : Prop :=
  ∀ m₁ es₁ k₁ m₂ es₂ k₂, SeqReach prof h σ0 comp args Adm m₁ es₁ k₁ →
    SeqReach prof h σ0 comp args Adm m₂ es₂ k₂ → Obs m₁ m₂ → ∀ name f₁ f₂,
      es₁.lookup name = some f₁ → es₂.lookup name = some f₂ → ∀ vals, Adm name vals →
        CallAgreeAt prof h m₁ m₂ ⟨k₁⟩ ⟨k₂⟩ f₁ f₂ vals

/-- An instance state with its thread table erased. -/
def eraseThreads (ι : InstState) : InstState := { ι with threads := .empty }

/-- The admissible calls of a simple component (`Silmaril.Wasm.Component.Reference.Simple`): an
export by name, on the reference images of IR values of its parameter types. -/
def SimpleAdm (c : Silmaril.Wasm.Component.Reference.Simple) (name : String)
    (vals : List Value.Val) : Prop :=
  ∃ (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val), name = c.exports[j].name ∧
    vals = vs.map Silmaril.Wasm.Component.Reference.toRefVal ∧
    Silmaril.Wasm.Component.ValTy.checkList c.exports[j].ty.params vs = true

/-- A configuration with its core store and its call bookkeeping erased. -/
def eraseBook {E : Engine} {σ : Type} (m : Config E σ) : Config E σ :=
  { m with
    conts := []
    ctl := []
    pending := []
    results := []
    cancels := []
    store := { m.store with
      core := E.empty _
      tasks := []
      threads := []
      callers := []
      insts := m.store.insts.map eraseThreads } }

/-- **The scratch observable state ignoring the call bookkeeping** (engine `core3P P`). -/
def BookCfg {P : Silmaril.Wasm.Numerics.Profile} {σ : Type} (m lo hi : Nat)
    (c₁ c₂ : Config (core3P P) σ) : Prop :=
  eraseBook c₁ = eraseBook c₂ ∧ ScratchEqH m lo hi c₁.store.core c₂.store.core

end Silmaril.Wasm.Det.CompScratch

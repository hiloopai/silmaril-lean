module

public import Silmaril.Wasm.Component.RefValid.Defs
public import Silmaril.Wasm.Component.Reference.Embedding.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Instance.Defs
public import Silmaril.Wasm.Game.Machine.Defs

/-!
# The reference semantics of the WebAssembly Component Model

The names below are the stable interface for Silmaril developments:

* syntax and types: `CompAst M` (the index-based component AST over core modules `M`),
  `Core3Component` (core modules are Core 3.0 modules), component types `ComponentType`,
  validation `Valid` with its checker `check?` (Core 3.0 profile);
* values: `Val` (component values), `ValType` (WIT value types);
* the core-engine interface `CoreEngine` and the Core 3.0 engine **at an arbitrary
  profile** `core3P P`: `core3 o` with its interpreter step and status replaced by the
  relational single-threaded step `Silmaril.Wasm.Game.InternalP P` and the status
  `Silmaril.Wasm.Game.statusP P` read at the flat boundary (`flatStatus`);
* the host side of the component machine, `Host E σ` (limits, quirks, host readiness and host
  functions), and its dispatcher `Host.dispatch`;
* observable behaviour: `Outcome` (returned values, trap, deadlock, divergence),
  `callBehaviours` (a top-level call of a component function value, from a machine
  configuration), `instBehaviours` (root instantiation) and `exportBehaviours` (instantiate a
  component from the empty store, then call one of its exports by name).

Every relation is the copied machine's (`Calls`, `CallDiverges`, `Instantiates`,
`InstantiateTraps`, `InstantiateDiverges` of `Silmaril.Raw.Wasm.Component.Embedding`), at an
arbitrary component choice profile `prof` and an arbitrary core engine. Theorems are in
`Silmaril.Wasm.Component.Reference.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Numerics (Profile)

/-! ## Syntax, types and validation

`CompAst`, `Core3Component`, `ComponentType`, `Valid` and `check?` are declared in
`Silmaril.Wasm.Component.RefValid` (no component machine), re-exported here. -/

/-- Component values. -/
abbrev Val : Type := Value.Val

/-! ## Core engines -/

/-- The core-engine interface of the component machine. -/
abbrev Engine : Type 1 := Silmaril.Wasm.Component.Engine.CoreEngine

/-- A single-threaded status at the flat canonical-ABI boundary: results and callout arguments
that are not all numeric are `stuck` (as in `Core3.statusE`). -/
def flatStatus {H : Type} : Silmaril.Wasm.SingleThreaded.Status H → Status H
  | .running => .running
  | .returned (.values vs) =>
    match vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
    | some fvs => .returned (.values fvs)
    | none => .stuck
  | .returned .trap => .returned .trap
  | .callout h args =>
    match args.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
    | some fargs => .callout h fargs
    | none => .stuck
  | .stuck => .stuck

/-- **The Core 3.0 engine at an arbitrary profile** `P` (any `$ND`, relaxed choices, NaN
policy and grow policy): modules, types, validation, instantiation, stores, memories, tables,
callouts and resumption are those of silmaril-lean's `core3`; the internal step is the relational
single-threaded step `InternalP P` and the status is `statusP P` at the flat boundary.
(`core3 o` uses no grow oracle outside these two fields; `neverFail` only fills the
parameter.) -/
noncomputable def core3P (P : Profile) : Engine :=
  { core3 Silmaril.Wasm.SingleThreaded.neverFail with
    status := fun s t => flatStatus (Silmaril.Wasm.Game.statusP P s t)
    Internal := fun c c' => Silmaril.Wasm.Game.InternalP P c c' }

/-- Import matching of `core3P P` is that of `core3`, hence decidable. -/
instance core3P_decExternSub (P : Profile) (a b : (core3P P).ExternType) :
    Decidable ((core3P P).ExternSub a b) :=
  core3_decExternSub Silmaril.Wasm.SingleThreaded.neverFail a b

/-! ## Hosts and behaviours -/

/-- The host side of a component machine over engine `E` and host state `σ`: limits and quirks
(`Limits.spec` and `Quirks.none` are the specification), the readiness of host waitables and
the host functions. -/
structure Host (E : Engine) (σ : Type) where
  lim : Limits := Limits.spec
  q : Quirks := Quirks.none
  hr : HostReady σ
  impl : HostImpl E σ

variable {E : Engine} {σ : Type}

/-- The late-bound call dispatcher of a host (`Canon.dispatch`). -/
abbrev Host.dispatch [∀ a b, Decidable (E.ExternSub a b)] (h : Host E σ) :
    Call E → P E σ (Ret E) :=
  Canon.dispatch h.lim h.q h.hr h.impl

/-- The host of an embedder. -/
def Host.ofEmbedder (emb : Embedder E σ) : Host E σ :=
  { lim := emb.lim, q := emb.q, hr := emb.hr, impl := emb.host }

/-- The initial machine configuration: the empty component store, host state `σ0`, the host in
control (REF `Store()`). -/
def initConfig (σ0 : σ) : Config E σ := Config.init CStore.empty σ0

/-- An observable behaviour of a top-level call or instantiation. -/
inductive Outcome where
  /-- The call resolved with these results (`none`: cancelled). -/
  | returns (r : Option (List Val))
  /-- A specification trap (never a model fault `TrapReason.internal`). -/
  | traps
  /-- The call is unresolved and no thread can make progress. -/
  | deadlocks
  /-- Infinitely many internal steps. -/
  | diverges

/-- The outcome of a finished call. -/
def Outcome.ofCall : CallOutcome → Outcome
  | .resolved r => .returns r
  | .trap => .traps
  | .deadlock => .deadlocks

variable [∀ a b, Decidable (E.ExternSub a b)]

/-- **The behaviours of a top-level call** `c` of the function value `f` on the component values
`args` from configuration `m`, at component choice profile `prof`: the outcomes of the
machine's `Calls` relation, and divergence (`CallDiverges`). -/
def callBehaviours (prof : ProfileKind) (h : Host E σ) (m : Config E σ) (c : CallId)
    (f : FuncId) (args : List Val) : Set Outcome :=
  {b | (∃ m' out, Calls prof h.hr h.dispatch m c f args m' out ∧ b = Outcome.ofCall out) ∨
    (b = .diverges ∧ CallDiverges prof h.hr h.dispatch m c f args)}

/-- A result of root instantiation: an instance with its function exports and the configuration
reached, a trap, or divergence. -/
inductive InstResult (E : Engine) (σ : Type) where
  | instance (m : Config E σ) (inst : InstId) (exports : List (String × FuncId))
  | traps
  | diverges

/-- **The results of instantiating** the component `c` with the root arguments `args` from `m`
(`Instantiates`, `InstantiateTraps`, `InstantiateDiverges`). -/
def instBehaviours (prof : ProfileKind) (h : Host E σ) (m : Config E σ)
    (c : CompAst E.Module) (args : Instantiate.Exports E) : Set (InstResult E σ) :=
  {r | match r with
    | .instance m' inst es => Instantiates prof h.hr h.dispatch m c args m' inst es
    | .traps => ∃ m', InstantiateTraps prof h.hr h.dispatch m c args m'
    | .diverges => InstantiateDiverges prof h.hr h.dispatch m c args}

/-- **The observable behaviour of calling an export**: instantiate `c` with `args` from the
empty store with host state `σ0`, then call its function export `name` on `vals` as top-level
call `0`. A trap or divergence of the instantiation is a behaviour of the whole run. An export
that does not exist contributes nothing. -/
def exportBehaviours (prof : ProfileKind) (h : Host E σ) (σ0 : σ) (c : CompAst E.Module)
    (args : Instantiate.Exports E) (name : String) (vals : List Val) : Set Outcome :=
  {b | (∃ m₁ inst es f, InstResult.instance m₁ inst es ∈ instBehaviours prof h (initConfig σ0) c args ∧
        es.lookup name = some f ∧ b ∈ callBehaviours prof h m₁ ⟨0⟩ f vals) ∨
    (b = .traps ∧ InstResult.traps ∈ instBehaviours prof h (initConfig σ0) c args) ∨
    (b = .diverges ∧ InstResult.diverges ∈ instBehaviours prof h (initConfig σ0) c args)}

end Silmaril.Wasm.Component.Reference

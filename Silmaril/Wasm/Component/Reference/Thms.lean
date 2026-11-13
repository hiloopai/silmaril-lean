module

public import Silmaril.Wasm.Component.Reference.Defs
import Silmaril.Proofs.Wasm.Component.Reference.Basic

/-!
# The reference semantics of the WebAssembly Component Model: theorems

* validation: the checker is sound (`check?_sound`);
* the Core 3.0 engine at a profile: `core3P P` is `core3 o` except for its step and status
  (`core3P_with_core3`), its step is `InternalP P` (`core3P_internal_iff`), at `profile o`
  silmaril-lean's relational `Internal o` (`core3P_profile_internal_iff`), and its status is
  the flat view of `statusP P` (`core3P_status`); `core3 o`'s own status is the flat view of
  the interpreter's (`statusE_eq_flatStatus`);
* the copied executable drivers are sound for the behaviour sets (`callTop_mem`,
  `instantiateRun_mem`, `exportBehaviours_of_run`);
* end to end on the Mock engine: the constant component's export returns `[u32 42]`
  (`const_export_returns`); the Core 3.0 adder is in
  `Silmaril.Wasm.Component.Reference.Example.Thms`.

Not shown here: that `core3P (profile o)` and `core3 o` have the same behaviours (the
interpreter agrees with the relational step only on typed threads and up to bubbling of traps
and exceptions, `Engine/Core3/Agreement.lean`), the engine laws `CoreEngine.Lawful` for
`core3P P`, or any completeness of the executable drivers.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.Basic`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Numerics (Profile)

/-- The executable validator is sound. -/
theorem check?_sound {feat : Features} {c : Core3Component} {ct : ComponentType}
    (h : check? feat c = .ok ct) : Valid feat c ct :=
  Silmaril.Proofs.Wasm.Component.Reference.check?_sound h

/-- `core3 o`'s status is the flat view of the interpreter's status. -/
theorem statusE_eq_flatStatus {H : Type} (o : Silmaril.Wasm.SingleThreaded.GrowOracle)
    (s : Silmaril.Wasm.Execution.Core.Store H) (t : Silmaril.Wasm.SingleThreaded.Thread) :
    Core3.statusE o s t =
      flatStatus (Silmaril.Wasm.SingleThreaded.statusC
        (Silmaril.Wasm.SingleThreaded.Exec.stepI o) s t) :=
  Silmaril.Proofs.Wasm.Component.Reference.statusE_eq_flatStatus o s t

/-- `core3P P` differs from `core3 o` only in its step and its status. -/
theorem core3P_with_core3 (P : Profile) (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    ({ core3P P with status := (core3 o).status, Internal := (core3 o).Internal } : Engine) =
      core3 o :=
  Silmaril.Proofs.Wasm.Component.Reference.core3P_with_core3 P o

/-- The internal step of `core3P P` is the single-threaded step at profile `P`. -/
theorem core3P_internal_iff {P : Profile} {H : Type}
    {c c' : Silmaril.Wasm.Execution.Core.Store H × Silmaril.Wasm.SingleThreaded.Thread} :
    (core3P P).Internal c c' ↔ Silmaril.Wasm.Game.InternalP P c c' :=
  Silmaril.Proofs.Wasm.Component.Reference.core3P_internal_iff

/-- At `profile o` the internal step of `core3P` is silmaril-lean's `Internal o`. -/
theorem core3P_profile_internal_iff {o : Silmaril.Wasm.SingleThreaded.GrowOracle} {H : Type}
    {c c' : Silmaril.Wasm.Execution.Core.Store H × Silmaril.Wasm.SingleThreaded.Thread} :
    (core3P (Silmaril.Wasm.SingleThreaded.profile o)).Internal c c' ↔
      Silmaril.Wasm.SingleThreaded.Internal o c c' :=
  Silmaril.Proofs.Wasm.Component.Reference.core3P_profile_internal_iff

/-- The status of `core3P P` is the flat view of `statusP P`. -/
theorem core3P_status {P : Profile} {H : Type} (s : Silmaril.Wasm.Execution.Core.Store H)
    (t : Silmaril.Wasm.SingleThreaded.Thread) :
    (core3P P).status s t = flatStatus (Silmaril.Wasm.Game.statusP P s t) :=
  Silmaril.Proofs.Wasm.Component.Reference.core3P_status s t

variable {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

/-- A classified executable top-level call is a behaviour of the call. -/
theorem callTop_mem (emb : Embedder E σ) (o : Oracle E) {fuel : Nat} {c : CallId} {f : FuncId}
    {args : List Val} {m : Config E σ} {r : RunResult E σ o.State} {out : CallOutcome}
    (h : emb.callTop o fuel c f args m = some r) (ho : callOutcome? c r = some out) :
    Outcome.ofCall out ∈ callBehaviours o.prof (Host.ofEmbedder emb) m c f args :=
  Silmaril.Proofs.Wasm.Component.Reference.callTop_mem emb o h ho

/-- An executable instantiation with a decoded result is an instantiation result. -/
theorem instantiateRun_mem (emb : Embedder E σ) (o : Oracle E) {fuel : Nat}
    {c : CompAst E.Module} {args : Instantiate.Exports E} {m : Config E σ}
    {r : RunResult E σ o.State} {inst : InstId} {es : List (String × FuncId)}
    (h : emb.instantiateRun o fuel c args m = some (r, inst, es)) :
    InstResult.instance r.config inst es ∈ instBehaviours o.prof (Host.ofEmbedder emb) m c args :=
  Silmaril.Proofs.Wasm.Component.Reference.instantiateRun_mem emb o h

/-- Executable instantiation from the empty store, then a classified executable call of the
export `name`, is a behaviour of calling that export. -/
theorem exportBehaviours_of_run (emb : Embedder E σ) (o : Oracle E) (σ0 : σ) {fuel fuel' : Nat}
    {c : CompAst E.Module} {args : Instantiate.Exports E} {name : String} {vals : List Val}
    {r₁ : RunResult E σ o.State} {inst : InstId} {es : List (String × FuncId)} {f : FuncId}
    {r : RunResult E σ o.State} {out : CallOutcome}
    (hi : emb.instantiateRun o fuel c args (initConfig σ0) = some (r₁, inst, es))
    (hf : es.lookup name = some f)
    (hc : emb.callTop o fuel' ⟨0⟩ f vals r₁.config = some r)
    (ho : callOutcome? ⟨0⟩ r = some out) :
    Outcome.ofCall out ∈ exportBehaviours o.prof (Host.ofEmbedder emb) σ0 c args name vals :=
  Silmaril.Proofs.Wasm.Component.Reference.exportBehaviours_of_run emb o σ0 hi hf hc ho

/-- On the Mock engine, the constant component's export `"f"` returns `[u32 42]`. -/
theorem const_export_returns :
    Outcome.returns (some [Value.Val.u32 42]) ∈
      exportBehaviours EmbeddingTests.first.prof (Host.ofEmbedder EmbeddingTests.smokeEmb) ()
        EmbeddingTests.constComponent [] "f" [] :=
  Silmaril.Proofs.Wasm.Component.Reference.const_export_returns

end Silmaril.Wasm.Component.Reference

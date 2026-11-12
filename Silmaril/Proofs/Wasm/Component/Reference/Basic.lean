module

public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The component-model reference semantics: proofs

Validation by the checker, soundness of the copied executable drivers for the behaviour sets of
`Silmaril.Wasm.Component.Reference.Defs`, and the relation of `core3P` to silmaril-lean's
`core3 o`.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Numerics (Profile)

/-! ## Validation -/

theorem check?_sound {feat : Features} {c : Core3Component} {ct : ComponentType}
    (h : check? feat c = .ok ct) : Valid feat c ct :=
  Validation.checkCore3?_sound h

/-! ## The Core 3.0 engine at a profile -/

/-- `core3 o`'s status is the flat view of the interpreter's status. -/
theorem statusE_eq_flatStatus {H : Type} (o : Silmaril.Wasm.SingleThreaded.GrowOracle)
    (s : Silmaril.Wasm.Execution.Core.Store H) (t : Silmaril.Wasm.SingleThreaded.Thread) :
    Core3.statusE o s t =
      flatStatus (Silmaril.Wasm.SingleThreaded.statusC
        (Silmaril.Wasm.SingleThreaded.Exec.stepI o) s t) := by
  unfold Core3.statusE
  generalize Silmaril.Wasm.SingleThreaded.statusC (Silmaril.Wasm.SingleThreaded.Exec.stepI o) s t = st
  cases st with
  | returned r => cases r <;> rfl
  | _ => rfl

/-- Replacing the step and the status of `core3P P` by those of `core3 o` gives `core3 o`. -/
theorem core3P_with_core3 (P : Profile) (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    ({ core3P P with status := (core3 o).status, Internal := (core3 o).Internal } : Engine) =
      core3 o :=
  rfl

/-- The internal step of `core3P P` is `InternalP P`. -/
theorem core3P_internal_iff {P : Profile} {H : Type}
    {c c' : Silmaril.Wasm.Execution.Core.Store H × Silmaril.Wasm.SingleThreaded.Thread} :
    (core3P P).Internal c c' ↔ Silmaril.Wasm.Game.InternalP P c c' :=
  Iff.rfl

/-- At the deterministic profile `profile o`, the internal step of `core3P` is
silmaril-lean's relational single-threaded step `Internal o`. -/
theorem core3P_profile_internal_iff {o : Silmaril.Wasm.SingleThreaded.GrowOracle} {H : Type}
    {c c' : Silmaril.Wasm.Execution.Core.Store H × Silmaril.Wasm.SingleThreaded.Thread} :
    (core3P (Silmaril.Wasm.SingleThreaded.profile o)).Internal c c' ↔
      Silmaril.Wasm.SingleThreaded.Internal o c c' := by
  rw [core3P_internal_iff, Silmaril.Wasm.Game.internalP_profile]

/-- The status of `core3P P` is the flat view of `statusP P`. -/
theorem core3P_status {P : Profile} {H : Type} (s : Silmaril.Wasm.Execution.Core.Store H)
    (t : Silmaril.Wasm.SingleThreaded.Thread) :
    (core3P P).status s t = flatStatus (Silmaril.Wasm.Game.statusP P s t) :=
  rfl

/-! ## Executable drivers -/

variable {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

theorem dispatch_ofEmbedder (emb : Embedder E σ) :
    (Host.ofEmbedder emb).dispatch = emb.dispatch :=
  rfl

/-- A classified executable top-level call is a behaviour of the call. -/
theorem callTop_mem (emb : Embedder E σ) (o : Oracle E) {fuel : Nat} {c : CallId} {f : FuncId}
    {args : List Silmaril.Wasm.Component.Reference.Val} {m : Config E σ} {r : RunResult E σ o.State} {out : CallOutcome}
    (h : emb.callTop o fuel c f args m = some r) (ho : callOutcome? c r = some out) :
    Outcome.ofCall out ∈ callBehaviours o.prof (Host.ofEmbedder emb) m c f args :=
  Or.inl ⟨r.config, out, emb.callTop_sound o h ho, rfl⟩

/-- An executable instantiation with a decoded result is an instantiation result. -/
theorem instantiateRun_mem (emb : Embedder E σ) (o : Oracle E) {fuel : Nat}
    {c : CompAst E.Module} {args : Instantiate.Exports E} {m : Config E σ}
    {r : RunResult E σ o.State} {inst : InstId} {es : List (String × FuncId)}
    (h : emb.instantiateRun o fuel c args m = some (r, inst, es)) :
    InstResult.instance r.config inst es ∈ instBehaviours o.prof (Host.ofEmbedder emb) m c args :=
  emb.instantiateRun_sound o h

/-- An executable instantiation from the initial configuration followed by a classified
executable call of the export `name` is a behaviour of calling that export. -/
theorem exportBehaviours_of_run (emb : Embedder E σ) (o : Oracle E) (σ0 : σ) {fuel fuel' : Nat}
    {c : CompAst E.Module} {args : Instantiate.Exports E} {name : String} {vals : List Silmaril.Wasm.Component.Reference.Val}
    {r₁ : RunResult E σ o.State} {inst : InstId} {es : List (String × FuncId)} {f : FuncId}
    {r : RunResult E σ o.State} {out : CallOutcome}
    (hi : emb.instantiateRun o fuel c args (initConfig σ0) = some (r₁, inst, es))
    (hf : es.lookup name = some f)
    (hc : emb.callTop o fuel' ⟨0⟩ f vals r₁.config = some r)
    (ho : callOutcome? ⟨0⟩ r = some out) :
    Outcome.ofCall out ∈ exportBehaviours o.prof (Host.ofEmbedder emb) σ0 c args name vals :=
  Or.inl ⟨r₁.config, inst, es, f, instantiateRun_mem emb o hi, hf, callTop_mem emb o hc ho⟩

/-! ## A smoke test on the Mock engine -/

/-- The copied smoke machine starts in the initial configuration. -/
theorem smokeMachine_config :
    EmbeddingTests.smokeMachine.config = (initConfig () : Config Mock.mock Unit) :=
  rfl

/-- The component exporting `f() = 42` (copied `constComponent`, Mock engine): calling its
export `"f"` after instantiation from the empty store returns `[42]`. -/
theorem const_export_returns :
    Outcome.returns (some [Value.Val.u32 42]) ∈
      exportBehaviours EmbeddingTests.first.prof (Host.ofEmbedder EmbeddingTests.smokeEmb) ()
        EmbeddingTests.constComponent [] "f" [] := by
  obtain ⟨m₁, m', hi, hc⟩ := EmbeddingTests.const_calls
  exact Or.inl ⟨m₁, ⟨0⟩, [("f", ⟨0⟩)], ⟨0⟩, hi, rfl, Or.inl ⟨m', _, hc, rfl⟩⟩

end Silmaril.Proofs.Wasm.Component.Reference

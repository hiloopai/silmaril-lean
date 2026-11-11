module

public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Wasm.Game.Start.Thms
import Silmaril.Proofs.Wasm.Game.SpecInst.Basic
import Silmaril.Proofs.Wasm.Game.Start.Main

/-!
# Spec-faithful instantiation: theorems

For an **arbitrary** silmaril profile `P` (no determinism is used), a spec
instance `IsSpecInstance m mt I c₀` and an environment `K` throwing only
existing exceptions:

* `IsSpecInstanceAt.*`: the same theorems for instantiation into an arbitrary
  typed store `s` against addresses `xas` of the module's import types (imported
  globals, memories, tables, tags and Wasm functions owned by the closed
  program; the host functions of `s` are the imports of the game);
  `IsSpecInstance.toAt` makes `IsSpecInstance` the case of fresh host
  functions;
* `IsSpecInstance.instantiate`: `c₀` is the configuration of the
  specification's `$instantiate` (silmaril-lean's `Instantiate P host`) of `m`
  against the import addresses, for every profile and host;
* `IsSpecInstance.ok`: `c₀` is typed at `[]` and the instance is well formed
  at its store;
* `IsSpecInstance.adequacy_inst`: the instantiation observations of the closed
  program `I.closedSpec P c₀ K` (`ready` as `returns []`, `fail b` as `b`,
  divergence after `[askInst]` as `diverges`) are **exactly** the closed-world
  Core 3.0 behaviours `behavioursOf P (hostOf I.imports K) c₀` of the
  instantiation configuration: segment initialisation (which may trap) and
  then the module's start function (which may call imports, trap, throw or
  diverge), reduced by unchanged Core 3.0 `Step P`;
* `closedSpec_instReady_iff`, `closedSpec_instFails_iff`,
  `closedSpec_instDiverges_iff`: the three instantiation outcomes separately
  (no well-formedness needed);
* `IsSpecInstance.adequacy_after_inst`: the observations of an export call
  right after instantiation are its Core behaviours at the stores the spec's
  instantiation run may return at (`InstantiatesTo`): Core
  "instantiate-then-invoke".

These discharge the gap left by `IsInstanceStart` (whose Core side is
silmaril-lean's `instantiateOnce?` followed by `$invoke(start, [])`): the start
phase here is the spec's configuration itself, so no confluence or uniqueness
of the segment-initialisation prefix is needed under any profile.

Proofs: `Silmaril.Proofs.Wasm.Game.SpecInst.Basic` and the thread-general start
phase `Silmaril.Proofs.Wasm.Game.Start.Main` (`adequacy_instT`,
`adequacy_after_instT`). New.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Games.Inst Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

variable {m : Module} {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
  {s : Store Nat} {xas : List ExternAddr}

/-! ## Instances at an arbitrary store -/

/-- **The start phase is the specification's instantiation**: the configuration of a spec
instance at `s` is the configuration of `$instantiate` into `s`, for every profile and host. -/
theorem IsSpecInstanceAt.instantiate (h : IsSpecInstanceAt s xas m mt I c₀) (P : Profile)
    (host : HostSemantics Nat) : Instantiate P host s m xas c₀ :=
  Silmaril.Proofs.Wasm.Game.SpecInst.IsSpecInstanceAt.instantiate h P host

/-- The store of a spec instance at `s` is the store of its configuration. -/
theorem IsSpecInstanceAt.store_eq (h : IsSpecInstanceAt s xas m mt I c₀) : c₀.store = I.store :=
  Silmaril.Proofs.Wasm.Game.SpecInst.IsSpecInstanceAt.store_eq h

/-- **Spec instances at `s` are typed and well formed.** -/
theorem IsSpecInstanceAt.ok (h : IsSpecInstanceAt s xas m mt I c₀) :
    ConfigOk c₀ [] ∧ I.WellFormed c₀.store :=
  Silmaril.Proofs.Wasm.Game.SpecInst.IsSpecInstanceAt.ok h

/-- **Adequacy of the specification's instantiation into an arbitrary store, every profile.**
The instantiation observations of the closed program are exactly the closed-world Core 3.0
behaviours of the configuration of `$instantiate` (segment initialisation, then the start
function). -/
theorem IsSpecInstanceAt.adequacy_inst (h : IsSpecInstanceAt s xas m mt I c₀) (P : Profile)
    (K : Env I.E) (hK : ThrowsBelow K I.store.exns.length) :
    instObs (I.closedSpec P c₀ K) = behavioursOf P (hostOf I.imports K) c₀ := by
  obtain ⟨hok, hw⟩ := h.ok
  have hK' : ThrowsBelow K c₀.store.exns.length := h.store_eq ▸ hK
  exact Silmaril.Proofs.Wasm.Game.Start.adequacy_instT (t₀ := configThread c₀) hw hok hK'

/-- **Adequacy of instantiate-then-invoke into an arbitrary store, every profile.** -/
theorem IsSpecInstanceAt.adequacy_after_inst (h : IsSpecInstanceAt s xas m mt I c₀)
    (P : Profile) (K : Env I.E) (hK : ThrowsBelow K I.store.exns.length) (f : I.F.Op) :
    obsAfterInst (I.closedSpec P c₀ K) f =
      {b | ∃ s', InstantiatesTo P (hostOf I.imports K) c₀ s' ∧
        b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1} := by
  obtain ⟨hok, hw⟩ := h.ok
  have hK' : ThrowsBelow K c₀.store.exns.length := h.store_eq ▸ hK
  exact Silmaril.Proofs.Wasm.Game.Start.adequacy_after_instT (t₀ := configThread c₀) hw hok hK' f

/-- **The stores the specification's instantiation returns at are well formed**, and the
environment still throws only existing exceptions there. -/
theorem IsSpecInstanceAt.instantiatesTo_wellFormed (h : IsSpecInstanceAt s xas m mt I c₀)
    {P : Profile} {K : Env I.E} (hK : ThrowsBelow K I.store.exns.length) {s' : Store Nat}
    (hs : InstantiatesTo P (hostOf I.imports K) c₀ s') :
    I.WellFormed s' ∧ ThrowsBelow K s'.exns.length := by
  obtain ⟨hok, hw⟩ := h.ok
  have hK' : ThrowsBelow K c₀.store.exns.length := h.store_eq ▸ hK
  exact Silmaril.Proofs.Wasm.Game.Start.startT_wellFormed (t₀ := configThread c₀) hw hok hK' hs

/-- **Instantiation results are typed**: a run of the specification's instantiation to a result
returns `values []`, traps or throws. -/
theorem IsSpecInstanceAt.result_cases (h : IsSpecInstanceAt s xas m mt I c₀) {P : Profile}
    {K : Env I.E} (hK : ThrowsBelow K I.store.exns.length) {c' : Config Nat} {r : Result}
    (run : Steps P (hostOf I.imports K) c₀ c') (final : c'.code = r.toAdmin) :
    r = .values [] ∨ r = .trap ∨ ∃ x, r = .throw x := by
  obtain ⟨hok, hw⟩ := h.ok
  have hK' : ThrowsBelow K c₀.store.exns.length := h.store_eq ▸ hK
  exact Silmaril.Proofs.Wasm.Game.Start.startT_result_cases (t₀ := configThread c₀) hw hok hK' run final

/-! ## Instances against fresh host functions -/

/-- A spec instance against fresh host functions is a spec instance at `importStore`. -/
theorem IsSpecInstance.toAt (h : IsSpecInstance m mt I c₀) :
    IsSpecInstanceAt (importStore (CExternType.funcs mt.imports)) (importAddrs mt) m mt I c₀ :=
  Silmaril.Proofs.Wasm.Game.SpecInst.IsSpecInstance.toAt h

/-- **The start phase is the specification's instantiation**: the configuration of a spec
instance is the configuration of `$instantiate`, for every profile and host. -/
theorem IsSpecInstance.instantiate (h : IsSpecInstance m mt I c₀) (P : Profile)
    (host : HostSemantics Nat) :
    Instantiate P host (importStore (CExternType.funcs mt.imports)) m (importAddrs mt) c₀ :=
  h.toAt.instantiate P host

/-- The store of a spec instance is the store of its configuration. -/
theorem IsSpecInstance.store_eq (h : IsSpecInstance m mt I c₀) : c₀.store = I.store :=
  h.toAt.store_eq

/-- **Spec instances are typed and well formed.** -/
theorem IsSpecInstance.ok (h : IsSpecInstance m mt I c₀) :
    ConfigOk c₀ [] ∧ I.WellFormed c₀.store :=
  h.toAt.ok

/-- **Adequacy of the specification's instantiation, every profile.** The instantiation
observations of the closed program are exactly the closed-world Core 3.0 behaviours of the
configuration of `$instantiate` (segment initialisation, then the start function). -/
theorem IsSpecInstance.adequacy_inst (h : IsSpecInstance m mt I c₀) (P : Profile)
    (K : Env I.E) (hK : ThrowsBelow K I.store.exns.length) :
    instObs (I.closedSpec P c₀ K) = behavioursOf P (hostOf I.imports K) c₀ :=
  h.toAt.adequacy_inst P K hK

/-- The stores the specification's instantiation returns at are well formed. -/
theorem IsSpecInstance.instantiatesTo_wellFormed (h : IsSpecInstance m mt I c₀) {P : Profile}
    {K : Env I.E} (hK : ThrowsBelow K I.store.exns.length) {s' : Store Nat}
    (hs : InstantiatesTo P (hostOf I.imports K) c₀ s') :
    I.WellFormed s' ∧ ThrowsBelow K s'.exns.length :=
  h.toAt.instantiatesTo_wellFormed hK hs

/-- **Adequacy of instantiate-then-invoke, every profile.** The observations of an export call
right after instantiation are its Core 3.0 behaviours at the stores that the specification's
instantiation run may return at. -/
theorem IsSpecInstance.adequacy_after_inst (h : IsSpecInstance m mt I c₀) (P : Profile)
    (K : Env I.E) (hK : ThrowsBelow K I.store.exns.length) (f : I.F.Op) :
    obsAfterInst (I.closedSpec P c₀ K) f =
      {b | ∃ s', InstantiatesTo P (hostOf I.imports K) c₀ s' ∧
        b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1} :=
  h.toAt.adequacy_after_inst P K hK f

/-! ## The instantiation outcomes -/

/-- **Instantiation succeeds exactly when the specification's instantiation run may return.** -/
theorem closedSpec_instReady_iff (P : Profile) (K : Env I.E) :
    (I.closedSpec P c₀ K).InstReady ↔
      ∃ s', InstantiatesTo P (hostOf I.imports K) c₀ s' := by
  refine (Silmaril.Proofs.Wasm.Game.Start.instReady_closedInstT_iff
    (t₀ := configThread c₀)).trans ?_
  constructor
  · rintro ⟨c', h₁, h₂⟩
    exact ⟨c'.store, c', h₁, h₂, rfl⟩
  · rintro ⟨_, c', h₁, h₂, -⟩
    exact ⟨c', h₁, h₂⟩

/-- **Instantiation diverges exactly when the specification's instantiation run diverges.** -/
theorem closedSpec_instDiverges_iff (P : Profile) (K : Env I.E) :
    (I.closedSpec P c₀ K).InstDiverges ↔ Diverges P (hostOf I.imports K) c₀ :=
  Silmaril.Proofs.Wasm.Game.Start.div_inst_iff (t₀ := configThread c₀) (s₀ := c₀.store)

/-- **Instantiation fails with `b` exactly when the specification's instantiation run may trap
or throw, read as `b`.** -/
theorem closedSpec_instFails_iff (P : Profile) (K : Env I.E) (b : Behaviour Val) :
    (I.closedSpec P c₀ K).InstFails b ↔
      ∃ (c' : Config Nat) (r : Result), Steps P (hostOf I.imports K) c₀ c' ∧
        c'.code = r.toAdmin ∧ (r = .trap ∨ ∃ x, r = .throw x) ∧ b = r.toBehaviour :=
  Silmaril.Proofs.Wasm.Game.Start.instFails_closedInstT_iff (t₀ := configThread c₀) b

end Silmaril.Wasm.Game

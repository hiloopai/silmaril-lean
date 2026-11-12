module

public import Silmaril.Wasm.Component.Lime1Ref.Defs
public import Silmaril.Wasm.Component.EngineRef.Defs

/-!
# The machine half for the Lime1 engine: the open engine facts

`Lime1Ref.RefToSpecELime1` asks that every behaviour of the reference component machine
over the Lime1 engine `lime1` be an outcome of the engine's own canonical-ABI specification
`exportSpecE lime1 Lime1G.lime1G.emb`, on the Lime1 domain `Lime1Dom`. The engine-generic
re-run of `refToSpec_of_arity` (`EngineRef.refToSpecE_of_facts`) reduces it to the
instantiation facts and the run facts of `lime1`. Most of these are proved
(`Silmaril.Wasm.Component.Lime1RefE.Thms`): relabelling host codes, preparation in the empty
store, export lookup by name, the absence of callouts, returned statuses and divergence. Two
facts are not, and they are the statements here.

* **`Lime1InstOk`** (open): the Lime1 engine instantiates the module of every component in
  the Lime1 domain whose Core module instantiates (`Simple.Inst`): `instOf lime1` succeeds. The
  machine half needs it: when it fails, `exportSpecE` is empty on well-typed arguments, while
  the machine's instantiation fails too (preparation commutes with relabelling the host codes,
  `Lime1RefE.prepare_relabel`), which is a trap behaviour. It is an instantiation
  correspondence (Core 3.0 instantiation succeeds ⇒ Lime1 preparation succeeds, on Lime1
  syntax), the converse direction of the copied `Lime1.Execution.prepare_core`.
* **`Lime1TypedOk`** (open): type soundness of the Lime1 engine for export calls. A returned
  run of export `k` of the instance on flat values of its parameter types returns values of its
  result types. The machine half needs typed results to lift them (`EngineRef.RunFacts.values`,
  as `Reference.run_results_typed` does over Core 3.0); there is no Lime1 type soundness theorem
  in the repository yet (Lime1 → 2.0 simulation exists, `Versions/Lime1/ToV2`, as does 2.0 type
  soundness, `Versions/V2/Soundness`, but not their composition at the instance level).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1RefE

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Lime1Ref
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)

/-- **Lime1 instantiation on the domain** (proved: `Lime1Eng.lime1Inst`). -/
def Lime1InstOk : Prop :=
  ∀ c : Simple, Lime1Dom c → c.Good → c.Inst →
    ∃ I : EInstance lime1,
      instOf lime1 (ofCoreL c.mod.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
        some I

/-- **Typed results of Lime1 export calls** (proved: `Lime1Eng.lime1Typed`). -/
def Lime1TypedOk : Prop :=
  ∀ c : Simple, Lime1Dom c → c.Good → c.Inst → ∀ I : EInstance lime1,
    instOf lime1 (ofCoreL c.mod.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some I →
    ∀ (k : Nat) (nm : String) (ft : CoreFuncTy), c.mod.exports[k]? = some (nm, ft) →
    ∀ a, I.addrs[k]? = some a → ∀ xs : List Flat, xs.map (·.type) = ft.params →
    ∀ (s' : lime1.Store Nat) (t' : lime1.Thread Nat) (ys : List Flat),
      Silmaril.Wasm.Component.Engine.CoreEngine.Steps lime1 (I.store, lime1.invoke a xs) (s', t') →
      lime1.status s' t' = .returned (.values ys) → ys.map (·.type) = ft.results

end Silmaril.Wasm.Component.Lime1RefE

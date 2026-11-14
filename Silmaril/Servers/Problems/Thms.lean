module

public import Silmaril.Problems.Basic
public import Silmaril.Servers.Problems.Defs
public import Silmaril.Servers.Examples.Dice.Thms
public import Silmaril.Servers.Tensor.Thms
public import Silmaril.Servers.WasiContext.Thms
public import Silmaril.Servers.WasiBinaries.Thms

/-!
# HTTP obligations of abstract servers: registered problems

Each problem is a `Prop` registered with `@[problem]`; a solution or refutation is a Lean
theorem (`@[solves]`, `@[refutes]`), checked at elaboration. Problems without a solution are
open.

| problem | shape | status |
| --- | --- | --- |
| `servers/dice/must-spec` | `MustUnder` all stateful hosts, any state type | solved |
| `servers/dice/may-six` | `MayUnder` all hosts | solved |
| `servers/dice/zero-host/may-six` | `May` under the zero host | refuted |
| `servers/dice/per-request/roll-const` | `Satisfies`, a fresh instance per request | solved |
| `servers/dice-buggy/must-spec` | `MustUnder` all stateful hosts | refuted (planted bug) |
| `servers/dice-buggy/zero-host/must-spec` | `MustUnder` the zero host | solved (the bug is invisible there) |
| `servers/tensor/shared-counter/not-isolated` | a shared-state server is no tensor | solved |
| `servers/context/http-equiv-of-ctx-equiv` | contextual equivalence gives HTTP equivalence | solved |
| `servers/wasi/http-equiv-of-host-equiv` | the same for `wasi:http` components and hosts | solved |
| `servers/wasi/hello-module/runs-body` | Lean typing: the core module runs its body over typed hosts | solved |
| `servers/wasi/route-module/runs-body` | the same for `route` (`WasiBinaries.Task.binRuns`) | open |
| `servers/wasi/hello/exports-handle` | the export *name* is `wasi:http/incoming-handler.handle` | solved, `nameMatch` only |

`catalogue` lists, for each problem and for each runtime check of `tests/servers/policies`, the
kind of evidence that backs it.
-/

@[expose] public section

namespace Silmaril.Servers.Problems

open Silmaril.Servers Silmaril.Servers.Observe Silmaril.Servers.Hosts
open Silmaril.Servers.Examples.Dice Silmaril.Servers.Context Silmaril.Servers.WasiContext
open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiCore
open Silmaril.Servers.WasiExamples Silmaril.Servers.WasiBinaries
open Silmaril.Net.Http (Request Response)

/-! ## The dice server -/

@[problem "servers/dice/must-spec"]
def diceMustSpec : Prop := ∀ σ : Type, Shape.MustUnder Set.univ (openDice 6 σ) spec

@[solves "servers/dice/must-spec"]
theorem diceMustSpec_solution : diceMustSpec := dice_mustAll

@[problem "servers/dice/may-six"]
def diceMaySix : Prop := Shape.MayUnder Set.univ (openDice 6 Unit) rollsSix

@[solves "servers/dice/may-six"]
theorem diceMaySix_solution : diceMaySix := dice_maySome_six

@[problem "servers/dice/zero-host/may-six"]
def diceZeroMaySix : Prop := (openDice 6 Unit zeroHost).May rollsSix

@[refutes "servers/dice/zero-host/may-six"]
theorem diceZeroMaySix_refuted : ¬ diceZeroMaySix := zero_not_maySix

@[problem "servers/dice/per-request/roll-const"]
def dicePerRequestConst : Prop := ∀ (σ : Type) (h : Stateful σ Unit UInt64),
  Shape.Satisfies (perRequest 6 h) (Sen.atomic (A := Http.sig) fun (r : Request) (s : Response) =>
    r.target.pathWithQuery = rollPath → s = rollResp (face 6 (h.step h.init ()).1))

@[solves "servers/dice/per-request/roll-const"]
theorem dicePerRequestConst_solution : dicePerRequestConst := fun _ h => perRequest_roll_const h

@[problem "servers/dice-buggy/must-spec"]
def buggyMustSpec : Prop := ∀ σ : Type, Shape.MustUnder Set.univ (openDice 7 σ) spec

@[refutes "servers/dice-buggy/must-spec"]
theorem buggyMustSpec_refuted : ¬ buggyMustSpec := fun h => buggy_not_mustAll (h Unit)

@[problem "servers/dice-buggy/zero-host/must-spec"]
def buggyZeroMustSpec : Prop := Shape.MustUnder {zeroHost} (openDice 7 Unit) spec

@[solves "servers/dice-buggy/zero-host/must-spec"]
theorem buggyZeroMustSpec_solution : buggyZeroMustSpec := buggy_mustAll_zero

/-! ## Independence -/

@[problem "servers/tensor/shared-counter/not-isolated"]
def sharedNotIsolated : Prop :=
  ∀ q₁ q₂ : Nat, Tensor.sharedCounter.Hist 0 ≠ (Machine.tensor Tensor.counter Tensor.counter).Hist (q₁, q₂)

@[solves "servers/tensor/shared-counter/not-isolated"]
theorem sharedNotIsolated_solution : sharedNotIsolated := Tensor.shared_not_tensor

/-! ## Contextual equivalence -/

@[problem "servers/context/http-equiv-of-ctx-equiv"]
def httpEquivOfCtxEquiv : Prop :=
  ∀ (L : Lang) (X : Type) (A : Sig) (ρ : Reading L X A) (c₁ c₂ : L.Comp),
    CtxEquivOn ρ.ctxs c₁ c₂ → EquivAt Set.univ (ρ.beh c₁) (ρ.beh c₂)

@[solves "servers/context/http-equiv-of-ctx-equiv"]
theorem httpEquivOfCtxEquiv_solution : httpEquivOfCtxEquiv :=
  fun _ _ _ ρ _ _ h => ρ.equivAt_of_ctxEquivOn h

@[problem "servers/wasi/http-equiv-of-host-equiv"]
def wasiHttpEquivOfHostEquiv : Prop :=
  ∀ (Y : Silmaril.Games.Sig.{0}) (X : Set FnName) (Hs : Set (Host Y proxyImports))
    (σ₁ σ₂ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)),
    HostEquivOn Hs σ₁ σ₂ → EquivAt Hs ((httpReading Y X).beh σ₁) ((httpReading Y X).beh σ₂)

@[solves "servers/wasi/http-equiv-of-host-equiv"]
theorem wasiHttpEquivOfHostEquiv_solution : wasiHttpEquivOfHostEquiv :=
  fun _ _ _ _ _ h => httpReading_equivAt h

/-! ## Component typing: three different claims -/

@[problem "servers/wasi/hello-module/runs-body"]
def helloModuleRunsBody : Prop := RunsTy (den helloCore) hello

@[solves "servers/wasi/hello-module/runs-body"]
theorem helloModuleRunsBody_solution : helloModuleRunsBody := hello_runsTy

/-- Open: one conjunct of `WasiBinaries.Task.binRuns`. -/
@[problem "servers/wasi/route-module/runs-body"]
def routeModuleRunsBody : Prop := RunsTy (den routeCore) route

/-- Only a name: the world exports a function called `wasi:http/incoming-handler.handle`. -/
@[problem "servers/wasi/hello/exports-handle"]
def helloExportsHandle : Prop := handleF ∈ proxyWorld.exports

@[solves "servers/wasi/hello/exports-handle"]
theorem helloExportsHandle_solution : helloExportsHandle := rfl

/-! ## Evidence catalogue -/

/-- **The kind of evidence behind each problem and each runtime check** (runtime check names are
those of `tests/servers/policies`; their records carry `"evidence": "runtime-test"`). -/
def catalogue : List (String × Evidence) :=
  [("servers/dice/must-spec", .proof),
   ("servers/dice/may-six", .proof),
   ("servers/dice/zero-host/may-six", .refutation),
   ("servers/dice/per-request/roll-const", .proof),
   ("servers/dice-buggy/must-spec", .refutation),
   ("servers/dice-buggy/zero-host/must-spec", .proof),
   ("servers/tensor/shared-counter/not-isolated", .proof),
   ("servers/context/http-equiv-of-ctx-equiv", .proof),
   ("servers/wasi/http-equiv-of-host-equiv", .proof),
   ("servers/wasi/hello-module/runs-body", .proof),
   ("servers/wasi/hello/exports-handle", .nameMatch),
   ("runtime/dice/{zero,seeded-1,seeded-42,chaos-7}/must", .runtimeTest),
   ("runtime/dice-buggy/chaos-7/must (expected failure)", .runtimeTest),
   ("runtime/{dice,dice-buggy}/*/replay", .runtimeTest),
   ("runtime/negative/core-module/wasm-tools-validate", .validatorCheck),
   ("runtime/negative/bad-handler/wasm-tools-validate", .validatorCheck),
   ("runtime/negative/bad-handler/component-targets", .validatorCheck),
   ("runtime/negative/bad-handler/wasmtime-serve", .runtimeTest),
   ("runtime/negative/start-trap/wasmtime-serve", .runtimeTest),
   ("runtime/negative/loop/timeout", .runtimeTest)]

end Silmaril.Servers.Problems

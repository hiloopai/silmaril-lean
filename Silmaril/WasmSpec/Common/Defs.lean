module

public import Silmaril.Wasm.Logic.Core.Defs
public import Silmaril.Wasm.Wat

/-!
# Wasm specification library: shared statement forms

Entries of the Wasm specification library (`docs/projects/wasm-binaryen-tooling.md`) state
what a function computes in one of two forms, both over silmaril-lean's Core 3
small-step semantics and Silmaril's weakest-precondition calculus
(`Silmaril.Wasm.Logic.Core`):

* `Computes fn args res`: the **body-level** form. The body of `fn`, entered in
  the frame a call builds (`Frame.forCall`) from the arguments `args`, in any
  store and module instance, for every profile and host relation, can run to
  the results `res` (and only falls through, branches to its own label or
  returns), leaving the store unchanged. This is what a solving mode proves.
* `FuncSpec` (from `Silmaril.Wasm.Logic.Core`): the **call-level** form, for the
  function stored at an address. `Computes.funcSpec`
  (`Silmaril.WasmSpec.Common.Thms`) turns the first into the second, so that other
  entries can call the function through `wp_call` using only its specification.

`Computes` is existential (`WP`): it promises one run to `res`, not that every
run ends there. In a deterministic profile the two coincide for these
programs. Entries may state every-run forms instead (`Silmaril.Wasm.Logic.Hoare`,
`Silmaril.Wasm.Logic.Total`); the manifest's `spec.runs`/`spec.correctness`
record which form an entry proves.
-/

@[expose] public section

namespace Silmaril.WasmSpec

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Core

/-- **Body-level specification.** The body of `fn`, called on `args`, can return
exactly `res` in any store, module instance, profile and host, without changing
the store. -/
def Computes (fn : Func) (args res : List Val) : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (s : Store H) (m : ModuleInst),
    WP P host s (Frame.forCall m args fn.locals) (expression fn.body)
      (funcPost P host res.length (fun s' r => s' = s ∧ r = res))

/-- **Call-level specification of a pure function.** The function at address `a`,
called in a store satisfying `Inv` on the arguments `argsOf x` for some input
`x`, returns `resOf x` without changing the store. -/
def PureSpec {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat)
    (Inv : Store H → Prop) {α : Type} (argsOf resOf : α → List Val) : Prop :=
  FuncSpec P host a (fun s args => Inv s ∧ ∃ x, args = argsOf x)
    (fun s args s' res => s' = s ∧ ∃ x, args = argsOf x ∧ res = resOf x)

end Silmaril.WasmSpec

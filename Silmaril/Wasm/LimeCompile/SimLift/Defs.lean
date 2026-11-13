module

public import Silmaril.Wasm.Binaryen.Equiv

/-!
# Lifting run transport to export refinement: definitions

A container compiler changes more than function code. It adds functions and types, changes data
instances, and replaces instructions by calls. silmaril-lean's module-level closure
(`exportRefines_of_bodiesRel`) fixes the store relation to "equal up to function code". Here the
store relation `S` is a parameter.

* `SessTransport P host S mi mi'`: what a session of export calls needs. The two instances export
  the same function addresses, `S`-related stores accept the same invocations of exported
  functions, and every finished or diverging invocation from `S`-related stores is matched,
  finished runs with `S`-related final stores.
* `InstTransport P host m m'`: every instantiation of `m` is matched by one of `m'` together
  with a store relation for which the instantiation run transports and `SessTransport` holds,
  and `m` instantiates whenever `m'` does.

`Silmaril.Wasm.LimeCompile.SimLift.exportRefines_of_instTransport` turns `InstTransport` into
`ExportRefines (· = ·)`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.SimLift

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (exportFunc?)

variable {H : Type}

/-- Runs from `S`-related configurations: a finished run on the left is matched by a finished
run on the right with the same result and `S`-related final stores. -/
def RunTransport (P : Profile) (host : HostSemantics H) (S : Store H → Store H → Prop)
    (c d : Config H) : Prop :=
  ∀ (c₁ : Config H) (r : Result), Steps P host c c₁ → c₁.code = r.toAdmin →
    ∃ d₁, Steps P host d d₁ ∧ d₁.code = r.toAdmin ∧ S c₁.store d₁.store

/-- What a session of export invocations needs from a store relation. -/
structure SessTransport (P : Profile) (host : HostSemantics H) (S : Store H → Store H → Prop)
    (mi mi' : ModuleInst) : Prop where
  /-- Both instances export the same function addresses. -/
  exports : ∀ x, exportFunc? mi' x = exportFunc? mi x
  /-- Related stores accept the same invocations of exported functions. -/
  invokeOk : ∀ {s t : Store H} {x : String} {a : Nat} {vs : List Val}, S s t →
    exportFunc? mi x = some a → (InvokeOk s a vs ↔ InvokeOk t a vs)
  /-- Finished invocations transport, with related final stores. -/
  run : ∀ {s t : Store H} {x : String} {a : Nat} {vs : List Val}, S s t →
    exportFunc? mi x = some a → InvokeOk s a vs → RunTransport P host S (invoke s a vs) (invoke t a vs)
  /-- Diverging invocations transport. -/
  diverges : ∀ {s t : Store H} {x : String} {a : Nat} {vs : List Val}, S s t →
    exportFunc? mi x = some a → InvokeOk s a vs → Diverges P host (invoke s a vs) →
      Diverges P host (invoke t a vs)

/-- Instantiation transport from `m` to `m'`. -/
structure InstTransport (P : Profile) (host : HostSemantics H) (m m' : Module) : Prop where
  /-- `m` instantiates whenever `m'` does. -/
  back : ∀ (s : Store H) xas d, StoreOk s → Instantiate P host s m' xas d →
    ∃ c, Instantiate P host s m xas c
  /-- Every instantiation of `m` is matched, with a store relation for the rest. -/
  fwd : ∀ (s : Store H) xas c, StoreOk s → Instantiate P host s m xas c →
    ∃ (d : Config H) (S : Store H → Store H → Prop), Instantiate P host s m' xas d ∧
      RunTransport P host S c d ∧ (Diverges P host c → Diverges P host d) ∧
      SessTransport P host S c.frame.module d.frame.module

end Silmaril.Wasm.LimeCompile.SimLift

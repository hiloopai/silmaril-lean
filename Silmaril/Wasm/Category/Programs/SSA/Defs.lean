module

public import Silmaril.Wasm.SSA.CoreCert.Thms
public import Silmaril.Compile.Category.Compiler
public import Silmaril.Compile.Category.Pass

@[expose] public section

/-!
# The lambda-SSA dialect as a Wasm language

* `ssaLang`: **the lambda-SSA dialect** of `Silmaril.Wasm.SSA` (`SFunc`: a lambda-SSA region over
  Wasm integer primitives) as a language of silmaril-lean's category of compilers. Interfaces
  are integer signatures; an observation is an argument list of the parameter types with the
  function's call outcome (`some o`, a return value or a trap) or `none` when it has none
  (it diverges or is stuck).
* `coreFnLang P`: **closed Core 3.0 function instances**: a store (closed host), an address and
  a signature; an observation is a typed argument list (`InvokeOk`) with a Core 3.0 behaviour
  of the invocation at profile `P` (`behaviours P closedHost`), divergence included.
* `ssaCoreConv P`: the convention between them: arguments as Core values, outcomes as
  behaviours (`outBeh`; `none` as divergence).
* `ssaToCoreRun`: the translation, `Silmaril.Wasm.SSA.compileCore?` (out of SSA, lowering,
  validation, executable instantiation and run-time checks), the function at address `0`.

Its soundness and the morphisms are in `Silmaril.Wasm.Category.Programs.SSA.Thms`. New.
-/

namespace Silmaril.Wasm.Category

open Silmaril.Compile.Category Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA

/-- Integer signatures: parameters and an optional result. -/
abbrev FragSig : Type := List IntType × Option IntType

/-- The observations of a lambda-SSA function: typed arguments with an outcome, or with none
exactly when there is none. -/
def ssaBeh (f : SFunc) : Set (List WVal × Option FOut) :=
  {p | p.1.map WVal.type = f.params ∧ (∀ o, p.2 = some o → f.Run p.1 o) ∧
    (p.2 = none → ∀ o, ¬ f.Run p.1 o)}

/-- **The lambda-SSA dialect** as a language. -/
def ssaLang : Language.{0} where
  Iface := FragSig
  Prog := SFunc
  iface f := (f.params, f.result)
  Obs := List WVal × Option FOut
  beh := ssaBeh

/-- A closed Core 3.0 function instance. -/
structure CoreFn where
  store : Store Empty
  addr : Nat
  sig : FragSig

/-- **Closed Core 3.0 function instances** at profile `P`. -/
noncomputable def coreFnLang (P : Numerics.Profile) : Language.{0} where
  Iface := FragSig
  Prog := CoreFn
  iface p := p.sig
  Obs := List Val × Behaviour Val
  beh p := {o | InvokeOk p.store p.addr o.1 ∧
    o.2 ∈ behaviours P Binaryen.closedHost p.store p.addr o.1}

/-- The convention: arguments as Core values, outcomes as behaviours. -/
def ssaCoreConv (P : Numerics.Profile) : Convention ssaLang (coreFnLang P) :=
  ⟨id, fun o o' => o'.1 = o.1.map WVal.toVal ∧ o'.2 = outBeh o.2⟩

/-- The translation: `compileCore?`, the function at address `0`. -/
def ssaToCoreRun (f : SFunc) : Option CoreFn :=
  (compileCore? f).map fun s => ⟨s, 0, (f.params, f.result)⟩

end Silmaril.Wasm.Category

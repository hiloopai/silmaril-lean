module

public import Silmaril.Wasm.SSA.Pipeline.Defs
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Binaryen.Typing

/-!
# Validated optimisation

The SSA optimiser does not prove that the code it emits is well typed. These
wrappers make validity hold by construction: they run silmaril's computable
module validator `Silmaril.Wasm.Validation.validate?` (sound for `ModuleOk`,
`validate_sound`) on the lowered module after the replacement and return the
optimised code only when it accepts.

* `optimizeFuncChecked m g`: optimise defined function `g` (relative index)
  of `m`; `some bf'` only if `m.setFunc g bf'` validates.
* `optimizeModuleChecked m`: optimise every function in the fragment, then
  keep the result only if the whole module validates, else return `m`.

The check costs a full module validation per call.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen

/-- Does the lowered module pass silmaril's validator? -/
def validates (m : BModule) : Bool := (Validation.validate? m.lower).isSome

/-- Optimise defined function `g` of `m`, keeping the result only if the module
with the replacement validates. -/
def optimizeFuncChecked (m : BModule) (g : Nat) : Option BFunc := do
  let bf ← m.funcs[g]?
  let bf' ← optimizeFuncIn? m bf
  if validates (m.setFunc g bf') then some bf' else none

/-- Optimise every function of `m` in the fragment; fall back to `m` if the result
does not validate. -/
def optimizeModuleChecked (m : BModule) : BModule :=
  let m' := optimizeModule m
  if validates m' then m' else m

end Silmaril.Wasm.SSA

module

public import Silmaril.Wasm.Auto2.Kernel.Defs
public import Silmaril.Wasm.Auto2.Calls.Defs

@[expose] public section

/-!
# The chunk checks of the function summaries over the kernel-cheap instance

`Silmaril.Wasm.Auto2.Summ.checkAmongU` (loops unrolled) and `Silmaril.Wasm.Auto2.Calls.checkAmongC`
(calls inlined) instantiate both modules with `Silmaril.Wasm.Verify.instance?`: in a certificate
every `chunkU`/`chunkC` theorem validated both modules again and initialised data segments byte
by byte, and `sumCheckU` compared memories with `decide` on byte arrays (`Array.isEqv`).

`checkAmongUK` and `checkAmongCK` are the same checks over `Silmaril.Wasm.Auto2.Kernel.instK?`
(no validation, closed-form data segments) with memories compared by `bytesEqL`; they equal the
specification checks once both modules are known to validate (`checkAmongU_eq_K`,
`checkAmongC_eq_K` in `Silmaril.Wasm.Auto2.KernelU.Thms`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Auto2.KernelU

open Silmaril.Wasm
open Silmaril.Wasm.Auto.Bridge (FnSumX usesMem)
open Silmaril.Wasm.Auto2.Summ (anyDead keys slots2)
open Silmaril.Wasm.Auto2.Kernel (instK? bytesEqL)

/-- `Silmaril.Wasm.Auto2.Summ.sumCheckU` with the memories compared by `bytesEqL`. -/
noncomputable def sumCheckUK : Option FnSumX → Option FnSumX → Bool
  | some A, some B =>
    A.params == B.params && decide (A.gvals = B.gvals) &&
      ((anyDead A.final.guards && anyDead B.final.guards) ||
        ((!(usesMem A.final || usesMem B.final) ||
            bytesEqL A.bytes.data.toList B.bytes.data.toList) &&
          (keys A.final.guards).all (keys B.final.guards).contains &&
          (keys B.final.guards).all (keys A.final.guards).contains &&
          decide (slots2 A.final.stack = slots2 B.final.stack)))
  | _, _ => false

/-- `Silmaril.Wasm.Auto2.Summ.checkAmongU` over `instK?`, with `sumCheckUK`. -/
noncomputable def checkAmongUK (fuel : Nat) (m₁ m₂ : Module) (js : List Nat) : List Bool :=
  match instK? m₁, instK? m₂ with
  | some I₁, some I₂ =>
    js.map fun j => sumCheckUK (Silmaril.Wasm.Auto2.Summ.fnSumUI fuel I₁ j)
      (Silmaril.Wasm.Auto2.Summ.fnSumUI fuel I₂ j)
  | _, _ => []

/-- `Silmaril.Wasm.Auto2.Calls.checkAmongC` over `instK?`, with `sumCheckUK`. -/
noncomputable def checkAmongCK (fuel : Nat) (m₁ m₂ : Module) (js : List Nat) : List Bool :=
  match instK? m₁, instK? m₂ with
  | some I₁, some I₂ =>
    js.map fun j => sumCheckUK (Silmaril.Wasm.Auto2.Calls.fnSumCI fuel I₁ j)
      (Silmaril.Wasm.Auto2.Calls.fnSumCI fuel I₂ j)
  | _, _ => []

end Silmaril.Wasm.Auto2.KernelU

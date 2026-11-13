module

public import Silmaril.Wasm.Auto2.Kernel.Defs

@[expose] public section

/-!
# Composing module equivalences: accepted arguments

`ModEquiv R P m₁ m₂ j` (`Silmaril.Wasm.Auto.Front`) relates the behaviours of export `j` of two
modules on the arguments that the *first* module's export accepts (`InvokeOk`). Two equivalences
therefore compose only when the middle module accepts the arguments the outer ones do
(`InvokeImp`). `sigOkK m₁ m₂ j` is a kernel-cheap sufficient condition (`invokeImp_of_sigOkK`,
`Silmaril.Wasm.Auto2.Link.Thms`): both instances (computed by the validation-free `instK?` of
`Silmaril.Wasm.Auto2.Kernel`) give export `j` a function of the same defined type, whose parameters
are number or vector types (whose values are typed independently of the store).

This is what lets a certificate about Binaryen's reading of a binary (`--wat`) be transferred to
the module silmaril-lean's decoder reads from the same binary when the two differ only in their
type sections (`wasm-check pass --link-equiv`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Auto2.Link

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Front (addrOf)
open Silmaril.Wasm.Verify (instOf)

/-- Export `j` of `m₂` accepts every argument list export `j` of `m₁` accepts. -/
def InvokeImp (m₁ m₂ : Module) (j : Nat) : Prop :=
  ∀ vs, InvokeOk (instOf m₁).store (addrOf m₁ j) vs → InvokeOk (instOf m₂).store (addrOf m₂ j) vs

/-- The defined type of the function implementing export `j`, from the validation-free
instance. -/
noncomputable def sigK (m : Module) (j : Nat) : Option DefType :=
  ((Silmaril.Wasm.Auto2.Kernel.instK? m).map fun I =>
    (I.store.funcs[I.addrs.getD j 0]?).map FuncInst.type).join

/-- The parameters of a defined function type are number or vector types. -/
def numParams (d : DefType) : Bool :=
  match d.expand? with
  | some (.func ps _) => ps.toList.all fun t => decide t.IsNumOrVec
  | _ => false

/-- **Same signature at export `j`**, with number or vector parameters. -/
noncomputable def sigOkK (m₁ m₂ : Module) (j : Nat) : Bool :=
  match sigK m₁ j, sigK m₂ j with
  | some d₁, some d₂ => decide (d₁ = d₂) && numParams d₁
  | _, _ => false

/-- `sigOkK` on several exports. -/
noncomputable def sigOkAll (m₁ m₂ : Module) (js : List Nat) : Bool :=
  js.all (sigOkK m₁ m₂)

end Silmaril.Wasm.Auto2.Link

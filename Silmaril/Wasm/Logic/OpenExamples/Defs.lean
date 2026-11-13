module

public import Silmaril.Wasm.Logic.Open.Thms
public import Silmaril.Wasm.Logic.HoareExamples.Thms

/-!
# Worked example for open modules: programs, specifications and modules

Two modules, checked in `Silmaril.Wasm.Logic.OpenExamples.Thms`:

* the **provider** `incMod a₁ fi₁`: one function at address `a₁` whose body is
  `incBody` (`local.get 0; i32.const 1; i32.add`); it imports nothing;
* the **client** `clientMod a₂ fi₂`: one function at address `a₂` whose body is
  `clientBody x` (`local.get 0; call x`), where the function index `x` resolves to
  an import stub (host code `h`) at address `b`, and `bind h = a₁`: the import is
  the provider's export.

`incSpec a₁ fi₁` (on an `i32` `m`, returns `m + 1` and leaves the store unchanged)
is the provider's export specification and the client's import specification;
`clientSpec` is the client's export specification.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.OpenExamples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare (Ctx FSpec)
open Silmaril.Wasm.Logic.Open (OMod)
open Silmaril.Wasm.Logic.HoareExamples (x0)

variable {H : Type}

/-- The provider's body: `local.get 0; i32.const 1; i32.add`. -/
def incBody : List Instr := [.localGet x0, .intConst .i32 1, .intBinOp .i32 .add]

/-- The client's body: `local.get 0; call x`. -/
def clientBody (x : FuncIdx) : List Instr := [.localGet x0, .call x]

/-- The module with the single function `fi` at address `a`. -/
def OMod.single (a : Nat) (fi : FuncInst H) : OMod H :=
  ⟨fun a' => if a' = a then some fi else none⟩

/-- The context with the single specification `S` at address `a`. -/
def ctxSingle (a : Nat) (S : FSpec H) : Ctx H := fun a' => if a' = a then some S else none

/-- The provider's specification: on an `i32` `m`, in a store holding the
function, return `m + 1` and leave the store unchanged. -/
def incSpec (a₁ : Nat) (fi₁ : FuncInst H) : FSpec H where
  pre s args := s.funcs[a₁]? = some fi₁ ∧ ∃ m : BitVec 32, args = [.i32 m]
  post s args s' o := s' = s ∧ ∃ m : BitVec 32, args = [.i32 m] ∧ o = .normal [.i32 (m + 1)]

/-- The client's specification: on an `i32` `m`, in a store holding the client,
the stub `fib` at `b` and the provider, return `m + 1` and leave the store
unchanged. -/
def clientSpec (a₂ : Nat) (fi₂ : FuncInst H) (b : Nat) (fib : FuncInst H) (a₁ : Nat)
    (fi₁ : FuncInst H) : FSpec H where
  pre s args := s.funcs[a₂]? = some fi₂ ∧ s.funcs[b]? = some fib ∧ s.funcs[a₁]? = some fi₁ ∧
    ∃ m : BitVec 32, args = [.i32 m]
  post s args s' o := s' = s ∧ ∃ m : BitVec 32, args = [.i32 m] ∧ o = .normal [.i32 (m + 1)]

end Silmaril.Wasm.Logic.OpenExamples

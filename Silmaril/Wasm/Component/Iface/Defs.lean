module

public import Silmaril.Wasm.Component.ABI.Defs
public import Silmaril.Games.Sig.Defs

/-!
# WIT-like interfaces and their game signatures

* `FuncTy`: a component function type (parameter and result value types);
  `CoreFuncTy`: a core (flat) function type. `FuncTy.flat` is its flattening
  by the canonical ABI.
* `Iface`: a WIT-like interface, a list of named component functions;
  `CoreIface`: the named functions a core module imports or exports.
* `Payload`: what crosses an interface — flat core values or component values.
* `sigN n`: the game signature of an interface with `n` functions. An
  operation is a function index together with its arguments; an answer is a
  result payload or a trap (`none`). `Iface.sig I = sigN I.length` and
  `CoreIface.sig`.
* `sigU`: the same with unbounded function indices, used inside components.

Arguments are *dynamically* typed: the signature does not depend on the
function types, only on their number. Type agreement is checked by the
canonical-ABI adapters (`Silmaril.Wasm.Component.Adapter`), which trap on
ill-typed payloads. This keeps every handler over these signatures simply
typed, which the component denotation and the passes rely on.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Wasm (NumType)
open Silmaril.Games

/-- A component-level function type. -/
structure FuncTy where
  /-- Parameter types. -/
  params : List ValTy
  /-- Result types. -/
  results : List ValTy
  deriving Repr, Inhabited, DecidableEq

/-- A core-level (flat) function type. -/
structure CoreFuncTy where
  /-- Parameter core types. -/
  params : List NumType
  /-- Result core types. -/
  results : List NumType
  deriving Repr, Inhabited, DecidableEq

/-- The flattening of a component function type (flat-only: no spilling to
memory). -/
def FuncTy.flat (ft : FuncTy) : CoreFuncTy :=
  ⟨ValTy.flatList ft.params, ValTy.flatList ft.results⟩

/-- A WIT-like interface: named component functions. -/
abbrev Iface := List (String × FuncTy)

/-- The named core functions of a core module interface. -/
abbrev CoreIface := List (String × CoreFuncTy)

/-- What crosses an interface: flat core values or component values. -/
inductive Payload where
  /-- Flat core values (core-level calls). -/
  | flat (xs : List Flat)
  /-- Component values (interface-level calls). -/
  | vals (vs : List Val)
  deriving Repr, BEq, Inhabited

/-- The game signature of an interface with `n` functions: call function `i`
with a payload; the answer is a payload, or `none` for a trap. -/
abbrev sigN (n : Nat) : Sig.{0} := ⟨Fin n × Payload, fun _ => Option Payload⟩

/-- Answers of `sigN`. -/
@[simp] theorem sigN_Ar (n : Nat) (q : (sigN n).Op) : (sigN n).Ar q = Option Payload := rfl

/-- The *universal* interface signature: call any function index with a
payload. Environments and component internals use it, so that their types do
not depend on the number of functions (which passes change); out-of-range
calls trap. `sigN n` is used at the boundaries (core modules, the imports and
exports of the outermost component). -/
abbrev sigU : Sig.{0} := ⟨Nat × Payload, fun _ => Option Payload⟩

/-- Answers of `sigU`. -/
@[simp] theorem sigU_Ar (q : sigU.Op) : sigU.Ar q = Option Payload := rfl

/-- The game signature of a WIT-like interface. -/
abbrev Iface.sig (I : Iface) : Sig.{0} := sigN I.length

/-- The game signature of a core interface. -/
abbrev CoreIface.sig (I : CoreIface) : Sig.{0} := sigN I.length

end Silmaril.Wasm.Component

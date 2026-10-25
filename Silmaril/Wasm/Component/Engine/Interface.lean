module

public import Silmaril.Wasm.Execution.Runtime

/-!
# The core-engine interface of the component runtime

The component runtime is parametric in the core WebAssembly language that runs the embedded
core modules. This file fixes the interface such a language must provide: a `CoreEngine`. Its
design:

* One engine store `Store H` is shared by all core instances of all component instances.
  Addresses are global, so composition is allocation into the same store. All component-level
  state (handle tables, tasks, waitables, threads) lives OUTSIDE this store.
* `H` is the type of host-code identifiers. The component runtime allocates one host function
  per lowering site (`canon lower`, canon builtins) with `allocHost`; canon host functions always
  have flat numeric signatures, so `allocHost` takes a `V1.FuncType` and stores
  `ofFlatType ft`.
* Core types are engine-provided (`FuncType`, `ExternType`, `ExternSub`), so that an abstract
  Core 3.0 engine can be typed with Core 3.0 extern types. `CoreExternType` below is the
  instance used by the V1 and Lime1 engines.
* Activations are store-free first-class `Thread` values. The store is threaded separately.
  A host callout is an observable `Status`, not a transition: the component scheduler decides
  when, and with which `CallResult`, to `resume` a parked thread. This is how the reference's
  `Thread.suspend`/`resume` (definitions.py L279-390, a25fc0b) and wasmtime's fiber suspension
  are represented, including non-LIFO interleavings.
* The engine exposes a relational, host-free step `Internal`; an executable stepper is an
  optional extra (`CoreEngine.Exec`, in `Engine/Laws.lean`).

Design note: `resume` also receives the engine store at which the callout is
resumed. A store-free resume cannot locate the callout redex of a Lime1 thread (the number of
arguments consumed is the arity of the stored host function type). Every law relating `resume`
to `status` is stated with that store.

What is NOT modelled here: evaluation contexts (`Lime1/Execution/Callout.lean` and
`V1/Execution/Callout.lean` provide them for Lime1/V1), concrete engines (Lime1, V1, Mock and
Core 3.0 are in their own files), and any law (see `Engine/Laws.lean`). Nothing about a particular
engine is claimed. -/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

/-- Flat core values at the canonical-ABI boundary: always i32/i64/f32/f64. -/
abbrev FlatValue := Silmaril.Wasm.Execution.Runtime.Value

/-- The outcome of a finished core activation. A core exception escaping to a canon boundary
is a trap (REF `call_and_trap_on_throw`, definitions.py at a25fc0b). -/
inductive CallResult where
  | values (vs : List FlatValue)
  | trap
  deriving DecidableEq, Repr

/-- The observable status of a core activation in a given store.

* `running`: the thread is not final and not parked; internal steps may exist (an engine is
  not required to report progress through this constructor).
* `returned r`: the activation is finished.
* `callout h args`: the activation is parked on a call of the host function with code `h`.
* `stuck`: no internal step, not returned, no callout (e.g. ill-typed code). This mirrors
  `Lime1.Execution.Status.stuck`. -/
inductive Status (H : Type) where
  | running
  | returned (r : CallResult)
  | callout (h : H) (args : List FlatValue)
  | stuck
  deriving DecidableEq, Repr

/-- Core extern types of the V1 and Lime1 engines (the `ExternType` of those instances).

`table` is a funcref table: the only table element type of V1/Lime1. `tag` is included so that
the same carrier can describe exception-tag imports of a module type; V1/Lime1 modules never
declare tags. Sizes are in the unit of the kind (table elements, memory pages). -/
inductive CoreExternType where
  | func (t : V1.FuncType)
  | table (addr : AddrType) (min : Nat) (max : Option Nat)
  | memory (addr : AddrType) (min : Nat) (max : Option Nat)
  | global (t : NumType) (mutable : Bool)
  | tag (t : V1.FuncType)
  deriving DecidableEq, Repr

/-- Core `limits_match` (Core 3.0 import matching of limits): the provided limits `(min, max)` match
the expected limits `(min', max')` when `min ≥ min'` and, if an expected maximum exists, a provided
maximum exists and is at most it. -/
def limitsMatch (min : Nat) (max : Option Nat) (min' : Nat) (max' : Option Nat) : Bool :=
  decide (min' ≤ min) &&
    match max' with
    | none => true
    | some m' =>
      match max with
      | none => false
      | some m => decide (m ≤ m')

/-- Boolean core extern subtyping `a <: b` for `CoreExternType`: functions and tags by equality,
tables and memories by equal address type and `limitsMatch`, globals by equal type and
mutability. Different kinds never match. -/
def CoreExternType.sub : CoreExternType → CoreExternType → Bool
  | .func t, .func t' => decide (t = t')
  | .table a n m, .table a' n' m' => decide (a = a') && limitsMatch n m n' m'
  | .memory a n m, .memory a' n' m' => decide (a = a') && limitsMatch n m n' m'
  | .global t mu, .global t' mu' => decide (t = t') && decide (mu = mu')
  | .tag t, .tag t' => decide (t = t')
  | _, _ => false

/-- Core extern subtyping `a <: b` (Core 3.0 import matching of external types). -/
def CoreExternType.Sub (a b : CoreExternType) : Prop := a.sub b = true

instance (a b : CoreExternType) : Decidable (a.Sub b) :=
  inferInstanceAs (Decidable (a.sub b = true))

theorem limitsMatch_refl (n : Nat) (m : Option Nat) : limitsMatch n m n m = true := by
  cases m <;> simp [limitsMatch]

theorem limitsMatch_trans {n₁ n₂ n₃ : Nat} {m₁ m₂ m₃ : Option Nat}
    (h₁ : limitsMatch n₁ m₁ n₂ m₂ = true) (h₂ : limitsMatch n₂ m₂ n₃ m₃ = true) :
    limitsMatch n₁ m₁ n₃ m₃ = true := by
  cases m₁ <;> cases m₂ <;> cases m₃ <;> simp_all [limitsMatch] <;> omega

theorem CoreExternType.Sub.refl (a : CoreExternType) : a.Sub a := by
  cases a <;> simp [Sub, sub, limitsMatch_refl]

theorem CoreExternType.Sub.trans {a b c : CoreExternType} (h₁ : a.Sub b) (h₂ : b.Sub c) :
    a.Sub c := by
  cases a <;> cases b <;> cases c <;> simp only [Sub, sub, Bool.and_eq_true,
    decide_eq_true_eq, Bool.false_eq_true] at h₁ h₂ ⊢
  all_goals first
    | exact h₁.trans h₂
    | exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
    | exact ⟨h₁.1.trans h₂.1, limitsMatch_trans h₁.2 h₂.2⟩

example : (CoreExternType.memory .i32 2 (some 4)).Sub (.memory .i32 1 (some 8)) := by decide
example : ¬ (CoreExternType.memory .i32 2 none).Sub (.memory .i32 1 (some 8)) := by decide
example : ¬ (CoreExternType.memory .i32 0 none).Sub (.memory .i32 1 none) := by decide
example : ¬ (CoreExternType.memory .i64 1 none).Sub (.memory .i32 1 none) := by decide
example : ¬ (CoreExternType.global (.int .i32) true).Sub (.global (.int .i32) false) := by decide

/-- A core engine: static module structure, one shared store per component store, addresses,
linear memories, funcref tables, and store-free activations with a host-free internal step. See the
module docstring. -/
structure CoreEngine where
  /-- Core modules. -/
  Module : Type
  /-- Module validity. -/
  Valid : Module → Prop
  /-- Core function types of this engine. -/
  FuncType : Type
  [decEqFuncType : DecidableEq FuncType]
  /-- Core extern types of this engine. -/
  ExternType : Type
  /-- Core extern subtyping `a <: b`. -/
  ExternSub : ExternType → ExternType → Prop
  /-- Embedding of flat numeric signatures (canon host functions). -/
  ofFlatType : V1.FuncType → FuncType
  /-- The flat numeric signature of a function type, if it has one. -/
  flatType? : FuncType → Option V1.FuncType
  /-- Imports of a module: module name, field name, expected type (positional order). -/
  importTypes : Module → List (String × String × ExternType)
  /-- Exports of a module and their types. -/
  exportTypes : Module → List (String × ExternType)
  /-- The shared engine store over host-code identifiers `H`. -/
  Store : Type → Type
  /-- The empty store. -/
  empty : (H : Type) → Store H
  FuncAddr : Type
  MemAddr : Type
  TableAddr : Type
  GlobalAddr : Type
  [decEqFuncAddr : DecidableEq FuncAddr]
  [decEqMemAddr : DecidableEq MemAddr]
  [decEqTableAddr : DecidableEq TableAddr]
  [decEqGlobalAddr : DecidableEq GlobalAddr]
  /-- External values (exports of instances, arguments of instantiation). -/
  ExternVal : Type
  asFunc? : ExternVal → Option FuncAddr
  asMemory? : ExternVal → Option MemAddr
  asTable? : ExternVal → Option TableAddr
  asGlobal? : ExternVal → Option GlobalAddr
  ofFunc : FuncAddr → ExternVal
  /-- Core module instances. -/
  Inst : Type
  exports : Inst → List (String × ExternVal)
  /-- The type of an external value in a store. -/
  externType? : {H : Type} → Store H → ExternVal → Option ExternType
  /-- Instantiation: allocation plus segment initialization, with positional imports. The
  start function is returned, not run: it runs as an activation under the scheduler. -/
  prepare? : {H : Type} → Store H → Module → List ExternVal →
    Option (Store H × Inst × Option FuncAddr)
  /-- Allocate a host function with a flat signature and host code `h`. -/
  allocHost : {H : Type} → Store H → V1.FuncType → H → Store H × FuncAddr
  funcType? : {H : Type} → Store H → FuncAddr → Option FuncType
  /-- Address type of a memory (`.i32` for V1/Lime1). -/
  memAddrType? : {H : Type} → Store H → MemAddr → Option AddrType
  /-- Memory size in bytes. -/
  memSize? : {H : Type} → Store H → MemAddr → Option Nat
  memRead? : {H : Type} → Store H → MemAddr → (start len : Nat) → Option ByteArray
  memWrite? : {H : Type} → Store H → MemAddr → (start : Nat) → ByteArray → Option (Store H)
  /-- Address type of a table. -/
  tableAddrType? : {H : Type} → Store H → TableAddr → Option AddrType
  /-- Funcref table read: `none` when out of bounds, `some none` for a null entry. -/
  tableFunc? : {H : Type} → Store H → TableAddr → Nat → Option (Option FuncAddr)
  /-- Store-free activations. -/
  Thread : Type → Type
  /-- A fresh activation calling a function with arguments. -/
  invoke : {H : Type} → FuncAddr → List FlatValue → Thread H
  status : {H : Type} → Store H → Thread H → Status H
  /-- Host-free step of a configuration. -/
  Internal : {H : Type} → Store H × Thread H → Store H × Thread H → Prop
  /-- Resume a parked activation with a host result, observed at the given store. -/
  resume : {H : Type} → Store H → Thread H → CallResult → Thread H

attribute [instance] CoreEngine.decEqFuncType CoreEngine.decEqFuncAddr CoreEngine.decEqMemAddr
  CoreEngine.decEqTableAddr CoreEngine.decEqGlobalAddr

/-- A core configuration: an engine store together with one activation. -/
abbrev CoreEngine.Config (E : CoreEngine) (H : Type) := E.Store H × E.Thread H

end Silmaril.Wasm.Component.Engine

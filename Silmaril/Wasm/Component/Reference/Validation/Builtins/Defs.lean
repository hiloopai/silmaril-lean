module

public import Silmaril.Wasm.Component.Reference.Validation.CanonOpts.Defs
import all Init.Data.String.Defs
import all Init.Data.Repr
import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Defs

/-!
# Validation of the canonical builtins

The static rules of the `canon` builtins (`CanonicalABI.md` §Canonical Definitions at
component-model `a25fc0b`,
https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/CanonicalABI.md,
sections `canon resource.new` ... `canon error-context.drop`), with the error texts and a few
check orders of wasmparser (`crates/wasmparser/src/validator/component.rs` in wasm-tools,
`resource_new` ... `thread_yield_then_promote`, `check_local_resource`).

## What is modelled

* `BuiltinOk feat V Γ b ft`: the builtin `b` is valid in context `Γ` under features `feat`
  and gets core type `ft` (a flat `V1.FuncType`, `A` the address type of the `memory` option,
  `i32` without one (D-g)):
  - `resource.new`/`resource.rep` require a **locally defined** resource: the type index
    names a resource variable `r` with `Γ.localRep? r = some rep` (a `resource` definition of
    this component). Imported resources and resources defined by a child instance
    (`definedRes` entry `none`) are rejected ("type {rt} is not a local resource"). Core types
    `[rep] → [i32]` / `[i32] → [rep]`. `resource.drop` needs any resource, `[i32] → []`.
  - 🔀 `backpressure.inc`/`.dec`, `task.cancel`: `[] → []`.
  - 🔀 `task.return (result t)? opts`: general option validation at site
    `.builtin .taskReturn` (only `memory`/`string-encoding`), the `lower` rules of the
    function type `(func (param "v" t)?)` (a parameter containing a list or string, or more
    than `MAX_FLAT_PARAMS` flat values, requires `memory`), and core type
    `flatten_functype(opts, (func (param t)?), 'lower')` (`CanonOpts.lowerCoreType`), as
    wasmparser's `task_return` computes it.
  - 🔀 `context.get t i` / `context.set t i`: `t` is `i32` (or `i64` with 🐘), `i < 2`, and
    `t` agrees with the component's fixed `contextType` (if any); the definition fixes it
    (`fixContext`). Core types `[] → [t]` / `[t] → []`.
  - 🔀 `subtask.cancel async?` (`[i32] → [i32]`; `async` needs 🚝), `subtask.drop`.
  - 🔀 `{stream,future}.new t` (`[] → [i64]`), `.cancel-{read,write} t async?`
    (`[i32] → [i32]`; `async` needs 🚝), `.drop-{readable,writable} t` (`[i32] → []`), and
    ➡️ (plus 🔀) `.forward t` (`[i32 i32] → []`): `t` must be a defined type of the form
    `(stream e?)` / `(future e?)`.
  - 🔀 `{stream,future}.{read,write} t opts` (`CopyOk`): general option validation at site
    `.builtin .copy`; without 🚝 `async` must be present; if the element type `e` is present,
    `memory` is required, and a `read` of an `e` containing a list or string (`containsPtr`)
    requires `realloc`. Core types `[i32 A A] → [A]` (stream), `[i32 A] → [i32]` (future).
  - 📝 `error-context.new opts` (`[A A] → [i32]`) and `.debug-message opts`
    (`[i32 A] → []`) (`ErrCtxOk`): general option validation, `memory` required, `realloc`
    required for `debug-message`, no `async`. `error-context.drop`: `[i32] → []`.
  - 🔀 `waitable-set.new` (`[] → [i32]`), `.wait mem`/`.poll mem` (`[i32 A] → [i32]`, `mem`
    a memory of address type `A`, `i64` needing 🐘), `.drop` (`[i32] → []`),
    `waitable.join` (`[i32 i32] → []`).
  - 🧵 `thread.index` (`[] → [i32]`), `thread.resume-later` (`[i32] → []`),
    `thread.suspend` (`[] → [i32]`), the four `thread.*-then-*` (`[i32] → [i32]`); 🔀
    `thread.yield` (`[] → [i32]`).
  - 🧵 `thread.new-indirect ft tbl`: core type `ft` is `(func (param T))` with `T` `i32` (or
    `i64` with 🐘), and `tbl` is a table whose element type matches `funcref`, with address
    type `U` (`i64` needing 🐘); core type `[U T] → [i32]`.
* `ValidBuiltin feat V Γ b x Γ'`: the relational judgement for the definition
  `(canon b (core func))`: `BuiltinOk feat V Γ b ft`, the pushed core function is
  `x = V.core.ofFlat ft`, and the context after the definition is `Γ' = fixContext Γ b`.
* `checkBuiltin?`, returning the pushed core function type and the updated context, with
  `checkBuiltin?_sound` (soundness, the acceptance criterion) and `checkBuiltin?_complete`;
  `builtinType?` computes the core type (`builtinType?_of_builtinOk`). The error message is
  computed separately (`explainBuiltin`) and never influences acceptance.

## Core views

Tables are not part of `CoreView`; `BuiltinView X` pairs a `CoreView X` with
`funcTable? : X → Option AddrType` (`some a` iff the extern type is a table whose element type
matches `funcref`, with address type `a`). `coreExternBuiltinView` is the V1/Lime1 instance
(`Engine.CoreExternType` tables are funcref-only). "Matches" is Wasm 3.0 reference subtyping
against `(ref null func)` (`Reftype_sub`), not table subtyping (which would demand an
equivalent element type and admit only `(ref null func)`). `wasmFuncrefTable?` decides it for a
source Core 3.0 `Silmaril.Wasm.TableType` (the test profile below): `(ref null? func)` and
`(ref null? nofunc)` match; a concrete `(ref null? $t)` is conservatively rejected, since a
module-relative type index cannot be resolved in the component context. The Core 3.0 profile
(`core3FuncTable?`, Validation/Defs.lean) works over closed table types and decides it exactly,
by `Sub.check {}` on the element type (so a closed concrete function type matches too).

## Deviations and choices

* **Spec over wasmparser.** Where the normative `CanonicalABI.md` and wasmparser differ, the
  former is followed: `context.{get,set}` accept `i = 1` without 🧵 (wasmparser demands the
  threading feature for `i > 0`); `thread.new-indirect` accepts `T = i64` and a 64-bit table
  with 🐘 (wasmparser accepts only `i32` and 32-bit tables), and a table whose element type
  matches `funcref` by reference subtyping, e.g. `(ref null nofunc)` or `(ref func)`
  (wasmparser checks table subtyping against `(table 0 funcref)`, i.e. an equivalent element
  type).
* **Core type index space.** The component-level core type space stores one `CoreTypeSlot`
  per member of a recursion group (Validation/Context.lean, DefTypes.lean), as in `Binary.md`
  and wasmparser, so `thread.new-indirect` requires `ft` to name a member whose body is the
  function type `(func (param T))`; finality and declared supertypes are not inspected (as in
  wasmparser's `thread_new_indirect`, which inspects only the composite type).
* **Gates.** The 🧵 builtins are gated by 🧵 alone and the 📝 builtins by 📝 alone (as in
  wasmparser); `.forward` needs 🔀 and ➡️. The `rep` of a resource is not re-checked against 🐘
  here (the `resource` type definition is validated with its rep).
* **`containsPtr`**, not REF `contains`: as in `Validation/CanonOpts.lean` (and wasmparser
  `contains_ptr`), a `stream`/`future` element that is itself a `stream`/`future` of strings needs
  no `realloc`.
* The context-type rule is stated against `Γ.contextType`, the type fixed by earlier
  `context.*` definitions of the same component; `fixContext` records it (equivalently
  `Ctx.setContextType?`, `fixContext_eq_setContextType?`).
* The 🧵② builtins (`thread.spawn-*`, `thread.available-parallelism`) are not in the syntax
  and not modelled.

## Error messages

Taken from wasmparser (`component.rs` at the vendored revision): the feature-gate texts
("`stream.read` requires the component model async feature", "synchronous `stream.read`
requires the component model more async builtins feature", "async `subtask.cancel` requires
the component model more async builtins feature", ...), "type {rt} is not a local resource",
"type index {rt} is not a resource type", "`stream.new` requires a stream type", "canonical
option `memory` is required", "canonical option `realloc` is required", "cannot specify
`async` option on `error-context.new`", "cannot specify `realloc` option on `task.return`",
"`context.get` type must match previous context type", "start function must take a single
`i32` argument (currently)", "start function must not return any values", "expected a core
function type", "start type must be a function", "`context.get` immediate must be zero or
one: {i}". Descriptive (not wasmparser's): "table is not a table of (ref null (func))", the
64-bit gate texts of `context.*`, `thread.new-indirect` and tables, and the fallback
"invalid canonical `{name}`". None of these is matched against the upstream corpus here.

## Tests (all kernel-checked, `decide +kernel`)

`resource.new`/`.rep` on an imported resource and on a child-instance resource rejected,
on a local resource accepted (and `resource.drop` accepted on the imported one);
`stream.read` without `async` and without 🚝 rejected, accepted with `async` or with 🚝;
`thread.new-indirect` with a non-funcref table rejected (a test profile whose tables are Core
3.0 `TableType`s), accepted with a funcref table, and with an `i64` start parameter only
under 🐘; plus: `stream.read` of `stream<string>` without `realloc`, `stream.write` of it
without `memory`, `stream.new` on a non-stream type, `error-context.debug-message` without
`realloc`, `error-context.new` with `async`, `context.get` type mismatch and `context.set`
fixing the type, 🚝 on `subtask.cancel`/`stream.cancel-read`, 🧵/🔀/➡️ gates,
`waitable-set.wait` on an `i64` memory, and the core type of `task.return`. Relational
corollaries: `not_validBuiltin_resourceNew_imported`, `not_validBuiltin_sync_streamRead`,
`not_validBuiltin_newIndirect_externref`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types

variable {X : Type}

/-! ## Core views with tables -/

/-- A `CoreView` together with the funcref-table view needed by `thread.new-indirect`. -/
structure BuiltinView (X : Type) where
  core : CoreView X
  /-- `some a` iff the extern type is a table with address type `a` whose element type
  matches `funcref`. -/
  funcTable? : X → Option AddrType

/-- The view for `Engine.CoreExternType` (V1/Lime1 profiles, funcref-only tables). -/
def coreExternBuiltinView : BuiltinView Engine.CoreExternType where
  core := coreExternView
  funcTable?
    | .table a _ _ => some a
    | _ => none

/-- A source Core 3.0 table type whose element type is a reference subtype of `(ref null func)`
(`(ref null? func)` or `(ref null? nofunc)`), with its address type. Concrete `(ref null? $t)`
elements are conservatively rejected (module-relative index); the Core 3.0 profile's
`core3FuncTable?` decides the same condition exactly on closed table types. -/
def wasmFuncrefTable? (tt : Silmaril.Wasm.TableType) : Option AddrType :=
  match tt.element.heap with
  | .abstract .func | .abstract .nofunc => some tt.address
  | _ => none

/-! ## Lookups used by the builtin rules -/

/-- The resource variable named by type index `rt`. -/
def resourceVar? (Γ : Ctx X) (rt : Nat) : Option Nat :=
  match Γ.type? rt with
  | some (.resource r) => some r
  | _ => none

/-- The representation of the **locally defined** resource named by type index `rt`
(wasmparser `check_local_resource`). -/
def localResRep? (Γ : Ctx X) (rt : Nat) : Option AddrType :=
  (resourceVar? Γ rt).bind Γ.localRep?

/-- The element type of the defined type `(stream e?)` named by `t`. -/
def streamElem? (Γ : Ctx X) (t : Nat) : Option (Option (Types.ValType Nat)) :=
  match Γ.type? t with
  | some (.val (.stream e)) => some e
  | _ => none

/-- The element type of the defined type `(future e?)` named by `t`. -/
def futureElem? (Γ : Ctx X) (t : Nat) : Option (Option (Types.ValType Nat)) :=
  match Γ.type? t with
  | some (.val (.future e)) => some e
  | _ => none

/-- The address type of memory `m`, if it is a memory. -/
def memAddrAt? (V : CoreView X) (Γ : Ctx X) (m : Nat) : Option AddrType :=
  (Γ.coreMem? m).bind V.memAddr?

/-- The parameter type `T` of a core type slot naming a recursion group member with body
`(func (param T))` (`T` `i32` or `i64`). -/
def startParam? (s : CoreTypeSlot X) : Option AddrType :=
  match s.funcType? with
  | some ⟨[.num (.int .i32)], []⟩ => some .i32
  | some ⟨[.num (.int .i64)], []⟩ => some .i64
  | _ => none

/-- The address type of table `tbl`, if it is a funcref table. -/
def funcTableAt? (V : BuiltinView X) (Γ : Ctx X) (tbl : Nat) : Option AddrType :=
  (Γ.coreTable? tbl).bind V.funcTable?

/-! ## Core types -/

/-- `i32` as a core value type. -/
abbrev nI32 : NumType := .int .i32

/-- `i64` as a core value type. -/
abbrev nI64 : NumType := .int .i64

/-- The flat pointer type `A` of an option list (`i32` without `memory`, D-g). -/
def optsPtr (V : CoreView X) (Γ : Ctx X) (opts : List Syntax.CanonOpt) : NumType :=
  ABI.pointerType (CanonOpts.ptrType V Γ opts)

/-- The function type `(func (param "v" t)?)` whose `lower` gives `task.return`'s core type. -/
def taskReturnFt (t : Option (Types.ValType Nat)) : Types.FuncType Nat :=
  { params := t.toList.map fun u => ("v", u), result := none }

/-- A function type with no parameters and results (the `ft` argument of `ValidCanonOpts` at
builtin sites, where it is irrelevant). -/
def emptyFt : Types.FuncType Nat := { params := [], result := none }

/-! ## Option-carrying builtins -/

open CanonOpts in
/-- `task.return (result t)? opts` for the resolved `t` (`CanonicalABI.md` §`canon
task.return`; wasmparser `task_return`): general option validation at the `task.return`
site, the `lower` rules of `(func (param "v" t)?)`, and the core type
`flatten_functype(opts, (func (param t)?), 'lower')`. -/
def TaskReturnOk (feat : Features) (V : CoreView X) (Γ : Ctx X) (opts : List Syntax.CanonOpt)
    (t : Option (Types.ValType Nat)) (ft : V1.FuncType) : Prop :=
  ValidCanonOpts feat V Γ (.builtin .taskReturn) (taskReturnFt t) opts ∧
  -- `lower(param)`: a result containing a list or string requires `memory`.
  (paramsNeedMemory (taskReturnFt t) = true → (memIdx? opts).isSome = true) ∧
  -- more than `MAX_FLAT_PARAMS` flat values require `memory`.
  (ABI.maxFlatParams < flatParamCount V Γ opts (taskReturnFt t) →
    (memIdx? opts).isSome = true) ∧
  ft = lowerCoreType V Γ opts (taskReturnFt t)

open CanonOpts in
/-- `{stream,future}.{read,write}` options for element type `e` (`CanonicalABI.md` §`canon
{stream,future}.{read,write}`). `read` selects the `lift(e)` rule. -/
def CopyOk (feat : Features) (V : CoreView X) (Γ : Ctx X) (read : Bool)
    (opts : List Syntax.CanonOpt) (e : Option (Types.ValType Nat)) : Prop :=
  ValidCanonOpts feat V Γ (.builtin .copy) emptyFt opts ∧
  -- 🚝: `async` may be omitted only with the feature.
  (hasAsync opts = false → feat.moreAsyncBuiltins = true) ∧
  -- an element type requires `memory`.
  (e.isSome = true → (memIdx? opts).isSome = true) ∧
  -- `lift(e)` on read: a list or string element requires `realloc`.
  (read = true → e.any containsPtr = true → (reallocIdx? opts).isSome = true)

open CanonOpts in
/-- `error-context.new` (`debug = false`) / `error-context.debug-message` (`debug = true`)
options: `memory` required, `realloc` required for `debug-message`, no `async`. -/
def ErrCtxOk (feat : Features) (V : CoreView X) (Γ : Ctx X) (debug : Bool)
    (opts : List Syntax.CanonOpt) : Prop :=
  ValidCanonOpts feat V Γ
    (.builtin (if debug then .errorContextDebugMessage else .errorContextNew)) emptyFt opts ∧
  (memIdx? opts).isSome = true ∧
  (debug = true → (reallocIdx? opts).isSome = true) ∧
  hasAsync opts = false

/-- `task.return (result r)? opts` with `r` resolved by `ResolveOpt`. -/
def TaskReturnResolved (feat : Features) (V : CoreView X) (Γ : Ctx X) (r : Option Syntax.VT)
    (opts : List Syntax.CanonOpt) (ft : V1.FuncType) : Prop :=
  ∃ t, ResolveOpt Γ r t ∧ TaskReturnOk feat V Γ opts t ft

instance (feat : Features) (V : CoreView X) (Γ : Ctx X) (opts : List Syntax.CanonOpt)
    (t : Option (Types.ValType Nat)) (ft : V1.FuncType) :
    Decidable (TaskReturnOk feat V Γ opts t ft) := by
  unfold TaskReturnOk; infer_instance

instance (feat : Features) (V : CoreView X) (Γ : Ctx X) (read : Bool)
    (opts : List Syntax.CanonOpt) (e : Option (Types.ValType Nat)) :
    Decidable (CopyOk feat V Γ read opts e) := by
  unfold CopyOk; infer_instance

instance (feat : Features) (V : CoreView X) (Γ : Ctx X) (debug : Bool)
    (opts : List Syntax.CanonOpt) : Decidable (ErrCtxOk feat V Γ debug opts) := by
  unfold ErrCtxOk; infer_instance

theorem taskReturnResolved_iff {feat : Features} {V : CoreView X} {Γ : Ctx X}
    {r : Option Syntax.VT} {opts : List Syntax.CanonOpt} {ft : V1.FuncType} :
    TaskReturnResolved feat V Γ r opts ft ↔
      match resolveOpt? Γ r with
      | .ok t => TaskReturnOk feat V Γ opts t ft
      | .error _ => False := by
  unfold TaskReturnResolved
  cases h : resolveOpt? Γ r with
  | error e =>
    simp only [iff_false, not_exists, not_and]
    intro t ht
    rw [← resolveOpt?_eq_ok, h] at ht
    cases ht
  | ok t =>
    simp only
    constructor
    · rintro ⟨t', ht', hok⟩
      rw [← resolveOpt?_eq_ok, h] at ht'
      cases ht'
      exact hok
    · intro hok
      exact ⟨t, resolveOpt?_eq_ok.1 h, hok⟩

instance (feat : Features) (V : CoreView X) (Γ : Ctx X) (r : Option Syntax.VT)
    (opts : List Syntax.CanonOpt) (ft : V1.FuncType) :
    Decidable (TaskReturnResolved feat V Γ r opts ft) :=
  have : Decidable (match resolveOpt? Γ r with
      | .ok t => TaskReturnOk feat V Γ opts t ft
      | .error _ => False) :=
    match resolveOpt? Γ r with
    | .ok t => inferInstanceAs (Decidable (TaskReturnOk feat V Γ opts t ft))
    | .error _ => isFalse id
  decidable_of_iff _ taskReturnResolved_iff.symm

/-! ## The builtin judgement (relational) -/

open CanonOpts in
/-- Validity of builtin `b` with core type `ft` (`CanonicalABI.md` §Canonical Definitions, the
"validation specifies" clauses). -/
def BuiltinOk (feat : Features) (V : BuiltinView X) (Γ : Ctx X) :
    Syntax.Builtin → V1.FuncType → Prop
  | .resourceNew rt, ft => OptSome (localResRep? Γ rt) fun rep =>
      ft = ⟨[ABI.pointerType rep], [nI32]⟩
  | .resourceDrop rt, ft => (resourceVar? Γ rt).isSome = true ∧ ft = ⟨[nI32], []⟩
  | .resourceRep rt, ft => OptSome (localResRep? Γ rt) fun rep =>
      ft = ⟨[nI32], [ABI.pointerType rep]⟩
  | .backpressureInc, ft | .backpressureDec, ft | .taskCancel, ft =>
      feat.async_ = true ∧ ft = ⟨[], []⟩
  | .taskReturn r opts, ft => feat.async_ = true ∧ TaskReturnResolved feat V.core Γ r opts ft
  | .contextGet a i, ft =>
      feat.async_ = true ∧ addrAllowed feat a = true ∧ i < 2 ∧
      OptAll Γ.contextType (· = a) ∧ ft = ⟨[], [ABI.pointerType a]⟩
  | .contextSet a i, ft =>
      feat.async_ = true ∧ addrAllowed feat a = true ∧ i < 2 ∧
      OptAll Γ.contextType (· = a) ∧ ft = ⟨[ABI.pointerType a], []⟩
  | .subtaskCancel as, ft =>
      feat.async_ = true ∧ (as = true → feat.moreAsyncBuiltins = true) ∧ ft = ⟨[nI32], [nI32]⟩
  | .subtaskDrop, ft => feat.async_ = true ∧ ft = ⟨[nI32], []⟩
  | .streamNew t, ft => feat.async_ = true ∧ (streamElem? Γ t).isSome = true ∧ ft = ⟨[], [nI64]⟩
  | .streamRead t opts, ft =>
      feat.async_ = true ∧ OptSome (streamElem? Γ t) (CopyOk feat V.core Γ true opts) ∧
      ft = ⟨[nI32, optsPtr V.core Γ opts, optsPtr V.core Γ opts], [optsPtr V.core Γ opts]⟩
  | .streamWrite t opts, ft =>
      feat.async_ = true ∧ OptSome (streamElem? Γ t) (CopyOk feat V.core Γ false opts) ∧
      ft = ⟨[nI32, optsPtr V.core Γ opts, optsPtr V.core Γ opts], [optsPtr V.core Γ opts]⟩
  | .streamCancelRead t as, ft | .streamCancelWrite t as, ft =>
      feat.async_ = true ∧ (as = true → feat.moreAsyncBuiltins = true) ∧
      (streamElem? Γ t).isSome = true ∧ ft = ⟨[nI32], [nI32]⟩
  | .streamDropReadable t, ft | .streamDropWritable t, ft =>
      feat.async_ = true ∧ (streamElem? Γ t).isSome = true ∧ ft = ⟨[nI32], []⟩
  | .streamForward t, ft =>
      feat.async_ = true ∧ feat.forward = true ∧ (streamElem? Γ t).isSome = true ∧
      ft = ⟨[nI32, nI32], []⟩
  | .futureNew t, ft => feat.async_ = true ∧ (futureElem? Γ t).isSome = true ∧ ft = ⟨[], [nI64]⟩
  | .futureRead t opts, ft =>
      feat.async_ = true ∧ OptSome (futureElem? Γ t) (CopyOk feat V.core Γ true opts) ∧
      ft = ⟨[nI32, optsPtr V.core Γ opts], [nI32]⟩
  | .futureWrite t opts, ft =>
      feat.async_ = true ∧ OptSome (futureElem? Γ t) (CopyOk feat V.core Γ false opts) ∧
      ft = ⟨[nI32, optsPtr V.core Γ opts], [nI32]⟩
  | .futureCancelRead t as, ft | .futureCancelWrite t as, ft =>
      feat.async_ = true ∧ (as = true → feat.moreAsyncBuiltins = true) ∧
      (futureElem? Γ t).isSome = true ∧ ft = ⟨[nI32], [nI32]⟩
  | .futureDropReadable t, ft | .futureDropWritable t, ft =>
      feat.async_ = true ∧ (futureElem? Γ t).isSome = true ∧ ft = ⟨[nI32], []⟩
  | .futureForward t, ft =>
      feat.async_ = true ∧ feat.forward = true ∧ (futureElem? Γ t).isSome = true ∧
      ft = ⟨[nI32, nI32], []⟩
  | .errorContextNew opts, ft =>
      feat.errorContext = true ∧ ErrCtxOk feat V.core Γ false opts ∧
      ft = ⟨[optsPtr V.core Γ opts, optsPtr V.core Γ opts], [nI32]⟩
  | .errorContextDebugMessage opts, ft =>
      feat.errorContext = true ∧ ErrCtxOk feat V.core Γ true opts ∧
      ft = ⟨[nI32, optsPtr V.core Γ opts], []⟩
  | .errorContextDrop, ft => feat.errorContext = true ∧ ft = ⟨[nI32], []⟩
  | .waitableSetNew, ft => feat.async_ = true ∧ ft = ⟨[], [nI32]⟩
  | .waitableSetWait m, ft | .waitableSetPoll m, ft =>
      feat.async_ = true ∧ OptSome (memAddrAt? V.core Γ m) fun a =>
        addrAllowed feat a = true ∧ ft = ⟨[nI32, ABI.pointerType a], [nI32]⟩
  | .waitableSetDrop, ft => feat.async_ = true ∧ ft = ⟨[nI32], []⟩
  | .waitableJoin, ft => feat.async_ = true ∧ ft = ⟨[nI32, nI32], []⟩
  | .threadIndex, ft | .threadSuspend, ft => feat.threads = true ∧ ft = ⟨[], [nI32]⟩
  | .threadNewIndirect ty tbl, ft =>
      feat.threads = true ∧
      OptSome ((Γ.coreType? ty).bind startParam?) fun c => addrAllowed feat c = true ∧
        OptSome (funcTableAt? V Γ tbl) fun u => addrAllowed feat u = true ∧
          ft = ⟨[ABI.pointerType u, ABI.pointerType c], [nI32]⟩
  | .threadResumeLater, ft => feat.threads = true ∧ ft = ⟨[nI32], []⟩
  | .threadYield, ft => feat.async_ = true ∧ ft = ⟨[], [nI32]⟩
  | .threadSuspendThenResume, ft | .threadYieldThenResume, ft
  | .threadSuspendThenPromote, ft | .threadYieldThenPromote, ft =>
      feat.threads = true ∧ ft = ⟨[nI32], [nI32]⟩

instance (feat : Features) (V : BuiltinView X) (Γ : Ctx X) (b : Syntax.Builtin)
    (ft : V1.FuncType) : Decidable (BuiltinOk feat V Γ b ft) := by
  cases b <;> dsimp only [BuiltinOk] <;> infer_instance

/-- The core value type used by `context.get`/`context.set`, if `b` is one. -/
def contextUse : Syntax.Builtin → Option AddrType
  | .contextGet a _ | .contextSet a _ => some a
  | _ => none

/-- The context after the definition of builtin `b`: `context.*` fixes `contextType`. -/
def fixContext (Γ : Ctx X) (b : Syntax.Builtin) : Ctx X :=
  match contextUse b with
  | some a => { Γ with contextType := some a }
  | none => Γ

/-- The judgement for `(canon b (core func))`: `b` is valid with core type `ft`, pushes the
core function `V.core.ofFlat ft`, and leaves context `fixContext Γ b`. -/
inductive ValidBuiltin (feat : Features) (V : BuiltinView X) (Γ : Ctx X) :
    Syntax.Builtin → X → Ctx X → Prop where
  | mk {b : Syntax.Builtin} {ft : V1.FuncType} (h : BuiltinOk feat V Γ b ft) :
      ValidBuiltin feat V Γ b (V.core.ofFlat ft) (fixContext Γ b)

/-! ## Executable core types and checker -/

open CanonOpts in
/-- The core type of builtin `b`, when its lookups succeed (mirrors `BuiltinOk`). -/
def builtinType? (V : BuiltinView X) (Γ : Ctx X) : Syntax.Builtin → Option V1.FuncType
  | .resourceNew rt => (localResRep? Γ rt).map fun rep => ⟨[ABI.pointerType rep], [nI32]⟩
  | .resourceDrop _ => some ⟨[nI32], []⟩
  | .resourceRep rt => (localResRep? Γ rt).map fun rep => ⟨[nI32], [ABI.pointerType rep]⟩
  | .backpressureInc | .backpressureDec | .taskCancel => some ⟨[], []⟩
  | .taskReturn r opts =>
    match resolveOpt? Γ r with
    | .ok t => some (lowerCoreType V.core Γ opts (taskReturnFt t))
    | .error _ => none
  | .contextGet a _ => some ⟨[], [ABI.pointerType a]⟩
  | .contextSet a _ => some ⟨[ABI.pointerType a], []⟩
  | .subtaskCancel _ => some ⟨[nI32], [nI32]⟩
  | .subtaskDrop => some ⟨[nI32], []⟩
  | .streamNew _ | .futureNew _ => some ⟨[], [nI64]⟩
  | .streamRead _ opts | .streamWrite _ opts =>
    some ⟨[nI32, optsPtr V.core Γ opts, optsPtr V.core Γ opts], [optsPtr V.core Γ opts]⟩
  | .futureRead _ opts | .futureWrite _ opts => some ⟨[nI32, optsPtr V.core Γ opts], [nI32]⟩
  | .streamCancelRead _ _ | .streamCancelWrite _ _
  | .futureCancelRead _ _ | .futureCancelWrite _ _ => some ⟨[nI32], [nI32]⟩
  | .streamDropReadable _ | .streamDropWritable _
  | .futureDropReadable _ | .futureDropWritable _ => some ⟨[nI32], []⟩
  | .streamForward _ | .futureForward _ => some ⟨[nI32, nI32], []⟩
  | .errorContextNew opts => some ⟨[optsPtr V.core Γ opts, optsPtr V.core Γ opts], [nI32]⟩
  | .errorContextDebugMessage opts => some ⟨[nI32, optsPtr V.core Γ opts], []⟩
  | .errorContextDrop => some ⟨[nI32], []⟩
  | .waitableSetNew => some ⟨[], [nI32]⟩
  | .waitableSetWait m | .waitableSetPoll m =>
    (memAddrAt? V.core Γ m).map fun a => ⟨[nI32, ABI.pointerType a], [nI32]⟩
  | .waitableSetDrop => some ⟨[nI32], []⟩
  | .waitableJoin => some ⟨[nI32, nI32], []⟩
  | .threadIndex | .threadSuspend | .threadYield => some ⟨[], [nI32]⟩
  | .threadNewIndirect ty tbl =>
    ((Γ.coreType? ty).bind startParam?).bind fun c =>
      (funcTableAt? V Γ tbl).map fun u => ⟨[ABI.pointerType u, ABI.pointerType c], [nI32]⟩
  | .threadResumeLater => some ⟨[nI32], []⟩
  | .threadSuspendThenResume | .threadYieldThenResume
  | .threadSuspendThenPromote | .threadYieldThenPromote => some ⟨[nI32], [nI32]⟩

/-! ## Error messages (never influence acceptance) -/

namespace BuiltinErr

/-- The builtin's name in wasmparser's messages. -/
def name : Syntax.Builtin → String
  | .resourceNew _ => "resource.new" | .resourceDrop _ => "resource.drop"
  | .resourceRep _ => "resource.rep" | .backpressureInc => "backpressure.inc"
  | .backpressureDec => "backpressure.dec" | .taskReturn _ _ => "task.return"
  | .taskCancel => "task.cancel" | .contextGet _ _ => "context.get"
  | .contextSet _ _ => "context.set" | .subtaskCancel _ => "subtask.cancel"
  | .subtaskDrop => "subtask.drop" | .streamNew _ => "stream.new"
  | .streamRead _ _ => "stream.read" | .streamWrite _ _ => "stream.write"
  | .streamCancelRead _ _ => "stream.cancel-read"
  | .streamCancelWrite _ _ => "stream.cancel-write"
  | .streamDropReadable _ => "stream.drop-readable"
  | .streamDropWritable _ => "stream.drop-writable" | .streamForward _ => "stream.forward"
  | .futureNew _ => "future.new" | .futureRead _ _ => "future.read"
  | .futureWrite _ _ => "future.write" | .futureCancelRead _ _ => "future.cancel-read"
  | .futureCancelWrite _ _ => "future.cancel-write"
  | .futureDropReadable _ => "future.drop-readable"
  | .futureDropWritable _ => "future.drop-writable" | .futureForward _ => "future.forward"
  | .errorContextNew _ => "error-context.new"
  | .errorContextDebugMessage _ => "error-context.debug-message"
  | .errorContextDrop => "error-context.drop" | .waitableSetNew => "waitable-set.new"
  | .waitableSetWait _ => "waitable-set.wait" | .waitableSetPoll _ => "waitable-set.poll"
  | .waitableSetDrop => "waitable-set.drop" | .waitableJoin => "waitable.join"
  | .threadIndex => "thread.index" | .threadNewIndirect _ _ => "thread.new-indirect"
  | .threadResumeLater => "thread.resume-later" | .threadSuspend => "thread.suspend"
  | .threadYield => "thread.yield"
  | .threadSuspendThenResume => "thread.suspend-then-resume"
  | .threadYieldThenResume => "thread.yield-then-resume"
  | .threadSuspendThenPromote => "thread.suspend-then-promote"
  | .threadYieldThenPromote => "thread.yield-then-promote"

/-- The feature gate of a builtin: wasmparser's message if the gate is off. -/
def gate (feat : Features) (b : Syntax.Builtin) : Option ValidationError :=
  let n := name b
  match b with
  | .resourceNew _ | .resourceDrop _ | .resourceRep _ => none
  | .errorContextNew _ | .errorContextDebugMessage _ | .errorContextDrop =>
    errIf (!feat.errorContext) s!"`{n}` requires the component model error-context feature"
  | .threadIndex | .threadNewIndirect _ _ | .threadResumeLater | .threadSuspend
  | .threadSuspendThenResume | .threadYieldThenResume | .threadSuspendThenPromote
  | .threadYieldThenPromote =>
    errIf (!feat.threads) s!"`{n}` requires the component model threading feature"
  | .streamForward _ | .futureForward _ =>
    match errIf (!feat.async_) s!"`{n}` requires the component model async feature" with
    | some e => some e
    | none => errIf (!feat.forward) s!"`{n}` requires the component model forward feature"
  | _ => errIf (!feat.async_) s!"`{n}` requires the component model async feature"

/-- Errors of a resource type index (wasmparser `resource_at`). -/
def resourceErr (Γ : Ctx X) (rt : Nat) : Option ValidationError :=
  match Γ.typeSlotAt? rt with
  | .error e => some e
  | .ok s => match s.def_ with
    | .resource _ => none
    | _ => some ⟨s!"type index {rt} is not a resource type"⟩

/-- Errors of a local resource type index (wasmparser `check_local_resource`). -/
def localErr (Γ : Ctx X) (rt : Nat) : List (Option ValidationError) :=
  [resourceErr Γ rt,
   errIf (localResRep? Γ rt).isNone s!"type {rt} is not a local resource"]

/-- Errors of a stream (`stream = true`) or future type index. -/
def streamFutureErr (Γ : Ctx X) (n : String) (stream : Bool) (t : Nat) :
    Option ValidationError :=
  match Γ.typeSlotAt? t with
  | .error e => some e
  | .ok s => match s.def_ with
    | .val _ =>
      if stream then errIf (streamElem? Γ t).isNone s!"`{n}` requires a stream type"
      else errIf (futureElem? Γ t).isNone s!"`{n}` requires a future type"
    | _ => some ⟨s!"type index {t} is not a defined type"⟩

/-- wasmparser's `require_memory`. -/
def memoryErr (opts : List Syntax.CanonOpt) (need : Bool) : Option ValidationError :=
  errIf (need && (CanonOpts.memIdx? opts).isNone) "canonical option `memory` is required"

/-- wasmparser's `require_realloc` (memory first). -/
def reallocErr (opts : List Syntax.CanonOpt) (need : Bool) : List (Option ValidationError) :=
  [memoryErr opts need,
   errIf (need && (CanonOpts.reallocIdx? opts).isNone) "canonical option `realloc` is required"]

/-- 🚝 errors of an `async?` immediate. -/
def asyncImmErr (feat : Features) (n : String) (as : Bool) : Option ValidationError :=
  errIf (as && !feat.moreAsyncBuiltins)
    s!"async `{n}` requires the component model more async builtins feature"

/-- Errors of the copy builtins. -/
def copyErr (feat : Features) (V : CoreView X) (Γ : Ctx X) (n : String) (stream read : Bool)
    (t : Nat) (opts : List Syntax.CanonOpt) : List (Option ValidationError) :=
  let e := ((if stream then streamElem? Γ t else futureElem? Γ t)).getD none
  [streamFutureErr Γ n stream t] ++ CanonOpts.optsErrors feat V Γ (.builtin .copy) emptyFt opts ++
  [errIf (!CanonOpts.hasAsync opts && !feat.moreAsyncBuiltins)
     s!"synchronous `{n}` requires the component model more async builtins feature",
   memoryErr opts e.isSome] ++ reallocErr opts (read && e.any containsPtr)

/-- Errors of the `error-context` option builtins. -/
def errCtxErr (feat : Features) (V : CoreView X) (Γ : Ctx X) (n : String) (debug : Bool)
    (opts : List Syntax.CanonOpt) : List (Option ValidationError) :=
  [errIf (CanonOpts.hasAsync opts) s!"cannot specify `async` option on `{n}`"] ++
  CanonOpts.optsErrors feat V Γ
    (.builtin (if debug then .errorContextDebugMessage else .errorContextNew)) emptyFt opts ++
  [memoryErr opts true] ++ reallocErr opts debug

/-- Errors of `context.get`/`context.set`. -/
def contextErr (feat : Features) (Γ : Ctx X) (n : String) (a : AddrType) (i : Nat) :
    List (Option ValidationError) :=
  [errIf (!addrAllowed feat a)
     s!"64-bit `{n}` requires the component model 64-bit feature",
   match Γ.contextType with
   | some t => errIf (t != a) s!"`{n}` type must match previous context type"
   | none => none,
   errIf (decide (2 ≤ i)) s!"`{n}` immediate must be zero or one: {i}"]

/-- Errors of `task.return`. -/
def taskReturnErr (feat : Features) (V : CoreView X) (Γ : Ctx X) (r : Option Syntax.VT)
    (opts : List Syntax.CanonOpt) : List (Option ValidationError) :=
  match resolveOpt? Γ r with
  | .error e => [some e]
  | .ok t =>
    let fty := taskReturnFt t
    [errIf (CanonOpts.reallocIdx? opts).isSome "cannot specify `realloc` option on `task.return`",
     errIf (CanonOpts.postReturnIdx? opts).isSome
       "cannot specify `post-return` option on `task.return`",
     errIf (CanonOpts.hasAsync opts) "cannot specify `async` option on `task.return`"] ++
    CanonOpts.optsErrors feat V Γ (.builtin .taskReturn) fty opts ++
    [memoryErr opts (CanonOpts.paramsNeedMemory fty ||
      decide (ABI.maxFlatParams < CanonOpts.flatParamCount V Γ opts fty))]

/-- Errors of a memory immediate (`waitable-set.wait`/`.poll`). -/
def memErr (feat : Features) (V : CoreView X) (Γ : Ctx X) (m : Nat) : Option ValidationError :=
  match Γ.coreMemAt? m with
  | .error e => some e
  | .ok x => match V.memAddr? x with
    | none => some ⟨"canonical option `memory` must be a memory"⟩
    | some a => errIf (!addrAllowed feat a)
        "64-bit memories require the component model memory64 feature"

/-- Errors of `thread.new-indirect`. -/
def newIndirectErr (feat : Features) (V : BuiltinView X) (Γ : Ctx X) (ty tbl : Nat) :
    List (Option ValidationError) :=
  [match Γ.coreTypeAt? ty with
   | .error e => some e
   | .ok (.module_ _) => some ⟨"expected a core function type"⟩
   | .ok s =>
     match s.funcType? with
     | some ⟨ps, rs⟩ =>
       if ps ≠ [.num (.int .i32)] ∧ ps ≠ [.num (.int .i64)] then
         some ⟨"start function must take a single `i32` argument (currently)"⟩
       else if rs ≠ [] then some ⟨"start function must not return any values"⟩
       else none
     | none => some ⟨"start type must be a function"⟩,
   match (Γ.coreType? ty).bind startParam? with
   | some c => errIf (!addrAllowed feat c)
       "64-bit `thread.new-indirect` requires the component model 64-bit feature"
   | none => none,
   match Γ.coreTableAt? tbl with
   | .error e => some e
   | .ok x => match V.funcTable? x with
     | none => some ⟨"table is not a table of (ref null (func))"⟩
     | some u => errIf (!addrAllowed feat u)
         "64-bit tables require the component model 64-bit feature"]

end BuiltinErr

open BuiltinErr in
/-- The error reported when builtin `b` is invalid. -/
def explainBuiltin (feat : Features) (V : BuiltinView X) (Γ : Ctx X) (b : Syntax.Builtin) :
    ValidationError :=
  let n := name b
  firstError ⟨s!"invalid canonical `{n}`"⟩ <| gate feat b :: match b with
  | .resourceNew rt | .resourceRep rt => localErr Γ rt
  | .resourceDrop rt => [resourceErr Γ rt]
  | .taskReturn r opts => taskReturnErr feat V.core Γ r opts
  | .contextGet a i | .contextSet a i => contextErr feat Γ n a i
  | .subtaskCancel as => [asyncImmErr feat n as]
  | .streamNew t | .streamDropReadable t | .streamDropWritable t | .streamForward t =>
    [streamFutureErr Γ n true t]
  | .futureNew t | .futureDropReadable t | .futureDropWritable t | .futureForward t =>
    [streamFutureErr Γ n false t]
  | .streamCancelRead t as | .streamCancelWrite t as =>
    [asyncImmErr feat n as, streamFutureErr Γ n true t]
  | .futureCancelRead t as | .futureCancelWrite t as =>
    [asyncImmErr feat n as, streamFutureErr Γ n false t]
  | .streamRead t opts => copyErr feat V.core Γ n true true t opts
  | .streamWrite t opts => copyErr feat V.core Γ n true false t opts
  | .futureRead t opts => copyErr feat V.core Γ n false true t opts
  | .futureWrite t opts => copyErr feat V.core Γ n false false t opts
  | .errorContextNew opts => errCtxErr feat V.core Γ n false opts
  | .errorContextDebugMessage opts => errCtxErr feat V.core Γ n true opts
  | .waitableSetWait m | .waitableSetPoll m => [memErr feat V.core Γ m]
  | .threadNewIndirect ty tbl => newIndirectErr feat V Γ ty tbl
  | _ => []

/-- Validate `(canon b (core func))`, returning the pushed core function type and the context
after the definition. Sound (`checkBuiltin?_sound`) and complete (`checkBuiltin?_complete`)
for `ValidBuiltin`. -/
def checkBuiltin? (feat : Features) (V : BuiltinView X) (Γ : Ctx X) (b : Syntax.Builtin) :
    Except ValidationError (X × Ctx X) :=
  match builtinType? V Γ b with
  | some ft =>
    if BuiltinOk feat V Γ b ft then .ok (V.core.ofFlat ft, fixContext Γ b)
    else .error (explainBuiltin feat V Γ b)
  | none => .error (explainBuiltin feat V Γ b)

/-! ## Soundness and completeness -/

/-! ## Tests -/

namespace BuiltinsTests

open Engine (CoreExternType)
open CanonOptsTests (okVal? canonErr?)

/-- `(func (param p))` as a singleton recursion group. -/
def startGroup (p : List Silmaril.Wasm.ValType) (r : List Silmaril.Wasm.ValType) :
    CoreTypeSlot X :=
  let g : Silmaril.Wasm.RecType := ⟨[⟨true, [], .func ⟨p, r⟩⟩]⟩
  .rec_ g 0 ((CoreTypeSlot.closeRec [] g).getD 0 default)

/-- The test context. Types: 0 an imported resource, 1 a resource defined by a child
instance, 2 a local resource (rep `i32`), 3 `stream<string>`, 4 `stream`, 5 `future<u32>`,
6 `u32`, 7 a local resource with rep `i64`. Memories 0 (`i32`), 1 (`i64`); core function 0
the `i32` realloc; core types 0 `(func (param i32))`, 1 `(func (param i64))`,
2 `(func (param i32) (result i32))`; table 0 (funcref). -/
def testCtx : Ctx CoreExternType :=
  { kind := .component
    coreMems := [.memory .i32 1 none, .memory .i64 1 none]
    coreFuncs := [.func (reallocType .i32)]
    coreTables := [.table .i32 0 none]
    coreTypes := [startGroup [.i32] [], startGroup [.i64] [], startGroup [.i32] [.i32]]
    types := [⟨.resource 0, 0⟩, ⟨.resource 1, 1⟩, ⟨.resource 2, 2⟩,
      ⟨.val (.stream (some (.prim .string))), 3⟩, ⟨.val (.stream none), 4⟩,
      ⟨.val (.future (some (.prim .u32))), 5⟩, ⟨.val (.prim .u32), 6⟩, ⟨.resource 3, 7⟩]
    importedRes := [(0, [0])]
    definedRes := [(1, none), (2, some .i32), (3, some .i64)] }

/-- Check under the P3 features (🔀 on; 🚝 📝 🧵 ➡️ 🐘 off). -/
def chkP3 (b : Syntax.Builtin) := checkBuiltin? Features.p3 coreExternBuiltinView testCtx b

/-- Check under `p3plus` (🚝 📝 🧵 ➡️ 🐘 on). -/
def chkPlus (b : Syntax.Builtin) := checkBuiltin? Features.p3plus coreExternBuiltinView testCtx b

/-- The pushed core function type of a successful check. -/
def ty? {α : Type} (r : Except ValidationError (α × Ctx CoreExternType)) : Option α :=
  (okVal? r).map (·.1)

/-! ### `resource.new` / `resource.rep` locality -/

/-! ### Stream/future copies and 🚝 -/

/-! ### Gates -/

/-! ### `error-context` -/

/-! ### `context.get` / `context.set` -/

/-! ### `task.return` and `waitable-set.wait` -/

/-! ### `thread.new-indirect` -/

/-- Extern types of a test profile whose tables are Core 3.0 table types (so that non-funcref
tables exist). -/
abbrev SumExtern := CoreExternType ⊕ Silmaril.Wasm.TableType

/-- Its view: memories and functions from `coreExternView`, tables by `wasmFuncrefTable?`. -/
def sumView : BuiltinView SumExtern where
  core :=
    { memAddr? := fun | .inl x => coreExternView.memAddr? x | .inr _ => none
      funcType? := fun | .inl x => coreExternView.funcType? x | .inr _ => none
      ofFlat := fun t => .inl (.func t) }
  funcTable? := fun
    | .inl x => coreExternBuiltinView.funcTable? x
    | .inr tt => wasmFuncrefTable? tt

/-- Table 0 `(table 0 externref)`, table 1 `(table 0 funcref)`; core types as in `testCtx`. -/
def sumCtx : Ctx SumExtern :=
  { kind := .component
    coreTypes := [startGroup [.i32] [], startGroup [.i64] [], startGroup [.i32] [.i32]]
    coreTables := [.inr ⟨.i32, ⟨0, none⟩, ⟨true, .abstract .extern⟩⟩,
      .inr ⟨.i32, ⟨0, none⟩, ⟨true, .abstract .func⟩⟩] }

def chkSum (feat : Features) (b : Syntax.Builtin) := checkBuiltin? feat sumView sumCtx b

end BuiltinsTests

end Silmaril.Wasm.Component.Validation

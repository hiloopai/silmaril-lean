module

public import Silmaril.Wasm.Component.Reference.Validation.Builtins.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Builtins.Defs

public import Silmaril.Raw.Wasm.Component.Validation.CanonOpts
import all Init.Data.String.Defs
import all Init.Data.Repr

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

/-! ## Lookups used by the builtin rules -/

/-! ## Core types -/

/-! ## Option-carrying builtins -/

/-! ## The builtin judgement (relational) -/

/-- For a valid builtin, `fixContext` agrees with `Ctx.setContextType?`. -/
theorem fixContext_eq_setContextType? {feat : Features} {V : BuiltinView X} {Γ : Ctx X}
    {b : Syntax.Builtin} {ft : V1.FuncType} {a : AddrType} (h : BuiltinOk feat V Γ b ft)
    (hb : contextUse b = some a) : Γ.setContextType? a = .ok (fixContext Γ b) := by
  have hctx : OptAll Γ.contextType (· = a) := by
    cases b <;> simp only [contextUse, reduceCtorEq, Option.some.injEq] at hb <;> subst hb <;>
      exact h.2.2.2.1
  unfold Ctx.setContextType? fixContext
  rw [hb]
  cases hc : Γ.contextType with
  | none => rfl
  | some t' =>
    rw [hc] at hctx
    simp only [OptAll] at hctx
    subst hctx
    simp only [↓reduceIte, Except.ok.injEq]
    cases Γ; simp_all

/-! ## Executable core types and checker -/

/-! ## Error messages (never influence acceptance) -/

namespace BuiltinErr

end BuiltinErr

/-! ## Soundness and completeness -/

/-- The core type of a valid builtin is the one `builtinType?` computes. -/
theorem builtinType?_of_builtinOk {feat : Features} {V : BuiltinView X} {Γ : Ctx X}
    {b : Syntax.Builtin} {ft : V1.FuncType} (h : BuiltinOk feat V Γ b ft) :
    builtinType? V Γ b = some ft := by
  cases b with
  | taskReturn r opts =>
    have h2 := taskReturnResolved_iff.1 h.2
    simp only [builtinType?]
    split at h2
    · rw [h2.2.2.2]
    · exact h2.elim
  | threadNewIndirect ty tbl =>
    obtain ⟨_, c, hc, _, u, hu, _, rfl⟩ := by simpa only [BuiltinOk, optSome_iff] using h
    simp only [builtinType?, hc, hu, Option.bind_some, Option.map_some]
  | resourceNew rt | resourceRep rt =>
    obtain ⟨a, ha, rfl⟩ := by simpa only [BuiltinOk, optSome_iff] using h
    simp only [builtinType?, ha, Option.map_some]
  | waitableSetWait m | waitableSetPoll m =>
    obtain ⟨_, a, ha, _, rfl⟩ := by simpa only [BuiltinOk, optSome_iff] using h
    simp only [builtinType?, ha, Option.map_some]
  | _ =>
    simp only [BuiltinOk, optSome_iff] at h
    simp only [builtinType?]
    simp_all

theorem checkBuiltin?_complete {feat : Features} {V : BuiltinView X} {Γ Γ' : Ctx X}
    {b : Syntax.Builtin} {x : X} (h : ValidBuiltin feat V Γ b x Γ') :
    checkBuiltin? feat V Γ b = .ok (x, Γ') := by
  cases h with
  | mk hok =>
    unfold checkBuiltin?
    rw [builtinType?_of_builtinOk hok]
    simp only [hok, ↓reduceIte]

theorem checkBuiltin?_iff {feat : Features} {V : BuiltinView X} {Γ Γ' : Ctx X}
    {b : Syntax.Builtin} {x : X} :
    checkBuiltin? feat V Γ b = .ok (x, Γ') ↔ ValidBuiltin feat V Γ b x Γ' :=
  ⟨checkBuiltin?_sound, checkBuiltin?_complete⟩

/-! ## Tests -/

namespace BuiltinsTests

open Engine (CoreExternType)
open CanonOptsTests (okVal? canonErr?)

/-! ### `resource.new` / `resource.rep` locality -/

/-- `resource.new` on an imported resource is rejected. -/
theorem test_resourceNew_imported :
    canonErr? (chkP3 (.resourceNew 0)) = some "type 0 is not a local resource" := by
  decide +kernel

theorem not_validBuiltin_resourceNew_imported (x : CoreExternType) (Γ' : Ctx CoreExternType) :
    ¬ ValidBuiltin Features.p3 coreExternBuiltinView testCtx (.resourceNew 0) x Γ' := fun h => by
  have hk : (okVal? (chkP3 (.resourceNew 0))).isNone = true := by decide +kernel
  simp [chkP3, checkBuiltin?_complete h, okVal?] at hk

theorem test_resource_locality :
    canonErr? (chkP3 (.resourceNew 1)) = some "type 1 is not a local resource" ∧
    canonErr? (chkP3 (.resourceRep 0)) = some "type 0 is not a local resource" ∧
    canonErr? (chkP3 (.resourceNew 6)) = some "type index 6 is not a resource type" ∧
    ty? (chkP3 (.resourceNew 2)) = some (.func ⟨[nI32], [nI32]⟩) ∧
    ty? (chkP3 (.resourceRep 2)) = some (.func ⟨[nI32], [nI32]⟩) ∧
    ty? (chkP3 (.resourceRep 7)) = some (.func ⟨[nI32], [nI64]⟩) ∧
    ty? (chkP3 (.resourceDrop 0)) = some (.func ⟨[nI32], []⟩) := by
  decide +kernel

/-! ### Stream/future copies and 🚝 -/

/-- `stream.read` without `async` and without 🚝 is rejected. -/
theorem test_sync_streamRead :
    canonErr? (chkP3 (.streamRead 4 [])) =
      some "synchronous `stream.read` requires the component model more async builtins \
        feature" := by
  decide +kernel

theorem not_validBuiltin_sync_streamRead (x : CoreExternType) (Γ' : Ctx CoreExternType) :
    ¬ ValidBuiltin Features.p3 coreExternBuiltinView testCtx (.streamRead 4 []) x Γ' :=
  fun h => by
    have hk : (okVal? (chkP3 (.streamRead 4 []))).isNone = true := by decide +kernel
    simp [chkP3, checkBuiltin?_complete h, okVal?] at hk

theorem test_streamRead_ok :
    ty? (chkP3 (.streamRead 4 [.async_])) = some (.func ⟨[nI32, nI32, nI32], [nI32]⟩) ∧
    ty? (chkPlus (.streamRead 4 [])) = some (.func ⟨[nI32, nI32, nI32], [nI32]⟩) ∧
    ty? (chkPlus (.streamRead 3 [.memory 0, .realloc 0])) =
      some (.func ⟨[nI32, nI32, nI32], [nI32]⟩) ∧
    ty? (chkPlus (.streamWrite 3 [.memory 1])) = some (.func ⟨[nI32, nI64, nI64], [nI64]⟩) ∧
    ty? (chkP3 (.futureRead 5 [.async_, .memory 0])) = some (.func ⟨[nI32, nI32], [nI32]⟩) := by
  decide +kernel

theorem test_copy_element_rules :
    canonErr? (chkPlus (.streamRead 3 [.memory 0])) =
      some "canonical option `realloc` is required" ∧
    canonErr? (chkPlus (.streamWrite 3 [])) = some "canonical option `memory` is required" ∧
    canonErr? (chkPlus (.futureWrite 5 [])) = some "canonical option `memory` is required" ∧
    canonErr? (chkPlus (.streamNew 5)) = some "`stream.new` requires a stream type" ∧
    canonErr? (chkPlus (.futureNew 6)) = some "`future.new` requires a future type" ∧
    canonErr? (chkPlus (.streamNew 2)) = some "type index 2 is not a defined type" := by
  decide +kernel

theorem test_async_immediates :
    canonErr? (chkP3 (.subtaskCancel true)) =
      some "async `subtask.cancel` requires the component model more async builtins feature" ∧
    ty? (chkPlus (.subtaskCancel true)) = some (.func ⟨[nI32], [nI32]⟩) ∧
    canonErr? (chkP3 (.streamCancelRead 4 true)) = some
      "async `stream.cancel-read` requires the component model more async builtins feature" ∧
    ty? (chkP3 (.futureCancelWrite 5 false)) = some (.func ⟨[nI32], [nI32]⟩) := by
  decide +kernel

/-! ### Gates -/

theorem test_gates :
    canonErr? (chkP3 (.threadIndex)) =
      some "`thread.index` requires the component model threading feature" ∧
    ty? (chkP3 .threadYield) = some (.func ⟨[], [nI32]⟩) ∧
    ty? (chkPlus .threadSuspendThenPromote) = some (.func ⟨[nI32], [nI32]⟩) ∧
    canonErr? (chkP3 (.streamForward 4)) =
      some "`stream.forward` requires the component model forward feature" ∧
    ty? (chkPlus (.futureForward 5)) = some (.func ⟨[nI32, nI32], []⟩) ∧
    canonErr? (checkBuiltin? Features.p2 coreExternBuiltinView testCtx .backpressureInc) =
      some "`backpressure.inc` requires the component model async feature" ∧
    canonErr? (chkP3 .errorContextDrop) =
      some "`error-context.drop` requires the component model error-context feature" ∧
    ty? (chkP3 (.streamNew 3)) = some (.func ⟨[], [nI64]⟩) := by
  decide +kernel

/-! ### `error-context` -/

theorem test_errorContext :
    canonErr? (chkPlus (.errorContextDebugMessage [.memory 0])) =
      some "canonical option `realloc` is required" ∧
    canonErr? (chkPlus (.errorContextNew [])) = some "canonical option `memory` is required" ∧
    canonErr? (chkPlus (.errorContextNew [.memory 0, .async_])) =
      some "cannot specify `async` option on `error-context.new`" ∧
    ty? (chkPlus (.errorContextNew [.memory 0])) = some (.func ⟨[nI32, nI32], [nI32]⟩) ∧
    ty? (chkPlus (.errorContextDebugMessage [.memory 0, .realloc 0])) =
      some (.func ⟨[nI32, nI32], []⟩) := by
  decide +kernel

/-! ### `context.get` / `context.set` -/

theorem test_context :
    (okVal? (chkP3 (.contextSet .i32 1))).map (·.2.contextType) = some (some .i32) ∧
    canonErr? (chkP3 (.contextGet .i64 0)) =
      some "64-bit `context.get` requires the component model 64-bit feature" ∧
    canonErr? (checkBuiltin? Features.p3plus coreExternBuiltinView
      { testCtx with contextType := some .i32 } (.contextGet .i64 0)) =
      some "`context.get` type must match previous context type" ∧
    canonErr? (chkP3 (.contextGet .i32 2)) =
      some "`context.get` immediate must be zero or one: 2" ∧
    ty? (chkPlus (.contextGet .i64 1)) = some (.func ⟨[], [nI64]⟩) := by
  decide +kernel

/-! ### `task.return` and `waitable-set.wait` -/

theorem test_taskReturn :
    ty? (chkP3 (.taskReturn none [])) = some (.func ⟨[], []⟩) ∧
    ty? (chkP3 (.taskReturn (some (.prim .string)) [.memory 0, .encoding .utf16])) =
      some (.func ⟨[nI32, nI32], []⟩) ∧
    canonErr? (chkP3 (.taskReturn (some (.prim .string)) [])) =
      some "canonical option `memory` is required" ∧
    canonErr? (chkP3 (.taskReturn (some (.prim .string)) [.memory 0, .realloc 0])) =
      some "cannot specify `realloc` option on `task.return`" ∧
    ty? (chkP3 (.taskReturn (some (.idx 6)) [])) = some (.func ⟨[nI32], []⟩) := by
  decide +kernel

theorem test_waitableSetWait :
    ty? (chkP3 (.waitableSetWait 0)) = some (.func ⟨[nI32, nI32], [nI32]⟩) ∧
    canonErr? (chkP3 (.waitableSetPoll 1)) =
      some "64-bit memories require the component model memory64 feature" ∧
    ty? (chkPlus (.waitableSetPoll 1)) = some (.func ⟨[nI32, nI64], [nI32]⟩) ∧
    canonErr? (chkP3 (.waitableSetWait 2)) =
      some "unknown memory 2: memory index out of bounds" := by
  decide +kernel

/-! ### `thread.new-indirect` -/

/-- `thread.new-indirect` with a non-funcref table is rejected. -/
theorem test_newIndirect_externref :
    canonErr? (chkSum Features.p3plus (.threadNewIndirect 0 0)) =
      some "table is not a table of (ref null (func))" := by
  decide +kernel

theorem not_validBuiltin_newIndirect_externref (x : SumExtern) (Γ' : Ctx SumExtern) :
    ¬ ValidBuiltin Features.p3plus sumView sumCtx (.threadNewIndirect 0 0) x Γ' := fun h => by
  have hk : (okVal? (chkSum Features.p3plus (.threadNewIndirect 0 0))).isNone = true := by
    decide +kernel
  simp [chkSum, checkBuiltin?_complete h, okVal?] at hk

theorem test_newIndirect :
    (okVal? (chkSum Features.p3plus (.threadNewIndirect 0 1))).map (·.1) =
      some (.inl (.func ⟨[nI32, nI32], [nI32]⟩)) ∧
    (okVal? (chkSum Features.p3plus (.threadNewIndirect 1 1))).map (·.1) =
      some (.inl (.func ⟨[nI32, nI64], [nI32]⟩)) ∧
    canonErr? (chkSum { Features.p3plus with memory64 := false } (.threadNewIndirect 1 1)) =
      some "64-bit `thread.new-indirect` requires the component model 64-bit feature" ∧
    canonErr? (chkSum Features.p3plus (.threadNewIndirect 2 1)) =
      some "start function must not return any values" ∧
    canonErr? (chkSum Features.p3 (.threadNewIndirect 0 1)) =
      some "`thread.new-indirect` requires the component model threading feature" ∧
    ty? (chkPlus (.threadNewIndirect 0 0)) = some (.func ⟨[nI32, nI32], [nI32]⟩) := by
  decide +kernel

end BuiltinsTests

end Silmaril.Wasm.Component.Validation

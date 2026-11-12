module

public import Silmaril.Wasm.Component.Reference.Validation.CanonOpts.Thms
public import Silmaril.Wasm.Component.Reference.Validation.CanonOpts.Defs

public import Silmaril.Raw.Wasm.Component.Validation.ValTypes
public import Silmaril.Wasm.Component.Engine.Interface
import all Init.Data.String.Defs
import all Init.Data.Repr

/-!
# Validation of canonical options and of `canon lift` / `canon lower`

The static rules of `CanonicalABI.md` §Canonical Definitions at component-model `a25fc0b`
(https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/CanonicalABI.md):
§`canonopt` Validation, §`canon lift` and §`canon lower`, with the core signatures of
`flatten_functype` (REF `definitions.py` lines 1769-1798, transcribed as `ABI.flattenFunc`).

## What is modelled

* `ValidCanonOpts feat V Γ dir ft opts`: general `canonopt` validation at a site
  `dir : OptsDir` (`lift`, `lower`, or the option-carrying builtins `builtin k`):
  - every option kind at most once (all string encodings are one kind);
  - each option is allowed at the site (`CanonOpts.allowed`): `post-return` and `callback` only on
    `canon lift`; `async` on lift, lower and the stream/future copies; `task.return` takes
    only `memory` and `string-encoding`;
  - `memory` is a core memory that is a subtype of `(memory 0)`, i.e. has address type
    `i32`, or `i64` with the 🐘 gate (`feat.memory64`);
  - `realloc` requires `memory` and has core type `(func (param A A A A) (result A))` with
    `A` the memory's address type;
  - `async` requires 🔀 and, on lift/lower, an `async` function type; it excludes
    `post-return`; a lift with `async` and no `callback` requires 🚟 (`feat.stackful`);
  - `callback` requires `async` and has core type `(func (param i32 i32 i32) (result i32))`.
* `LiftOk` / `LowerOk` and the judgement `ValidCanon feat V Γ c e` (`e : CanonEntity X` is
  the entity the definition pushes): the callee of a lift has core type
  `flatten_functype(opts, ft, 'lift')` and the lifted function gets type `ft`; `post-return`
  has params equal to the lifted core results and no results; `lift(param)` (a parameter
  containing a list or string, `containsPtr`) requires `realloc`; `lower(result)`
  requires `memory`; more than `MAX_FLAT_PARAMS` flat params require `realloc`; more flat
  results than `MAX_FLAT_RESULTS` (sync) or `MAX_FLAT_PARAMS` (async) require `memory`. A
  lower of `f : ft` pushes a core function of type `flatten_functype(opts, ft, 'lower')`
  (through the profile's `CoreView.ofFlat`); `lower(param)` requires `memory`,
  `lift(result)` requires `realloc`; more flat params than `max_flat_params` (16 sync, 4
  async) or flat results than `max_flat_results` (1 sync, 0 async; REF `canon_lower`) require
  `memory`. An `async` lower needs `memory` only through these rules (no `async` result, at
  most `MAX_FLAT_ASYNC_PARAMS` flat params, nothing containing a list or string needs none;
  see the deviation below).
* Executable checkers `checkCanonOpts?`, `checkLift?`, `checkLower?` (and the dispatcher
  `checkLiftLower?`), each deciding the relational conditions themselves:
  `checkCanonOpts?_iff`, `checkLift?_iff`, `checkLower?_iff` (soundness and completeness),
  with the soundness corollaries `checkCanonOpts?_sound`, `checkLift?_sound`,
  `checkLower?_sound`, `checkLiftLower?_sound`, and `checkLiftLower?_complete`
  (completeness of the dispatcher against `ValidCanon`). The error *message* is computed
  separately (`explainCanonOpts`,
  `explainLift`, `explainLower`) and never influences acceptance.

## Core types of the profile

`Ctx X` is parametric in the core extern type (Validation/Context.lean). The judgements take
a `CoreView X` telling which core extern types are memories (and their address type), the
flat `V1.FuncType` of a core function, and how to embed a flat signature as a core function
type (the `CoreEngine.ofFlatType`). `coreExternView` is the instance for
`Engine.CoreExternType` (V1/Lime1 profiles); `coreExternView_memAddr?_iff_sub` shows that its
memory condition is exactly `CoreExternType.Sub x (.memory a 0 none)` ("subtype of
`(memory 0)`"). The Core 3.0 profile's view, over closed extern types, is part of
`core3Profile` (`Validation/Defs.lean`).

## Deviations and choices

* (D-g) With no `memory` option, the pointer type used for flattening is `i32`
  (`CanonOpts.ptrType`); whenever the pointer type actually matters a `memory` is required,
  so this default is unobservable for valid definitions.
* The `async` feature gate is checked on the option itself (`asyncGate`) in addition to the 🔀 gate
  on `async` function types.
* The builtins' own option rules (e.g. `error-context.debug-message` needs `realloc`, stream
  copies need `async` without 🚝) are not here: `Validation/Builtins.lean` adds them on top of
  `ValidCanonOpts feat V Γ (.builtin k)`. `ValidCanon` has no builtin constructor; the
  per-definition judgement combines it with the builtin judgement of `Validation/Builtins.lean`.
* "`T` contains a `list` or `string`" is `containsPtr`, which, like wasmparser's
  `contains_ptr`, does not look inside `stream`/`future` payloads (they are `i32` handles
  and never touch the lifting/lowering memory); `ABI.containsListOrString` (REF
  `contains`) would recurse into them and reject e.g. a lift of `(param (stream string))`
  without `realloc`.
* `realloc` is allowed (and type-checked) at every site except `task.return`; whether
  wasmparser accepts it on `error-context.new` is not verified.
* `CanonicalABI.md` §`canon lower` "🔀 if `async` is specified, `memory` must be present" is
  not enforced: memory is required only when `flatten_functype`/`canon_lower` use it, as
  `Explainer.md` §Canonical ABI ("If the Canonical ABI needs to load or store, validation
  requires this option to be present"), wasmparser (`ComponentFuncType::lower`,
  `component_types.rs`) and the upstream tests (`test/async/cancel-targeted-resume.wast`,
  `test/async/reentrance.wast` lower `async func()` without `memory`) do. See `LowerOk`.

## Error messages

Only the substrings matched by the upstream corpus are claimed to be wasmparser's
(`test/validation/abi.wast`, `test/async/validate-no-async-abi-for-sync-type.wast`):
"canonical option `memory` is required", "canonical option `realloc` is required",
"canonical option `realloc` requires `memory` to also be specified",
"canonical encoding option `utf8` conflicts with option `utf16`" (and the other pairs),
"`memory` is specified more than once", "canonical option `realloc` is specified more than
once", "canonical option `post-return` is specified more than once",
"canonical option `realloc` uses a core function with an incorrect signature",
"canonical option `post-return` uses a core function with an incorrect signature",
"canonical option `post-return` cannot be specified for lowerings",
"lowered parameter types `[]` do not match parameter types `[I32]`" (and the result form),
"not a function type", "memory index out of bounds" and "the `async` canonical option
requires an async function type". All other texts (callback signature, callback without
async, async with post-return, stackful, memory64, feature gates) are descriptive.

## Tests (all kernel-checked, `decide +kernel`)

Mirrored (not replayed from the `.wast` files):
`validate-no-async-abi-for-sync-type.wast` (all three cases: async lift, async lift with
callback, async lower of a sync function type); `abi.wast`: lower of a large result without
`memory`, `realloc` without `memory`, superfluous `realloc` accepted, memory index out of
bounds, list param lift without `memory`, two-value result lift without `memory`, list param
lower without `memory`, list param lift without `realloc`, 20-param lift without `realloc`,
string result lower without `realloc`, string encodings accepted on lift and lower,
conflicting encodings (three pairs), duplicate `memory`/`realloc`/`post-return`, `realloc`
and `post-return` with a wrong signature, `post-return` on a lowering, core signature
mismatch on params and on results, and a lift at a non-function type. Additionally: a
callback of the wrong core type, `callback` without `async`, `async` with `post-return`,
stackless `async` lift without 🚟, `i64` memory with and without 🐘, and the core type pushed
by lowerings (sync spill, async), and a `stream<string>` param lift / `future<list<u8>>`
result lower accepted without options (`containsPtr`). Relational corollaries
`not_validCanon_async_sync_lift`,
`not_validCanon_string_param_no_realloc`, `not_validCanon_bad_callback`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types

variable {X : Type}

/-! ## Sites and option kinds -/

namespace CanonOpts

end CanonOpts

/-! ## Core types of the profile -/

/-- `coreExternView`'s memory condition is "subtype of `(memory a 0)`". -/
theorem coreExternView_memAddr?_iff_sub (x : Engine.CoreExternType) (a : AddrType) :
    coreExternView.memAddr? x = some a ↔ x.Sub (.memory a 0 none) := by
  cases x <;> simp [coreExternView, Engine.CoreExternType.Sub, Engine.CoreExternType.sub,
    Engine.limitsMatch, eq_comm]

namespace CanonOpts

variable (V : CoreView X) (Γ : Ctx X) (opts : List Syntax.CanonOpt)

end CanonOpts

/-! ## Option-valued quantifiers (decidable) -/

theorem OptAll.of_some {α : Type} {o : Option α} {P : α → Prop} {a : α} (h : OptAll o P)
    (ho : o = some a) : P a := by
  subst ho; exact h

theorem optSome_iff {α : Type} {o : Option α} {P : α → Prop} :
    OptSome o P ↔ ∃ a, o = some a ∧ P a := by
  cases o <;> simp [OptSome]

/-! ## General `canonopt` validation (relational) -/

/-! ## `canon lift` and `canon lower` (relational) -/

/-! ## Types whose flat representation points into linear memory -/

namespace CanonOpts

variable (V : CoreView X) (Γ : Ctx X) (opts : List Syntax.CanonOpt) (ft : Types.FuncType Nat)

end CanonOpts

open CanonOpts in
-- FLAG(statement-change): async lower no longer requires memory unconditionally (Explainer.md
-- §Canonical ABI, definitions.py flatten_functype/canon_lower; CanonicalABI.md §`canon lower`
-- "if `async` is specified, `memory` must be present" not followed; wasmparser
-- component_types.rs `ComponentFuncType::lower`).
open CanonOpts in
/-- When an `async` lower is valid without `memory`: exactly when nothing contains a list or
string, there are at most `MAX_FLAT_ASYNC_PARAMS` flat params and no result (REF
`flatten_functype` L1793-1797, `canon_lower` L2181-2182; wasmparser
`ComponentFuncType::lower`). `CanonicalABI.md` §`canon lower`'s blanket "🔀 if `async` is
specified, `memory` must be present" is not modelled (see `LowerOk`). -/
theorem lowerOk_async_noMemory_iff {feat : Features} {V : CoreView X} {Γ : Ctx X}
    {opts : List Syntax.CanonOpt} {ft : Types.FuncType Nat}
    (ha : hasAsync opts = true) (hm : memIdx? opts = none) :
    LowerOk feat V Γ opts ft ↔ ValidCanonOpts feat V Γ .lower ft opts ∧
      paramsNeedMemory ft = false ∧ resultNeedsMemory ft = false ∧
      flatParamCount V Γ opts ft ≤ ABI.maxFlatAsyncParams ∧
      flatResultCount V Γ opts ft = 0 := by
  have hm' : (memIdx? opts).isSome = false := by simp [hm]
  constructor
  · intro h
    refine ⟨h.validOpts, ?_, ?_, ?_, ?_⟩
    · cases hp : paramsNeedMemory ft
      · rfl
      · have := h.paramsMemory hp
        simp [hm'] at this
    · cases hr : resultNeedsMemory ft
      · rfl
      · obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (h.resultRealloc hr)
        have := (h.validOpts.realloc.of_some hf).1
        simp [hm'] at this
    · refine Nat.le_of_not_lt fun hlt => ?_
      have := h.spillParams (by simpa [lowerMaxFlatParams, ha] using hlt)
      simp [hm'] at this
    · refine Nat.eq_zero_of_not_pos fun hlt => ?_
      have := h.spillResults (by simpa [lowerMaxFlatResults, ha] using hlt)
      simp [hm'] at this
  · rintro ⟨hv, hp, hr, hpc, hrc⟩
    refine ⟨hv, ?_, ?_, ?_, ?_⟩
    · intro h; simp [hp] at h
    · intro h; simp [hr] at h
    · intro h; simp [lowerMaxFlatParams, ha] at h; omega
    · intro h; simp [lowerMaxFlatResults, ha] at h; omega

/-! ## Error messages (never influence acceptance) -/

namespace CanonOpts

variable (feat : Features) (V : CoreView X) (Γ : Ctx X) (dir : OptsDir)
  (ft : Types.FuncType Nat) (opts : List Syntax.CanonOpt)

end CanonOpts

/-! ## Checkers -/

/-! ## Soundness and completeness -/

theorem checkCanonOpts?_iff {feat : Features} {V : CoreView X} {Γ : Ctx X} {dir : OptsDir}
    {ft : Types.FuncType Nat} {opts : List Syntax.CanonOpt} :
    checkCanonOpts? feat V Γ dir ft opts = .ok () ↔ ValidCanonOpts feat V Γ dir ft opts := by
  unfold checkCanonOpts?
  split <;> simp_all

theorem checkCanonOpts?_sound {feat : Features} {V : CoreView X} {Γ : Ctx X} {dir : OptsDir}
    {ft : Types.FuncType Nat} {opts : List Syntax.CanonOpt}
    (h : checkCanonOpts? feat V Γ dir ft opts = .ok ()) : ValidCanonOpts feat V Γ dir ft opts :=
  checkCanonOpts?_iff.1 h

private theorem type?_of_typeSlotAt? {Γ : Ctx X} {t : Nat} {s : TypeSlot X}
    (h : Γ.typeSlotAt? t = .ok s) : Γ.type? t = some s.def_ := by
  have h' : Γ.types[t]? = some s := Ctx.listAt?_eq_ok.1 h
  simp [Ctx.type?, h']

theorem checkLiftLower?_complete {feat : Features} {V : CoreView X} {Γ : Ctx X}
    {c : Syntax.Canon} {e : CanonEntity X} (h : ValidCanon feat V Γ c e) :
    checkLiftLower? feat V Γ c = .ok e := by
  cases h with
  | lift hty hok =>
    simp only [checkLiftLower?, checkLift?_iff.2 ⟨hty, hok⟩, Except.map]
  | lower hty hok =>
    simp only [checkLiftLower?, checkLower?_iff.2 ⟨_, hty, hok, rfl⟩, Except.map]

/-! ## Tests -/

namespace CanonOptsTests

open Engine (CoreExternType)

/-! ### `validate-no-async-abi-for-sync-type.wast` -/

theorem test_async_lift_sync_type :
    canonErr? (liftP3 0 [.async_] 0) =
      some "the `async` canonical option requires an async function type" := by decide +kernel

theorem test_async_callback_lift_sync_type :
    canonErr? (liftP3 4 [.async_, .callback 2] 0) =
      some "the `async` canonical option requires an async function type" := by decide +kernel

theorem test_async_lower_sync_type :
    canonErr? (lowerP3 0 [.async_]) =
      some "the `async` canonical option requires an async function type" := by decide +kernel

/-- Relational form of the first case: no validity derivation exists. -/
theorem not_validCanon_async_sync_lift (e : CanonEntity CoreExternType) :
    ¬ ValidCanon Features.p3 coreExternView testCanonCtx (.lift 0 [.async_] 0) e := fun h => by
  have hk : (okVal? (checkLiftLower? Features.p3 coreExternView testCanonCtx
    (.lift 0 [.async_] 0))).isNone = true := by decide +kernel
  simp [checkLiftLower?_complete h, okVal?] at hk

/-! ### `abi.wast` -/

theorem test_lower_big_result_no_memory :
    canonErr? (lowerP3 1 []) = some "canonical option `memory` is required" := by decide +kernel

theorem test_lower_realloc_without_memory :
    canonErr? (lowerP3 1 [.realloc 1]) =
      some "canonical option `realloc` requires `memory` to also be specified" := by
  decide +kernel

theorem test_lower_big_result_ok :
    okVal? (lowerP3 1 [.memory 0]) = some (.func ⟨[i32t], []⟩) ∧
    okVal? (lowerP3 1 [.memory 0, .realloc 1]) = some (.func ⟨[i32t], []⟩) := by decide +kernel

theorem test_memory_oob :
    canonErr? (lowerP3 0 [.memory 2]) = some "unknown memory 2: memory index out of bounds" := by
  decide +kernel

theorem test_lift_list_param_no_memory :
    canonErr? (liftP3 3 [] 2) = some "canonical option `memory` is required" := by decide +kernel

theorem test_lift_pair_result_no_memory :
    canonErr? (liftP3 5 [] 5) = some "canonical option `memory` is required" := by decide +kernel

theorem test_lower_list_param_no_memory :
    canonErr? (lowerP3 2 []) = some "canonical option `memory` is required" := by decide +kernel

theorem test_lift_list_param_no_realloc :
    canonErr? (liftP3 3 [.memory 0] 2) = some "canonical option `realloc` is required" := by
  decide +kernel

/-- A string parameter lifted without `realloc` is rejected. -/
theorem test_lift_string_param_no_realloc :
    canonErr? (liftP3 3 [.memory 0] 3) = some "canonical option `realloc` is required" := by
  decide +kernel

theorem not_validCanon_string_param_no_realloc (e : CanonEntity CoreExternType) :
    ¬ ValidCanon Features.p3 coreExternView testCanonCtx (.lift 3 [.memory 0] 3) e := fun h => by
  have hk : (okVal? (checkLiftLower? Features.p3 coreExternView testCanonCtx
    (.lift 3 [.memory 0] 3))).isNone = true := by decide +kernel
  simp [checkLiftLower?_complete h, okVal?] at hk

/-- `stream`/`future` payloads do not require `memory`/`realloc` (wasmparser `contains_ptr`):
a lift of `(param (stream string))` and a lower of `(result (future (list u8)))` need no
options. -/
theorem test_stream_future_payload_no_options :
    okVal? (liftP3 6 [] 9) = some streamParamFt ∧
    okVal? (lowerP3 6 []) = some (.func ⟨[], [i32t]⟩) := by decide +kernel

theorem test_lift_twenty_params_no_realloc :
    canonErr? (liftP3 6 [.memory 0] 6) = some "canonical option `realloc` is required" := by
  decide +kernel

theorem test_lower_string_result_no_realloc :
    canonErr? (lowerP3 3 [.memory 0]) = some "canonical option `realloc` is required" := by
  decide +kernel

theorem test_string_encodings_ok :
    (∀ e ∈ [ABI.StringEncoding.utf8, .utf16, .latin1Utf16],
      okVal? (lowerP3 4 [.encoding e, .memory 0, .realloc 1]) =
        some (.func ⟨[i32t, i32t], []⟩)) ∧
    (∀ e ∈ [ABI.StringEncoding.utf8, .utf16, .latin1Utf16],
      okVal? (liftP3 3 [.encoding e, .memory 0, .realloc 1] 3) = some stringParamFt) := by
  decide +kernel

theorem test_encoding_conflicts :
    canonErr? (lowerP3 0 [.encoding .utf8, .encoding .utf16]) =
      some "canonical encoding option `utf8` conflicts with option `utf16`" ∧
    canonErr? (lowerP3 0 [.encoding .utf8, .encoding .latin1Utf16]) =
      some "canonical encoding option `utf8` conflicts with option `latin1-utf16`" ∧
    canonErr? (lowerP3 0 [.encoding .utf16, .encoding .latin1Utf16]) =
      some "canonical encoding option `utf16` conflicts with option `latin1-utf16`" := by
  decide +kernel

theorem test_duplicate_options :
    canonErr? (lowerP3 0 [.memory 0, .memory 0]) =
      some "canonical option `memory` is specified more than once" ∧
    canonErr? (liftP3 3 [.memory 0, .realloc 1, .realloc 1] 2) =
      some "canonical option `realloc` is specified more than once" ∧
    canonErr? (liftP3 5 [.memory 0, .realloc 1, .postReturn 7, .postReturn 7] 4) =
      some "canonical option `post-return` is specified more than once" := by
  decide +kernel

theorem test_bad_realloc :
    canonErr? (liftP3 3 [.memory 0, .realloc 8] 2) =
      some "canonical option `realloc` uses a core function with an incorrect signature" := by
  decide +kernel

theorem test_bad_post_return :
    canonErr? (liftP3 5 [.memory 0, .realloc 1, .postReturn 0] 4) =
      some "canonical option `post-return` uses a core function with an incorrect signature" ∧
    okVal? (liftP3 5 [.memory 0, .realloc 1, .postReturn 7] 4) = some stringResultFt := by
  decide +kernel

theorem test_post_return_lowering :
    canonErr? (lowerP3 4 [.memory 0, .realloc 1, .postReturn 7]) =
      some "canonical option `post-return` cannot be specified for lowerings" := by
  decide +kernel

theorem test_core_signature_mismatch :
    canonErr? (liftP3 6 [] 0) =
      some "lowered parameter types `[]` do not match parameter types `[I32]`" ∧
    canonErr? (liftP3 5 [] 0) =
      some "lowered result types `[]` do not match result types `[I32]`" := by
  decide +kernel

theorem test_lift_not_func_type :
    canonErr? (liftP3 0 [] 8) = some "type index 8 is not a function type" ∧
    canonErr? (liftP3 0 [] 10) = some "unknown type 10: type index out of bounds" := by
  decide +kernel

/-! ### Callback and async rules -/

/-- A callback of the wrong core type is rejected. -/
theorem test_bad_callback :
    canonErr? (liftP3 4 [.async_, .callback 9] 7) =
      some "canonical option `callback` uses a core function with an incorrect signature" := by
  decide +kernel

theorem not_validCanon_bad_callback (e : CanonEntity CoreExternType) :
    ¬ ValidCanon Features.p3 coreExternView testCanonCtx (.lift 4 [.async_, .callback 9] 7) e :=
  fun h => by
    have hk : (okVal? (checkLiftLower? Features.p3 coreExternView testCanonCtx
      (.lift 4 [.async_, .callback 9] 7))).isNone = true := by decide +kernel
    simp [checkLiftLower?_complete h, okVal?] at hk

theorem test_async_callback_lift_ok :
    okVal? (liftP3 4 [.async_, .callback 2] 7) = some asyncParamFt := by decide +kernel

theorem test_callback_without_async :
    canonErr? (liftP3 0 [.callback 2] 0) = some "canonical option `callback` requires `async`" := by
  decide +kernel

theorem test_callback_on_lower :
    canonErr? (lowerP3 5 [.memory 0, .async_, .callback 2]) =
      some "canonical option `callback` is not allowed here" := by decide +kernel

theorem test_async_post_return :
    canonErr? (liftP3 4 [.async_, .callback 2, .postReturn 6] 7) =
      some "cannot specify post-return function in async" := by decide +kernel

/-- Stackless async lift without `callback` needs 🚟. -/
theorem test_async_lift_stackful :
    canonErr? (liftP3 10 [.async_] 7) =
      some "async lift without `callback` requires the component model async stackful feature" ∧
    okVal? (checkLift? Features.p3plus coreExternView testCanonCtx 10 [.async_] 7) =
      some asyncParamFt := by
  decide +kernel

theorem test_async_lower :
    canonErr? (lowerP3 5 [.async_]) = some "canonical option `memory` is required" ∧
    okVal? (lowerP3 5 [.async_, .memory 0]) = some (.func ⟨[i32t, i32t], [i32t]⟩) := by
  decide +kernel

/-! ### When an `async` lower needs `memory`

Only when the lowering loads or stores (`LowerOk`; REF `flatten_functype` L1793-1797,
`canon_lower` L2181-2182; wasmparser `ComponentFuncType::lower`). The cases agree with
wasm-tools 1.259.0 and wasmtime 49.0.1. -/

/-- `async` lowers needing no memory: `async func()` (upstream
`test/async/cancel-targeted-resume.wast` lowers `park` so), 4 flat `u32` params, a
`stream<string>` param (an `i32` handle), a fixed-length `list<u8, 4>` (4 flat params), and
`string-encoding` alone; an unneeded `memory` is still accepted. -/
theorem test_async_lower_no_memory :
    okVal? (lowerP3 7 [.async_]) = some (.func ⟨[], [i32t]⟩) ∧
    okVal? (lowerP3 8 [.async_]) = some (.func ⟨[i32t, i32t, i32t, i32t], [i32t]⟩) ∧
    okVal? (lowerP3 13 [.async_]) = some (.func ⟨[i32t], [i32t]⟩) ∧
    okVal? (lowerP3 14 [.async_]) = some (.func ⟨[i32t, i32t, i32t, i32t], [i32t]⟩) ∧
    okVal? (lowerP3 7 [.async_, .memory 0]) = some (.func ⟨[], [i32t]⟩) ∧
    okVal? (lowerP3 7 [.async_, .encoding .utf16]) = some (.func ⟨[], [i32t]⟩) := by
  decide +kernel

/-- `async` lowers needing memory: 5 flat params (spilled to a pointer), a `string` param, a
result (returned through a pointer), a `list` result (also needs `realloc`), and `realloc`
without `memory`. -/
theorem test_async_lower_needs_memory :
    canonErr? (lowerP3 9 [.async_]) = some "canonical option `memory` is required" ∧
    okVal? (lowerP3 9 [.async_, .memory 0]) = some (.func ⟨[i32t], [i32t]⟩) ∧
    canonErr? (lowerP3 10 [.async_]) = some "canonical option `memory` is required" ∧
    okVal? (lowerP3 10 [.async_, .memory 0]) = some (.func ⟨[i32t, i32t], [i32t]⟩) ∧
    canonErr? (lowerP3 11 [.async_]) = some "canonical option `memory` is required" ∧
    okVal? (lowerP3 11 [.async_, .memory 0]) = some (.func ⟨[i32t], [i32t]⟩) ∧
    canonErr? (lowerP3 12 [.async_]) = some "canonical option `memory` is required" ∧
    canonErr? (lowerP3 12 [.async_, .memory 0]) = some "canonical option `realloc` is required" ∧
    okVal? (lowerP3 12 [.async_, .memory 0, .realloc 1]) = some (.func ⟨[i32t], [i32t]⟩) ∧
    canonErr? (lowerP3 7 [.async_, .realloc 1]) =
      some "canonical option `realloc` requires `memory` to also be specified" := by
  decide +kernel

/-- Relational form: the memoryless `async func()` lower is valid. -/
theorem validCanon_async_unit_lower_no_memory :
    ValidCanon Features.p3 coreExternView testCanonCtx (.lower 7 [.async_])
      (.coreFunc (.func ⟨[], [i32t]⟩)) := by
  have hk : okVal? (lowerP3 7 [.async_]) = some (.func ⟨[], [i32t]⟩) := by decide +kernel
  apply checkLower?_sound
  revert hk
  unfold lowerP3
  cases checkLower? Features.p3 coreExternView testCanonCtx 7 [.async_] <;> simp [okVal?]

/-- Relational form: an `async` lower with a result and no `memory` has no derivation. -/
theorem not_validCanon_async_result_no_memory (e : CanonEntity CoreExternType) :
    ¬ ValidCanon Features.p3 coreExternView testCanonCtx (.lower 11 [.async_]) e := fun h => by
  have hk : (okVal? (checkLiftLower? Features.p3 coreExternView testCanonCtx
    (.lower 11 [.async_]))).isNone = true := by decide +kernel
  simp [checkLiftLower?_complete h, okVal?] at hk

/-! ### Memory64 -/

theorem test_memory64 :
    canonErr? (lowerP3 0 [.memory 1]) =
      some "64-bit memories require the component model memory64 feature" ∧
    okVal? (checkLower? Features.p3plus coreExternView testCanonCtx 4 [.memory 1, .realloc 11]) =
      some (.func ⟨[.int .i64, .int .i64], []⟩) ∧
    canonErr? (checkLower? Features.p3plus coreExternView testCanonCtx 4
      [.memory 1, .realloc 1]) =
      some "canonical option `realloc` uses a core function with an incorrect signature" := by
  decide +kernel

/-! ### General options at builtin sites -/

theorem test_builtin_opts :
    okVal? (checkCanonOpts? Features.p3 coreExternView testCanonCtx (.builtin .taskReturn) syncFt
      [.memory 0, .encoding .utf16]) = some () ∧
    canonErr? (checkCanonOpts? Features.p3 coreExternView testCanonCtx (.builtin .taskReturn)
      syncFt [.memory 0, .realloc 1]) = some "canonical option `realloc` is not allowed here" ∧
    okVal? (checkCanonOpts? Features.p3 coreExternView testCanonCtx (.builtin .copy) syncFt
      [.async_, .memory 0, .realloc 1]) = some () := by
  decide +kernel

end CanonOptsTests

end Silmaril.Wasm.Component.Validation

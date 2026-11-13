module

public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Thms
public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Defs

public import Silmaril.Raw.Wasm.Component.Validation.Context
public import Silmaril.Raw.Wasm.Component.ABI.Predicates
import all Init.Data.String.Defs
import all Init.Data.Repr

/-!
# Validation of value types and function types (with feature gating)

The `defvaltype` and `functype` rules of `Binary.md` §Type Definitions (notes after the
grammar) at component-model `a25fc0b`
(https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/Binary.md),
with `Explainer.md` §Type Definitions, and the feature gates of `Explainer.md`
§Gated Features (🔧 fixed-length lists, 🗺️ `map`, 📝 `error-context`, 🔀 `stream`/`future`
and `async` function types).

A syntactic `Syntax.DefValType` refers to earlier type definitions by index; validation
*resolves* it against the context `Γ : Ctx X` into an index-free `Types.ValType Nat`:

* `ResolveVT Γ v t`: a `valtype` is a primitive, or a type index naming a `defvaltype`
  (`Γ.type? i = some (.val t)`); a type index is replaced by the type it names (types are index-free
  ASTs, `Explainer.md` §Type Checking).
* `ResolveDef Γ d t`: the constructor-wise resolution of a `defvaltype`; `own`/`borrow` must
  name a resource type (`Γ.type? r = some (.resource v)`, and the handle carries the resource
  variable `v`); a `map` key must resolve to a WIT key type (`keyOfType?`).
* `ValidDefValType feat Γ d t`: `ResolveDef Γ d t`, the component-model well-formedness
  `ABI.ValType.WellFormedCM t` (nonempty record/variant/tuple/enum/flags, `|flags| ≤ 32`,
  fixed length `> 0`, kebab-case and strongly unique labels, no `borrow` in `stream`/`future`
  elements, no `stream<char>`, `elem_size(u, 'i64') < 2^28` for every subterm `u`), and the feature
  gates `Gated feat t` stated with the deep usage predicates
  `ABI.ValType.usesFixedList/usesMap/usesErrorContext/usesAsyncValue`.
* `ValidFuncType feat Γ ft t`: parameters and result resolve, `ABI.FuncType.WellFormedCM t`
  (parameter names are strongly unique labels, parameter/result types well formed, no `borrow`
  transitively in the result), every parameter/result type is `Gated`, and an `async`
  function type needs `feat.async_`.

The executable checkers `checkDefValType?` and `checkFuncType?` return
`Except ValidationError`; `checkDefValType?_iff` and `checkFuncType?_iff` state soundness
and completeness (`= .ok t ↔ Valid...`), with the corollaries `checkDefValType?_sound`,
`checkDefValType?_complete`, `checkFuncType?_sound` and `checkFuncType?_complete`. The
Boolean decision is made on the relational conditions themselves; the error *message* is
computed separately (`explainDefValType`, `explainFuncType`) and has no influence on
acceptance.

Design notes and deviations:

* Checks are deep over the resolved type (as `WellFormedCM` is), whereas wasmparser checks
  one `defvaltype` node at a time; the two agree whenever every type already in `Γ` was
  itself validated under the same features (nested types enter only through indices).
* A `map` key that is a type index naming a primitive key type is accepted (types are
  index-free, so `(type $k u8) (type (map $k u32))` is `map<u8, u32>`); `Binary.md` says
  "if k is in `<keytype>`".
* Features are a parameter of the judgements (Validation/Context.lean design decision).

Error messages: the following are wasmparser's, as matched by the upstream corpus
`test/validation/defined-types.wast`, `kebab.wast`, `resources.wast`, `max-value-size.wast` and
`test/binary/binary.wast`: "type index out of bounds" (via `Ctx.typeSlotAt?`), "type index {i} is
not a defined type", "type index {i} is not a resource type", "record type must have at least one
field", "variant type must have at least one case", "tuple type must have at least one type", "flags
must have at least one entry", "enum type must have at least one variant", "cannot have more than 32
flags", "{record field | variant case | flag | enum tag | function parameter} name cannot be empty",
"... name `x` is not in kebab case", "... name `X` conflicts with previous {field | case | flag |
tag | parameter} name `x`", "`stream<char>` is not valid at this time", "exceeds maximum byte size"
(substring) and "function result cannot contain a `borrow` type". The feature-gate,
fixed-length-zero, map-key and borrow-in-stream messages are descriptive and not verified against
wasmparser.

Tests (all kernel-checked, `decide +kernel`): duplicate record labels, empty record,
non-kebab field, 33 flags, `borrow` (and `list<borrow>`) in a function result, duplicate
parameters, the 🔀 gate on `async` function types and on `stream`, the 🔧 gate on fixed-length
lists, fixed length 0, `elem_size` at `2^28 - 1` (accepted) and `2^28` (rejected), `stream<char>`,
`borrow` in a `future`, the 📝 gate, `map` key resolution, `own` of a resource / non-resource,
a `valtype` index naming a resource, and an out-of-bounds type index. Upstream cases mirrored
(not replayed from the `.wast` files): `defined-types.wast` (flags bounds, empty types),
`kebab.wast` (label messages), `resources.wast` 687-724 (`own`/`borrow` of non-resources,
borrow in results), `max-value-size.wast` 15 and 25-27, `binary.wast` (`stream char`).

NOT modelled here: `resource`, `component` and `instance` type definitions, the
`borrow`-in-exported-value rule (🪙, `Validation/Defs.lean`), and the resource-name rules of
annotated function names. -/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types

variable {X : Type}

/-! ## Resolution (relational) -/

/-! ## Feature gating and the judgements -/

/-! ## Executable resolution -/

/-! ## Resolution: executable ↔ relational -/

/-! ## Error messages -/

/-! ## Checkers -/

theorem checkDefValType?_complete {feat : Features} {Γ : Ctx X} {d : Syntax.DefValType}
    {t : Types.ValType Nat} (h : ValidDefValType feat Γ d t) :
    checkDefValType? feat Γ d = .ok t := by
  have hr : resolveDef? Γ d = .ok t := resolveDef?_eq_ok.mpr h.resolve
  unfold checkDefValType?
  rw [hr]
  exact ite_eq_left_of_eq_true _ _ (eq_true ⟨h.wf, h.gated⟩)

/-- Soundness and completeness of `checkDefValType?`. -/
theorem checkDefValType?_iff {feat : Features} {Γ : Ctx X} {d : Syntax.DefValType}
    {t : Types.ValType Nat} :
    checkDefValType? feat Γ d = .ok t ↔ ValidDefValType feat Γ d t :=
  ⟨checkDefValType?_sound, checkDefValType?_complete⟩

theorem checkFuncType?_complete {feat : Features} {Γ : Ctx X} {ft : Syntax.FuncType}
    {t : Types.FuncType Nat} (h : ValidFuncType feat Γ ft t) :
    checkFuncType? feat Γ ft = .ok t := by
  have hp : resolveFields? Γ ft.params = .ok t.params := resolveFields?_eq_ok.mpr h.params
  have hr : resolveOpt? Γ ft.result = .ok t.result := resolveOpt?_eq_ok.mpr h.result
  have ht : ({ params := t.params, result := t.result, async_ := ft.async_ } :
      Types.FuncType Nat) = t := by rw [← h.async_]
  unfold checkFuncType?
  rw [hp, hr]
  dsimp only
  rw [ht]
  exact ite_eq_left_of_eq_true _ _ (eq_true h.ok)

/-- Soundness and completeness of `checkFuncType?`. -/
theorem checkFuncType?_iff {feat : Features} {Γ : Ctx X} {ft : Syntax.FuncType}
    {t : Types.FuncType Nat} :
    checkFuncType? feat Γ ft = .ok t ↔ ValidFuncType feat Γ ft t :=
  ⟨checkFuncType?_sound, checkFuncType?_complete⟩

/-! ## Tests -/

-- record with duplicate (strongly non-unique) labels
theorem check_record_duplicate_labels :
    errMessage? (checkDefValType? Features.p2 testCtx0
      (.record [("a-b", .prim .u8), ("A-B", .prim .u8)])) =
      some "record field name `A-B` conflicts with previous field name `a-b`" := by
  decide +kernel

theorem not_valid_record_duplicate_labels (t : Types.ValType Nat) :
    ¬ ValidDefValType Features.all testCtx0
      (.record [("a-b", .prim .u8), ("ab", .prim .u8)]) t := by
  intro v
  have h := checkDefValType?_iff.mpr v
  have : errMessage? (checkDefValType? Features.all testCtx0
      (.record [("a-b", .prim .u8), ("ab", .prim .u8)])) =
      some "record field name `ab` conflicts with previous field name `a-b`" := by
    decide +kernel
  rw [h] at this
  cases this

theorem check_record_ok :
    (checkDefValType? Features.p2 testCtx0 (.record [("a-b", .prim .u8), ("c", .prim .string)])
      ).toOption = some (.record [("a-b", .prim .u8), ("c", .prim .string)]) := by
  decide +kernel

theorem check_record_empty :
    errMessage? (checkDefValType? Features.p2 testCtx0 (.record [])) =
      some "record type must have at least one field" := by decide +kernel

theorem check_record_not_kebab :
    errMessage? (checkDefValType? Features.p2 testCtx0 (.record [("GoNnA", .prim .u8)])) =
      some "record field name `GoNnA` is not in kebab case" := by decide +kernel

theorem check_flags_33 :
    errMessage? (checkDefValType? Features.p2 testCtx0 (.flags ((List.range 33).map fun i =>
      "a" ++ String.ofList (List.replicate i 'b')))) =
      some "cannot have more than 32 flags" := by decide +kernel

-- borrow in a function result
theorem check_func_borrow_result :
    errMessage? (checkFuncType? Features.p2 testCtxRes ⟨false, [], some (.idx 1)⟩) =
      some "function result cannot contain a `borrow` type" := by decide +kernel

theorem check_func_list_borrow_result :
    errMessage? (checkFuncType? Features.p2 testCtxRes ⟨false, [], some (.idx 2)⟩) =
      some "function result cannot contain a `borrow` type" := by decide +kernel

theorem not_valid_func_borrow_result (t : Types.FuncType Nat) :
    ¬ ValidFuncType Features.all testCtxRes ⟨false, [], some (.idx 1)⟩ t := by
  intro v
  have h := checkFuncType?_iff.mpr v
  have : errMessage? (checkFuncType? Features.all testCtxRes ⟨false, [], some (.idx 1)⟩) =
      some "function result cannot contain a `borrow` type" := by decide +kernel
  rw [h] at this
  cases this

theorem check_func_borrow_param_ok :
    (checkFuncType? Features.p2 testCtxRes
      ⟨false, [("self", .idx 1)], some (.prim .u32)⟩).toOption =
      some ⟨[("self", .borrow 7)], some (.prim .u32), false⟩ := by decide +kernel

theorem check_func_duplicate_params :
    errMessage? (checkFuncType? Features.p2 testCtx0
      ⟨false, [("foo", .prim .u8), ("FOO", .prim .u8)], none⟩) =
      some "function parameter name `FOO` conflicts with previous parameter name `foo`" := by
  decide +kernel

theorem check_func_async_gate :
    errMessage? (checkFuncType? Features.p2 testCtx0 ⟨true, [], none⟩) =
      some "async component functions require the component model async feature" := by
  decide +kernel

theorem check_func_async_ok :
    (checkFuncType? Features.p3 testCtx0 ⟨true, [], none⟩).toOption =
      some ⟨[], none, true⟩ := by
  decide +kernel

-- fixed-length lists are gated by 🔧
theorem check_fixedList_gate :
    errMessage? (checkDefValType? Features.p3 testCtx0 (.fixedList (.prim .u8) 4)) =
      some "fixed size lists require the component model fixed size list feature" := by
  decide +kernel

theorem not_valid_fixedList_p3 (t : Types.ValType Nat) :
    ¬ ValidDefValType Features.p3 testCtx0 (.fixedList (.prim .u8) 4) t := by
  intro v
  have h := checkDefValType?_iff.mpr v
  have := check_fixedList_gate
  rw [h] at this
  cases this

theorem check_fixedList_ok :
    (checkDefValType? Features.p3plus testCtx0 (.fixedList (.prim .u8) 4)).toOption =
      some (.fixedList (.prim .u8) 4) := by decide +kernel

theorem check_fixedList_max_ok :
    (checkDefValType? Features.p3plus testCtx0 (.fixedList (.prim .u8) 268435455)).toOption =
      some (.fixedList (.prim .u8) 268435455) := by decide +kernel

theorem check_fixedList_too_big :
    errMessage? (checkDefValType? Features.p3plus testCtx0 (.fixedList (.prim .u8) 268435456)) =
      some "value type exceeds maximum byte size" := by decide +kernel

theorem check_fixedList_zero :
    errMessage? (checkDefValType? Features.p3plus testCtx0 (.fixedList (.prim .u8) 0)) =
      some "fixed size lists must have more than zero elements" := by decide +kernel

-- `stream<char>` is rejected even with 🔀
theorem check_stream_char :
    errMessage? (checkDefValType? Features.p3 testCtx0 (.stream (some (.prim .char)))) =
      some "`stream<char>` is not valid at this time" := by decide +kernel

theorem not_valid_stream_char (t : Types.ValType Nat) :
    ¬ ValidDefValType Features.all testCtx0 (.stream (some (.prim .char))) t := by
  intro v
  have h := checkDefValType?_iff.mpr v
  have : errMessage? (checkDefValType? Features.all testCtx0 (.stream (some (.prim .char)))) =
      some "`stream<char>` is not valid at this time" := by decide +kernel
  rw [h] at this
  cases this

theorem check_stream_u8_ok :
    (checkDefValType? Features.p3 testCtx0 (.stream (some (.prim .u8)))).toOption =
      some (.stream (some (.prim .u8))) := by decide +kernel

theorem check_stream_gate :
    errMessage? (checkDefValType? Features.p2 testCtx0 (.stream none)) =
      some "`stream` and `future` require the component model async feature" := by
  decide +kernel

theorem check_future_borrow :
    errMessage? (checkDefValType? Features.p3 testCtxRes (.future (some (.idx 1)))) =
      some "`stream` and `future` element types cannot contain a `borrow` type" := by
  decide +kernel

theorem check_error_context_gate :
    errMessage? (checkDefValType? Features.p3 testCtx0 (.option (.prim .errorContext))) =
      some "`error-context` requires the component model error-context feature" := by
  decide +kernel

theorem check_map_ok :
    (checkDefValType? Features.p3 testCtxRes (.map (.idx 3) (.prim .u32))).toOption =
      some (.map .u8 (.prim .u32)) := by decide +kernel

theorem check_map_bad_key :
    errMessage? (checkDefValType? Features.p3 testCtx0 (.map (.prim .f32) (.prim .u32))) =
      some "map key type must be a primitive key type" := by decide +kernel

-- `own`/`borrow` must name a resource type; `valtype` indices must name a defined type
theorem check_own_resource_ok :
    (checkDefValType? Features.p2 testCtxRes (.own 0)).toOption = some (.own 7) := by decide +kernel

theorem check_own_not_resource :
    errMessage? (checkDefValType? Features.p2 testCtxRes (.own 3)) =
      some "type index 3 is not a resource type" := by decide +kernel

theorem check_list_not_defined :
    errMessage? (checkDefValType? Features.p2 testCtxRes (.list (.idx 0))) =
      some "type index 0 is not a defined type" := by decide +kernel

theorem check_type_out_of_bounds :
    errMessage? (checkDefValType? Features.p2 testCtx0 (.borrow 5)) =
      some "unknown type 5: type index out of bounds" := by decide +kernel

end Silmaril.Wasm.Component.Validation

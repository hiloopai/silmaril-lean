module

public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Defs
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

/-- The option-carrying builtins (Binary.md §Canonical Definitions): `task.return`, the
stream/future `read`/`write` copies, `error-context.new` and `error-context.debug-message`. -/
inductive BuiltinOptsKind where
  | taskReturn | copy | errorContextNew | errorContextDebugMessage
  deriving Repr, DecidableEq

/-- Where a `canonopt*` list occurs. -/
inductive OptsDir where
  | lift | lower
  | builtin (k : BuiltinOptsKind)
  deriving Repr, DecidableEq

/-- The kind of a canonical option; the three string encodings are one kind ("can be passed
at most once, regardless of `N`"). -/
inductive OptKey where
  | encoding | memory | realloc | postReturn | async_ | callback
  deriving Repr, DecidableEq

namespace CanonOpts

/-- The kind of an option. -/
def key : Syntax.CanonOpt → OptKey
  | .encoding _ => .encoding
  | .memory _ => .memory
  | .realloc _ => .realloc
  | .postReturn _ => .postReturn
  | .async_ => .async_
  | .callback _ => .callback

/-- Whether an option kind may occur at a site: `post-return` and `callback` only on `canon
lift`; `async` on lift, lower and stream/future copies; `task.return` takes only `memory`
and `string-encoding`. -/
def allowed : OptsDir → OptKey → Bool
  | _, .encoding => true
  | _, .memory => true
  | .builtin .taskReturn, .realloc => false
  | _, .realloc => true
  | .lift, .postReturn => true
  | _, .postReturn => false
  | .lift, .async_ => true
  | .lower, .async_ => true
  | .builtin .copy, .async_ => true
  | _, .async_ => false
  | .lift, .callback => true
  | _, .callback => false

/-- The index of the (first) `memory` option. -/
def memIdx? : List Syntax.CanonOpt → Option Nat
  | [] => none
  | .memory i :: _ => some i
  | _ :: os => memIdx? os

/-- The index of the (first) `realloc` option. -/
def reallocIdx? : List Syntax.CanonOpt → Option Nat
  | [] => none
  | .realloc i :: _ => some i
  | _ :: os => reallocIdx? os

/-- The index of the (first) `post-return` option. -/
def postReturnIdx? : List Syntax.CanonOpt → Option Nat
  | [] => none
  | .postReturn i :: _ => some i
  | _ :: os => postReturnIdx? os

/-- The index of the (first) `callback` option. -/
def callbackIdx? : List Syntax.CanonOpt → Option Nat
  | [] => none
  | .callback i :: _ => some i
  | _ :: os => callbackIdx? os

/-- Whether `async` is present. -/
def hasAsync : List Syntax.CanonOpt → Bool
  | [] => false
  | .async_ :: _ => true
  | _ :: os => hasAsync os

/-- The string encoding (REF default `utf8`). -/
def encoding : List Syntax.CanonOpt → ABI.StringEncoding
  | [] => .utf8
  | .encoding e :: _ => e
  | _ :: os => encoding os

end CanonOpts

/-! ## Core types of the profile -/

/-- What validation needs to know about the profile's core extern types `X`: the address type
of a memory, the flat signature of a function, and the core function type of a flat signature
(`CoreEngine.ofFlatType`). -/
structure CoreView (X : Type) where
  /-- `some a` iff the extern type is a memory with address type `a` that is a subtype of
  `(memory a 0)`. -/
  memAddr? : X → Option AddrType
  /-- The flat signature of a function extern type. -/
  funcType? : X → Option V1.FuncType
  /-- The core function type of a flat signature. -/
  ofFlat : V1.FuncType → X

/-- The view for `Engine.CoreExternType` (V1/Lime1 profiles). -/
def coreExternView : CoreView Engine.CoreExternType where
  memAddr?
    | .memory a _ _ => some a
    | _ => none
  funcType?
    | .func t => some t
    | _ => none
  ofFlat := .func

namespace CanonOpts

variable (V : CoreView X) (Γ : Ctx X) (opts : List Syntax.CanonOpt)

/-- The address type of the `memory` option's memory, if it is present and a memory. -/
def memAddr? : Option AddrType := ((memIdx? opts).bind Γ.coreMem?).bind V.memAddr?

/-- The pointer type of the options: the memory's address type, `i32` without a memory
(D-g). -/
def ptrType : AddrType := (memAddr? V Γ opts).getD .i32

/-- The static ABI options (`ABI.Options`) selected by `opts`. -/
def abiOptions : ABI.Options :=
  ⟨ptrType V Γ opts, hasAsync opts, (callbackIdx? opts).isSome⟩

/-- The flat signature of core function `f`, if it exists and is a function. -/
def coreFuncType? (f : Nat) : Option V1.FuncType := (Γ.coreFunc? f).bind V.funcType?

end CanonOpts

/-- An address type allowed for `memory`: `i32`, or `i64` with 🐘. -/
def addrAllowed (feat : Features) : AddrType → Bool
  | .i32 => true
  | .i64 => feat.memory64

/-- The `realloc` signature `(func (param A A A A) (result A))`. -/
def reallocType (a : AddrType) : V1.FuncType :=
  ⟨[ABI.pointerType a, ABI.pointerType a, ABI.pointerType a, ABI.pointerType a],
   [ABI.pointerType a]⟩

/-- The `callback` signature `(func (param i32 i32 i32) (result i32))`. -/
def callbackType : V1.FuncType := ⟨[.int .i32, .int .i32, .int .i32], [.int .i32]⟩

/-! ## Option-valued quantifiers (decidable) -/

/-- `P a` for the value `a` of `o`, if any. -/
def OptAll {α : Type} (o : Option α) (P : α → Prop) : Prop :=
  match o with
  | none => True
  | some a => P a

/-- `o` has a value `a` with `P a`. -/
def OptSome {α : Type} (o : Option α) (P : α → Prop) : Prop :=
  match o with
  | none => False
  | some a => P a

instance {α : Type} (o : Option α) (P : α → Prop) [DecidablePred P] :
    Decidable (OptAll o P) :=
  match o with
  | none => isTrue trivial
  | some a => inferInstanceAs (Decidable (P a))

instance {α : Type} (o : Option α) (P : α → Prop) [DecidablePred P] :
    Decidable (OptSome o P) :=
  match o with
  | none => isFalse id
  | some a => inferInstanceAs (Decidable (P a))

/-! ## General `canonopt` validation (relational) -/

open CanonOpts in
/-- General `canonopt` validation (`CanonicalABI.md` §`canonopt` Validation) of `opts` at site
`dir` for the component function type `ft` (only its `async_` flag matters here). -/
structure ValidCanonOpts (feat : Features) (V : CoreView X) (Γ : Ctx X) (dir : OptsDir)
    (ft : Types.FuncType Nat) (opts : List Syntax.CanonOpt) : Prop where
  /-- Each option kind at most once (string encodings are one kind). -/
  nodup : (opts.map key).Nodup
  /-- Each option is allowed at the site. -/
  allowed : ∀ o ∈ opts, allowed dir (key o) = true
  /-- `memory` names a memory of address type `i32` (or `i64` with 🐘). -/
  memory : OptAll (memIdx? opts) fun i =>
    OptSome (Γ.coreMem? i) fun x => OptSome (V.memAddr? x) fun a => addrAllowed feat a = true
  /-- `realloc` requires `memory` and has type `(func (param A A A A) (result A))`. -/
  realloc : OptAll (reallocIdx? opts) fun f =>
    (memIdx? opts).isSome = true ∧ coreFuncType? V Γ f = some (reallocType (ptrType V Γ opts))
  /-- `async` is 🔀-gated. -/
  asyncGate : hasAsync opts = true → feat.async_ = true
  /-- `async` on lift/lower requires an `async` function type. -/
  asyncType : hasAsync opts = true → (dir = .lift ∨ dir = .lower) → ft.async_ = true
  /-- `async` excludes `post-return`. -/
  asyncPostReturn : hasAsync opts = true → postReturnIdx? opts = none
  /-- `callback` requires `async` and has type `(func (param i32 i32 i32) (result i32))`. -/
  callback : OptAll (callbackIdx? opts) fun f =>
    hasAsync opts = true ∧ coreFuncType? V Γ f = some callbackType
  /-- Without 🚟, an `async` lift requires `callback`. -/
  stackful : dir = .lift → hasAsync opts = true → callbackIdx? opts = none →
    feat.stackful = true

open CanonOpts in
theorem validCanonOpts_iff {feat : Features} {V : CoreView X} {Γ : Ctx X} {dir : OptsDir}
    {ft : Types.FuncType Nat} {opts : List Syntax.CanonOpt} :
    ValidCanonOpts feat V Γ dir ft opts ↔
      (opts.map key).Nodup ∧ (∀ o ∈ opts, allowed dir (key o) = true) ∧
      (OptAll (memIdx? opts) fun i =>
        OptSome (Γ.coreMem? i) fun x => OptSome (V.memAddr? x) fun a =>
          addrAllowed feat a = true) ∧
      (OptAll (reallocIdx? opts) fun f => (memIdx? opts).isSome = true ∧
        coreFuncType? V Γ f = some (reallocType (ptrType V Γ opts))) ∧
      (hasAsync opts = true → feat.async_ = true) ∧
      (hasAsync opts = true → (dir = .lift ∨ dir = .lower) → ft.async_ = true) ∧
      (hasAsync opts = true → postReturnIdx? opts = none) ∧
      (OptAll (callbackIdx? opts) fun f =>
        hasAsync opts = true ∧ coreFuncType? V Γ f = some callbackType) ∧
      (dir = .lift → hasAsync opts = true → callbackIdx? opts = none →
        feat.stackful = true) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9⟩,
   fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

instance (feat : Features) (V : CoreView X) (Γ : Ctx X) (dir : OptsDir)
    (ft : Types.FuncType Nat) (opts : List Syntax.CanonOpt) :
    Decidable (ValidCanonOpts feat V Γ dir ft opts) :=
  decidable_of_iff _ validCanonOpts_iff.symm

/-! ## `canon lift` and `canon lower` (relational) -/

/-! ## Types whose flat representation points into linear memory -/

mutual
  /-- The value type contains a `list` or `string` (or a `map`, which is a list) that is part
  of its own flat representation: the `CanonicalABI.md` §`canonopt` Validation condition
  "`T` contains a `list` or `string`". Unlike REF `contains` (`ABI.containsListOrString`)
  the search stops at `stream`/`future` (passed as `i32` handles; their payloads are copied
  by `stream.read`/`future.write` with those builtins' own options) and at resources, as
  wasmparser's `ComponentDefinedType::contains_ptr` does. -/
  def containsPtr {R : Type} : WIT.ClosedType R → Bool
    | .ref e => nomatch e
    | .prim .string => true
    | .prim _ => false
    | .own _ | .borrow _ | .flags _ | .errorContext | .enum _ => false
    | .stream _ | .future _ => false
    | .list _ | .map _ _ => true
    | .fixedList u _ => containsPtr u
    | .option u => containsPtr u
    | .record fs => containsPtrFields fs
    | .tuple ts => containsPtrList ts
    | .variant cs => containsPtrCases cs
    | .result a b => containsPtrOpt a || containsPtrOpt b

  def containsPtrFields {R : Type} : List (String × WIT.ClosedType R) → Bool
    | [] => false
    | (_, t) :: fs => containsPtr t || containsPtrFields fs

  def containsPtrList {R : Type} : List (WIT.ClosedType R) → Bool
    | [] => false
    | t :: ts => containsPtr t || containsPtrList ts

  def containsPtrCases {R : Type} : List (String × Option (WIT.ClosedType R)) → Bool
    | [] => false
    | (_, t) :: cs => containsPtrOpt t || containsPtrCases cs

  def containsPtrOpt {R : Type} : Option (WIT.ClosedType R) → Bool
    | none => false
    | some t => containsPtr t
end

namespace CanonOpts

variable (V : CoreView X) (Γ : Ctx X) (opts : List Syntax.CanonOpt) (ft : Types.FuncType Nat)

/-- `flatten_functype(opts, ft, 'lift')`. -/
def liftCoreType : V1.FuncType :=
  ABI.flattenFunc (abiOptions V Γ opts) .lift (ABI.FuncType.ofWIT ft)

/-- `flatten_functype(opts, ft, 'lower')`. -/
def lowerCoreType : V1.FuncType :=
  ABI.flattenFunc (abiOptions V Γ opts) .lower (ABI.FuncType.ofWIT ft)

/-- `len(flatten_types(ft.param_types()))`. -/
def flatParamCount : Nat := (ABI.flattenTypes (ptrType V Γ opts) (ft.params.map Prod.snd)).length

/-- `len(flatten_types(ft.result_type()))`. -/
def flatResultCount : Nat := (ABI.flattenTypes (ptrType V Γ opts) ft.result.toList).length

/-- Some parameter contains a `list` or `string` (`containsPtr`). -/
def paramsNeedMemory : Bool := ft.params.any fun p => containsPtr p.2

/-- The result contains a `list` or `string` (`containsPtr`). -/
def resultNeedsMemory : Bool := ft.result.any containsPtr

/-- The flat-result bound of a lift: `MAX_FLAT_RESULTS` sync, `MAX_FLAT_PARAMS` async. -/
def liftMaxFlatResults (async_ : Bool) : Nat :=
  if async_ then ABI.maxFlatParams else ABI.maxFlatResults

/-- REF `canon_lower`'s `max_flat_params`: 16 sync, 4 async. -/
def lowerMaxFlatParams (async_ : Bool) : Nat :=
  if async_ then ABI.maxFlatAsyncParams else ABI.maxFlatParams

/-- REF `canon_lower`'s `max_flat_results`: 1 sync, 0 async. -/
def lowerMaxFlatResults (async_ : Bool) : Nat :=
  if async_ then 0 else ABI.maxFlatResults

end CanonOpts

open CanonOpts in
/-- The conditions of `(canon lift $callee $opts (func (type $ft)))` (`CanonicalABI.md`
§`canon lift`), for a resolved function type `ft`. -/
structure LiftOk (feat : Features) (V : CoreView X) (Γ : Ctx X) (callee : Nat)
    (opts : List Syntax.CanonOpt) (ft : Types.FuncType Nat) : Prop where
  validOpts : ValidCanonOpts feat V Γ .lift ft opts
  /-- `lift(param)`: a parameter containing a list or string requires `realloc`. -/
  paramsRealloc : paramsNeedMemory ft = true → (reallocIdx? opts).isSome = true
  /-- `lower(result)`: a result containing a list or string requires `memory`. -/
  resultMemory : resultNeedsMemory ft = true → (memIdx? opts).isSome = true
  /-- More than `MAX_FLAT_PARAMS` flat params require `realloc`. -/
  spillParams : ABI.maxFlatParams < flatParamCount V Γ opts ft →
    (reallocIdx? opts).isSome = true
  /-- More flat results than the lift bound require `memory`. -/
  spillResults : liftMaxFlatResults (hasAsync opts) < flatResultCount V Γ opts ft →
    (memIdx? opts).isSome = true
  /-- The callee has type `flatten_functype(opts, ft, 'lift')`. -/
  callee : coreFuncType? V Γ callee = some (liftCoreType V Γ opts ft)
  /-- `post-return` takes the lifted core results and returns nothing. -/
  postReturn : OptAll (postReturnIdx? opts) fun p =>
    coreFuncType? V Γ p = some ⟨(liftCoreType V Γ opts ft).results, []⟩

open CanonOpts in
theorem liftOk_iff {feat : Features} {V : CoreView X} {Γ : Ctx X} {callee : Nat}
    {opts : List Syntax.CanonOpt} {ft : Types.FuncType Nat} :
    LiftOk feat V Γ callee opts ft ↔
      ValidCanonOpts feat V Γ .lift ft opts ∧
      (paramsNeedMemory ft = true → (reallocIdx? opts).isSome = true) ∧
      (resultNeedsMemory ft = true → (memIdx? opts).isSome = true) ∧
      (ABI.maxFlatParams < flatParamCount V Γ opts ft → (reallocIdx? opts).isSome = true) ∧
      (liftMaxFlatResults (hasAsync opts) < flatResultCount V Γ opts ft →
        (memIdx? opts).isSome = true) ∧
      coreFuncType? V Γ callee = some (liftCoreType V Γ opts ft) ∧
      (OptAll (postReturnIdx? opts) fun p =>
        coreFuncType? V Γ p = some ⟨(liftCoreType V Γ opts ft).results, []⟩) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩,
   fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩

instance (feat : Features) (V : CoreView X) (Γ : Ctx X) (callee : Nat)
    (opts : List Syntax.CanonOpt) (ft : Types.FuncType Nat) :
    Decidable (LiftOk feat V Γ callee opts ft) :=
  decidable_of_iff _ liftOk_iff.symm

open CanonOpts in
/-- The conditions of `(canon lower $callee $opts (core func))` (`CanonicalABI.md`
§`canon lower`), for the callee's function type `ft`.

`memory` is required exactly when the lowering loads or stores (`Explainer.md` §Canonical
ABI: "If the Canonical ABI needs to load or store, validation requires this option to be
present"): a parameter containing a list or string (`paramsMemory`), a result containing one
(`resultRealloc`, since `realloc` requires `memory`), or flat params/results beyond
`canon_lower`'s bounds (`spillParams`, `spillResults`). For `async` these are exactly the
places REF `definitions.py` (pin `a25fc0b`) reads `opts.memory`: `flatten_functype`, case
`'lower'`, async branch (L1793-1794 `flat_params = [opts.memory.ptr_type()]` when more than
`MAX_FLAT_ASYNC_PARAMS` (L1766); L1795-1796 a result pointer when `flat_results` is
non-empty);
`canon_lower` sets `max_flat_params = MAX_FLAT_ASYNC_PARAMS`, `max_flat_results = 0`
(L2181-2182), and `lift_flat_values` (L2192) / `lower_flat_values` (L2205) touch memory only
past those bounds; `flatten_type` uses it for `string` and variable-length `list`. So
`async func()` lowers without `memory`, as wasmparser `ComponentFuncType::lower`
(`component_types.rs`, `(Abi::Lower, Concurrency::Async)`: memory only `if
self.result.is_some()`) and wasmtime accept. The blanket "🔀 if `async` is specified,
`memory` must be present" of `CanonicalABI.md` §`canon lower` is not modelled. -/
structure LowerOk (feat : Features) (V : CoreView X) (Γ : Ctx X)
    (opts : List Syntax.CanonOpt) (ft : Types.FuncType Nat) : Prop where
  validOpts : ValidCanonOpts feat V Γ .lower ft opts
  /-- `lower(param)`: a parameter containing a list or string requires `memory`. -/
  paramsMemory : paramsNeedMemory ft = true → (memIdx? opts).isSome = true
  /-- `lift(result)`: a result containing a list or string requires `realloc`. -/
  resultRealloc : resultNeedsMemory ft = true → (reallocIdx? opts).isSome = true
  /-- More flat params than `max_flat_params` require `memory`. -/
  spillParams : lowerMaxFlatParams (hasAsync opts) < flatParamCount V Γ opts ft →
    (memIdx? opts).isSome = true
  /-- More flat results than `max_flat_results` require `memory`. -/
  spillResults : lowerMaxFlatResults (hasAsync opts) < flatResultCount V Γ opts ft →
    (memIdx? opts).isSome = true

open CanonOpts in
-- FLAG(statement-change): async lower no longer requires memory unconditionally (Explainer.md
-- §Canonical ABI, definitions.py flatten_functype/canon_lower; CanonicalABI.md §`canon lower`
-- "if `async` is specified, `memory` must be present" not followed; wasmparser
-- component_types.rs `ComponentFuncType::lower`).
theorem lowerOk_iff {feat : Features} {V : CoreView X} {Γ : Ctx X}
    {opts : List Syntax.CanonOpt} {ft : Types.FuncType Nat} :
    LowerOk feat V Γ opts ft ↔
      ValidCanonOpts feat V Γ .lower ft opts ∧
      (paramsNeedMemory ft = true → (memIdx? opts).isSome = true) ∧
      (resultNeedsMemory ft = true → (reallocIdx? opts).isSome = true) ∧
      (lowerMaxFlatParams (hasAsync opts) < flatParamCount V Γ opts ft →
        (memIdx? opts).isSome = true) ∧
      (lowerMaxFlatResults (hasAsync opts) < flatResultCount V Γ opts ft →
        (memIdx? opts).isSome = true) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩,
   fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩⟩

instance (feat : Features) (V : CoreView X) (Γ : Ctx X)
    (opts : List Syntax.CanonOpt) (ft : Types.FuncType Nat) :
    Decidable (LowerOk feat V Γ opts ft) :=
  decidable_of_iff _ lowerOk_iff.symm

/-- The entity a `canon lift`/`canon lower` definition pushes: a component function (into
`funcs`) or a core function (into `coreFuncs`). -/
inductive CanonEntity (X : Type) where
  | func (t : Types.FuncType Nat)
  | coreFunc (t : X)

/-- Validity of a `canon lift` / `canon lower` definition and the entity it pushes. Builtins
are validated by `Validation/Builtins.lean` (no constructor here). -/
inductive ValidCanon (feat : Features) (V : CoreView X) (Γ : Ctx X) :
    Syntax.Canon → CanonEntity X → Prop where
  /-- `(canon lift $callee $opts (func (type $t)))`: `$t` names a function type `ft`, and the
  new component function has type `ft`. -/
  | lift {callee t : Nat} {opts : List Syntax.CanonOpt} {ft : Types.FuncType Nat}
      (hty : Γ.type? t = some (.func ft)) (h : LiftOk feat V Γ callee opts ft) :
      ValidCanon feat V Γ (.lift callee opts t) (.func ft)
  /-- `(canon lower $f $opts (core func))`: `$f : ft`, and the new core function has type
  `flatten_functype(opts, ft, 'lower')`. -/
  | lower {f : Nat} {opts : List Syntax.CanonOpt} {ft : Types.FuncType Nat}
      (hty : Γ.func? f = some ft) (h : LowerOk feat V Γ opts ft) :
      ValidCanon feat V Γ (.lower f opts)
        (.coreFunc (V.ofFlat (CanonOpts.lowerCoreType V Γ opts ft)))

/-! ## Error messages (never influence acceptance) -/

namespace CanonOpts

/-- The option name in wasmparser's messages. -/
def keyName : OptKey → String
  | .encoding => "string-encoding"
  | .memory => "memory"
  | .realloc => "realloc"
  | .postReturn => "post-return"
  | .async_ => "async"
  | .callback => "callback"

/-- The encoding name in wasmparser's messages. -/
def encodingName : ABI.StringEncoding → String
  | .utf8 => "utf8"
  | .utf16 => "utf16"
  | .latin1Utf16 => "latin1-utf16"

/-- The first earlier option of the same kind. -/
def findKey (k : OptKey) : List Syntax.CanonOpt → Option Syntax.CanonOpt
  | [] => none
  | o :: os => if key o = k then some o else findKey k os

/-- The first duplicated option kind, in wasmparser's wording (`seen`: earlier options, most
recent first). -/
def dupError : List Syntax.CanonOpt → List Syntax.CanonOpt → Option ValidationError
  | _, [] => none
  | seen, o :: os =>
    match findKey (key o) seen, o with
    | some (.encoding e₁), .encoding e₂ =>
      some ⟨s!"canonical encoding option `{encodingName e₁}` conflicts with option \
        `{encodingName e₂}`"⟩
    | some _, _ => some ⟨s!"canonical option `{keyName (key o)}` is specified more than once"⟩
    | none, _ => dupError (o :: seen) os

/-- The first option not allowed at the site. -/
def allowedError (dir : OptsDir) : List Syntax.CanonOpt → Option ValidationError
  | [] => none
  | o :: os =>
    if allowed dir (key o) then allowedError dir os
    else match dir, key o with
      | .lower, .postReturn =>
        some ⟨"canonical option `post-return` cannot be specified for lowerings"⟩
      | _, k => some ⟨s!"canonical option `{keyName k}` is not allowed here"⟩

/-- wasmparser's `Debug` spelling of a core value type. -/
def numTypeName : NumType → String
  | .int .i32 => "I32"
  | .int .i64 => "I64"
  | .float .f32 => "F32"
  | .float .f64 => "F64"

/-- `[I32, I64]`-style rendering of a core type list. -/
def renderTypes : List NumType → String
  | [] => "[]"
  | t :: ts => "[" ++ ts.foldl (fun s u => s ++ ", " ++ numTypeName u) (numTypeName t) ++ "]"

/-- Errors of a core function reference expected to have type `expected`. -/
def funcSigError (V : CoreView X) (Γ : Ctx X) (what : String) (f : Nat)
    (expected : V1.FuncType) : Option ValidationError :=
  match Γ.coreFunc? f with
  | none => some (ValidationError.outOfBounds "core function" "function" f)
  | some x =>
    if V.funcType? x = some expected then none
    else some ⟨s!"canonical option `{what}` uses a core function with an incorrect signature"⟩

variable (feat : Features) (V : CoreView X) (Γ : Ctx X) (dir : OptsDir)
  (ft : Types.FuncType Nat) (opts : List Syntax.CanonOpt)

/-- The error list of `ValidCanonOpts`, in check order. -/
def optsErrors : List (Option ValidationError) :=
  [dupError [] opts,
   allowedError dir opts,
   match memIdx? opts with
   | none => none
   | some i => match Γ.coreMem? i with
     | none => some (ValidationError.outOfBounds "memory" "memory" i)
     | some x => match V.memAddr? x with
       | none => some ⟨"canonical option `memory` must be a memory"⟩
       | some a => errIf (!addrAllowed feat a)
           "64-bit memories require the component model memory64 feature",
   match reallocIdx? opts with
   | none => none
   | some f =>
     if (memIdx? opts).isNone then
       some ⟨"canonical option `realloc` requires `memory` to also be specified"⟩
     else funcSigError V Γ "realloc" f (reallocType (ptrType V Γ opts)),
   errIf (hasAsync opts && !feat.async_)
     "the `async` canonical option requires the component model async feature",
   errIf (hasAsync opts && (dir == .lift || dir == .lower) && !ft.async_)
     "the `async` canonical option requires an async function type",
   errIf (hasAsync opts && (postReturnIdx? opts).isSome)
     "cannot specify post-return function in async",
   match callbackIdx? opts with
   | none => none
   | some f =>
     if !hasAsync opts then some ⟨"canonical option `callback` requires `async`"⟩
     else funcSigError V Γ "callback" f callbackType,
   errIf (dir == .lift && hasAsync opts && (callbackIdx? opts).isNone && !feat.stackful)
     "async lift without `callback` requires the component model async stackful feature"]

/-- The error reported when `ValidCanonOpts` fails. -/
def explainCanonOpts : ValidationError :=
  firstError ⟨"invalid canonical options"⟩ (optsErrors feat V Γ dir ft opts)

/-- The error reported when `LiftOk` fails. -/
def explainLift (callee : Nat) : ValidationError :=
  let needRealloc := paramsNeedMemory ft || decide (ABI.maxFlatParams < flatParamCount V Γ opts ft)
  let needMemory := needRealloc || resultNeedsMemory ft ||
    decide (liftMaxFlatResults (hasAsync opts) < flatResultCount V Γ opts ft)
  let core := liftCoreType V Γ opts ft
  firstError ⟨"invalid canonical lift"⟩
    (optsErrors feat V Γ .lift ft opts ++
     [errIf (needMemory && (memIdx? opts).isNone) "canonical option `memory` is required",
      errIf (needRealloc && (reallocIdx? opts).isNone) "canonical option `realloc` is required",
      match Γ.coreFunc? callee with
      | none => some (ValidationError.outOfBounds "core function" "function" callee)
      | some x => match V.funcType? x with
        | none => some ⟨s!"core function {callee} is not a function"⟩
        | some actual =>
          if core.params ≠ actual.params then
            some ⟨s!"lowered parameter types `{renderTypes core.params}` do not match \
              parameter types `{renderTypes actual.params}`"⟩
          else if core.results ≠ actual.results then
            some ⟨s!"lowered result types `{renderTypes core.results}` do not match \
              result types `{renderTypes actual.results}`"⟩
          else none,
      match postReturnIdx? opts with
      | none => none
      | some p => funcSigError V Γ "post-return" p ⟨core.results, []⟩])

/-- The error reported when `LowerOk` fails. -/
def explainLower : ValidationError :=
  let needMemory := paramsNeedMemory ft || resultNeedsMemory ft ||
    decide (lowerMaxFlatParams (hasAsync opts) < flatParamCount V Γ opts ft) ||
    decide (lowerMaxFlatResults (hasAsync opts) < flatResultCount V Γ opts ft)
  firstError ⟨"invalid canonical lower"⟩
    (optsErrors feat V Γ .lower ft opts ++
     [errIf (needMemory && (memIdx? opts).isNone) "canonical option `memory` is required",
      errIf (resultNeedsMemory ft && (reallocIdx? opts).isNone)
        "canonical option `realloc` is required"])

end CanonOpts

/-! ## Checkers -/

/-- General `canonopt` validation. Sound and complete for `ValidCanonOpts`
(`checkCanonOpts?_iff`). -/
def checkCanonOpts? (feat : Features) (V : CoreView X) (Γ : Ctx X) (dir : OptsDir)
    (ft : Types.FuncType Nat) (opts : List Syntax.CanonOpt) : Except ValidationError Unit :=
  if ValidCanonOpts feat V Γ dir ft opts then .ok ()
  else .error (CanonOpts.explainCanonOpts feat V Γ dir ft opts)

/-- Validate `(canon lift $callee $opts (func (type $t)))`, returning the type of the new
component function. Sound and complete (`checkLift?_iff`). -/
def checkLift? (feat : Features) (V : CoreView X) (Γ : Ctx X) (callee : Nat)
    (opts : List Syntax.CanonOpt) (t : Nat) : Except ValidationError (Types.FuncType Nat) :=
  match Γ.typeSlotAt? t with
  | .error e => .error e
  | .ok s =>
    match s.def_ with
    | .func ft =>
      if LiftOk feat V Γ callee opts ft then .ok ft
      else .error (CanonOpts.explainLift feat V Γ ft opts callee)
    | _ => .error ⟨s!"type index {t} is not a function type"⟩

/-- Validate `(canon lower $f $opts (core func))`, returning the type of the new core
function. Sound and complete (`checkLower?_iff`). -/
def checkLower? (feat : Features) (V : CoreView X) (Γ : Ctx X) (f : Nat)
    (opts : List Syntax.CanonOpt) : Except ValidationError X :=
  match Γ.funcAt? f with
  | .error e => .error e
  | .ok ft =>
    if LowerOk feat V Γ opts ft then .ok (V.ofFlat (CanonOpts.lowerCoreType V Γ opts ft))
    else .error (CanonOpts.explainLower feat V Γ ft opts)

/-- Validate a `canon lift`/`canon lower` definition, returning the pushed entity. Builtins
are rejected here (they are checked by `Validation/Builtins.lean`). -/
def checkLiftLower? (feat : Features) (V : CoreView X) (Γ : Ctx X) :
    Syntax.Canon → Except ValidationError (CanonEntity X)
  | .lift callee opts t => (checkLift? feat V Γ callee opts t).map .func
  | .lower f opts => (checkLower? feat V Γ f opts).map .coreFunc
  | .builtin _ => .error ⟨"canonical builtins are not validated by `checkLiftLower?`"⟩

/-! ## Soundness and completeness -/

/-! ## Tests -/

namespace CanonOptsTests

open Engine (CoreExternType)

/-- The value of a successful result. -/
def okVal? {α : Type} : Except ValidationError α → Option α
  | .ok a => some a
  | .error _ => none

/-- The message of an error result. -/
def canonErr? {α : Type} : Except ValidationError α → Option String
  | .error e => some e.message
  | .ok _ => none

/-- `i32` (test shorthand). -/
abbrev i32t : NumType := .int .i32

/-- Core functions of the test context:
0 `[] → []`, 1 `realloc`, 2 `callback`, 3 `[i32 i32] → []`, 4 `[i32] → [i32]`,
5 `[] → [i32]`, 6 `[i32] → []`, 7 `[i32] → []` (post-return), 8 `[] → []` (bad realloc),
9 `[i32 i32 i32] → []` (bad callback), 10 `[i32]→[]` (callback-less async lift target). -/
def testCoreFuncs : List CoreExternType :=
  [.func ⟨[], []⟩, .func (reallocType .i32), .func callbackType, .func ⟨[i32t, i32t], []⟩,
   .func ⟨[i32t], [i32t]⟩, .func ⟨[], [i32t]⟩, .func ⟨[i32t], []⟩,
   .func ⟨[i32t], []⟩,
   .func ⟨[], []⟩, .func ⟨[i32t, i32t, i32t], []⟩, .func ⟨[i32t], []⟩,
   .func (reallocType .i64)]

def syncFt : Types.FuncType Nat := { params := [], result := none }
def asyncFt : Types.FuncType Nat := { params := [], result := none, async_ := true }
def listParamFt : Types.FuncType Nat := { params := [("p", .list (.prim .u8))], result := none }
def stringParamFt : Types.FuncType Nat := { params := [("msg", .prim .string)], result := none }
def stringResultFt : Types.FuncType Nat := { params := [], result := some (.prim .string) }
def pairResultFt : Types.FuncType Nat :=
  { params := [], result := some (.tuple [.prim .s8, .prim .u8]) }
def bigResultFt : Types.FuncType Nat :=
  { params := [], result := some (.tuple (List.replicate 8 (.prim .u64))) }
def twentyParamsFt : Types.FuncType Nat :=
  { params := (List.range 20).map fun i => (s!"p{i + 1}", .prim .u32), result := none }
def asyncParamFt : Types.FuncType Nat :=
  { params := [("x", .prim .u32)], result := some (.prim .u32), async_ := true }
def streamParamFt : Types.FuncType Nat :=
  { params := [("s", .stream (some (.prim .string)))], result := none }
def futureResultFt : Types.FuncType Nat :=
  { params := [], result := some (.future (some (.list (.prim .u8)))) }
/-- `async` with `n` `u32` params and no result. -/
def asyncU32ParamsFt (n : Nat) : Types.FuncType Nat :=
  { params := (List.range n).map fun i => (s!"p{i + 1}", .prim .u32), result := none,
    async_ := true }
def asyncStringParamFt : Types.FuncType Nat :=
  { params := [("s", .prim .string)], result := none, async_ := true }
def asyncU32ResultFt : Types.FuncType Nat :=
  { params := [], result := some (.prim .u32), async_ := true }
def asyncListResultFt : Types.FuncType Nat :=
  { params := [], result := some (.list (.prim .u8)), async_ := true }
def asyncStreamStringParamFt : Types.FuncType Nat :=
  { params := [("s", .stream (some (.prim .string)))], result := none, async_ := true }
def asyncFixedListParamFt : Types.FuncType Nat :=
  { params := [("l", .fixedList (.prim .u8) 4)], result := none, async_ := true }

/-- The test context: memories 0 (`i32`) and 1 (`i64`), `testCoreFuncs`, types 0..9 as below
(8 is a value type), and component functions 0..14 (7..14 are the `async` lowers of the
memory tests: unit, 4 and 5 `u32` params, a `string` param, a `u32` result, a `list u8`
result, a `stream<string>` param, a `list<u8, 4>` param). -/
def testCanonCtx : Ctx CoreExternType :=
  { kind := .component
    coreMems := [.memory .i32 1 none, .memory .i64 1 none]
    coreFuncs := testCoreFuncs
    types := [⟨.func syncFt, 0⟩, ⟨.func asyncFt, 1⟩, ⟨.func listParamFt, 2⟩,
      ⟨.func stringParamFt, 3⟩, ⟨.func stringResultFt, 4⟩, ⟨.func pairResultFt, 5⟩,
      ⟨.func twentyParamsFt, 6⟩, ⟨.func asyncParamFt, 7⟩, ⟨.val (.prim .string), 8⟩,
      ⟨.func streamParamFt, 9⟩]
    funcs := [syncFt, bigResultFt, listParamFt, stringResultFt, stringParamFt, asyncParamFt,
      futureResultFt, asyncFt, asyncU32ParamsFt 4, asyncU32ParamsFt 5, asyncStringParamFt,
      asyncU32ResultFt, asyncListResultFt, asyncStreamStringParamFt, asyncFixedListParamFt] }

/-- Lift under the P3 features (🔀 on, 🚟 off). -/
def liftP3 (callee : Nat) (opts : List Syntax.CanonOpt) (t : Nat) :=
  checkLift? Features.p3 coreExternView testCanonCtx callee opts t

/-- Lower under the P3 features. -/
def lowerP3 (f : Nat) (opts : List Syntax.CanonOpt) :=
  checkLower? Features.p3 coreExternView testCanonCtx f opts

/-! ### `validate-no-async-abi-for-sync-type.wast` -/

/-! ### `abi.wast` -/

/-! ### Callback and async rules -/

/-! ### When an `async` lower needs `memory`

Only when the lowering loads or stores (`LowerOk`; REF `flatten_functype` L1793-1797,
`canon_lower` L2181-2182; wasmparser `ComponentFuncType::lower`). The cases agree with
wasm-tools 1.259.0 and wasmtime 49.0.1. -/

/-! ### Memory64 -/

/-! ### General options at builtin sites -/

end CanonOptsTests

end Silmaril.Wasm.Component.Validation

module

public import Silmaril.Wasm.Component.Reference.Validation.Context.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Predicates.Defs
import all Init.Data.String.Defs
import all Init.Data.Repr
public import Silmaril.Wasm.Component.Reference.Types.Basic.Defs

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

/-- The semantic type of a primitive value type (`error-context` is its own former). -/
def primType : Syntax.Prim → Types.ValType Nat
  | .bool => .prim .bool | .s8 => .prim .s8 | .u8 => .prim .u8 | .s16 => .prim .s16
  | .u16 => .prim .u16 | .s32 => .prim .s32 | .u32 => .prim .u32 | .s64 => .prim .s64
  | .u64 => .prim .u64 | .f32 => .prim .f32 | .f64 => .prim .f64 | .char => .prim .char
  | .string => .prim .string | .errorContext => .errorContext

/-- The WIT key type of a resolved type (`Binary.md` `<keytype>`: `bool`, integers, `char`,
`string`), if it is one. -/
def keyOfType? : Types.ValType Nat → Option WIT.KeyType
  | .prim .bool => some .bool | .prim .u8 => some .u8 | .prim .u16 => some .u16
  | .prim .u32 => some .u32 | .prim .u64 => some .u64 | .prim .s8 => some .s8
  | .prim .s16 => some .s16 | .prim .s32 => some .s32 | .prim .s64 => some .s64
  | .prim .char => some .char | .prim .string => some .string
  | _ => none

/-- A `valtype` resolves to a semantic type: a primitive, or a type index naming a
`defvaltype` (`Binary.md`: "the `typeidx` [must] refer to a `defvaltype`"). -/
inductive ResolveVT (Γ : Ctx X) : Syntax.VT → Types.ValType Nat → Prop where
  | prim (p : Syntax.Prim) : ResolveVT Γ (.prim p) (primType p)
  | idx {i : Nat} {t : Types.ValType Nat} (h : Γ.type? i = some (.val t)) :
      ResolveVT Γ (.idx i) t

/-- An optional `valtype` resolves pointwise. -/
inductive ResolveOpt (Γ : Ctx X) : Option Syntax.VT → Option (Types.ValType Nat) → Prop where
  | none : ResolveOpt Γ none none
  | some {v : Syntax.VT} {t : Types.ValType Nat} (h : ResolveVT Γ v t) :
      ResolveOpt Γ (some v) (some t)

/-- Labelled `valtype`s (record fields, function parameters) resolve pointwise, keeping labels. -/
inductive ResolveFields (Γ : Ctx X) :
    List (String × Syntax.VT) → List (String × Types.ValType Nat) → Prop where
  | nil : ResolveFields Γ [] []
  | cons {n : String} {v : Syntax.VT} {t : Types.ValType Nat} {fs ts}
      (h : ResolveVT Γ v t) (hs : ResolveFields Γ fs ts) :
      ResolveFields Γ ((n, v) :: fs) ((n, t) :: ts)

/-- Tuple components resolve pointwise. -/
inductive ResolveList (Γ : Ctx X) : List Syntax.VT → List (Types.ValType Nat) → Prop where
  | nil : ResolveList Γ [] []
  | cons {v : Syntax.VT} {t : Types.ValType Nat} {vs ts}
      (h : ResolveVT Γ v t) (hs : ResolveList Γ vs ts) : ResolveList Γ (v :: vs) (t :: ts)

/-- Variant cases resolve pointwise, keeping labels. -/
inductive ResolveCases (Γ : Ctx X) :
    List (String × Option Syntax.VT) → List (String × Option (Types.ValType Nat)) → Prop where
  | nil : ResolveCases Γ [] []
  | cons {n : String} {v : Option Syntax.VT} {t : Option (Types.ValType Nat)} {cs ts}
      (h : ResolveOpt Γ v t) (hs : ResolveCases Γ cs ts) :
      ResolveCases Γ ((n, v) :: cs) ((n, t) :: ts)

/-- Constructor-wise resolution of a `defvaltype` (no well-formedness yet). `own`/`borrow`
must name a resource type; a `map` key must resolve to a key type. -/
inductive ResolveDef (Γ : Ctx X) : Syntax.DefValType → Types.ValType Nat → Prop where
  | prim (p : Syntax.Prim) : ResolveDef Γ (.prim p) (primType p)
  | record {fs ts} (h : ResolveFields Γ fs ts) : ResolveDef Γ (.record fs) (.record ts)
  | variant {cs ts} (h : ResolveCases Γ cs ts) : ResolveDef Γ (.variant cs) (.variant ts)
  | list {v t} (h : ResolveVT Γ v t) : ResolveDef Γ (.list v) (.list t)
  | fixedList {v t} (n : Nat) (h : ResolveVT Γ v t) :
      ResolveDef Γ (.fixedList v n) (.fixedList t n)
  | tuple {vs ts} (h : ResolveList Γ vs ts) : ResolveDef Γ (.tuple vs) (.tuple ts)
  | flags (ls : List String) : ResolveDef Γ (.flags ls) (.flags ls)
  | enum (ls : List String) : ResolveDef Γ (.enum ls) (.enum ls)
  | option {v t} (h : ResolveVT Γ v t) : ResolveDef Γ (.option v) (.option t)
  | result {a b a' b'} (ha : ResolveOpt Γ a a') (hb : ResolveOpt Γ b b') :
      ResolveDef Γ (.result a b) (.result a' b')
  | map {k v kt t} {key : WIT.KeyType} (hk : ResolveVT Γ k kt) (hkey : keyOfType? kt = some key)
      (hv : ResolveVT Γ v t) : ResolveDef Γ (.map k v) (.map key t)
  | own {r : Nat} {v : Nat} (h : Γ.type? r = some (.resource v)) :
      ResolveDef Γ (.own r) (.own v)
  | borrow {r : Nat} {v : Nat} (h : Γ.type? r = some (.resource v)) :
      ResolveDef Γ (.borrow r) (.borrow v)
  | stream {a a'} (h : ResolveOpt Γ a a') : ResolveDef Γ (.stream a) (.stream a')
  | future {a a'} (h : ResolveOpt Γ a a') : ResolveDef Γ (.future a) (.future a')

/-! ## Feature gating and the judgements -/

/-- The feature gates of a resolved type (`Explainer.md` §Gated Features), via the deep
usage predicates: 🔧 fixed-length lists, 🗺️ `map`, 📝 `error-context`, 🔀 `stream`/`future`. -/
def Gated (feat : Features) (t : Types.ValType Nat) : Prop :=
  (ABI.ValType.usesFixedList t = true → feat.fixedLists = true) ∧
  (ABI.ValType.usesMap t = true → feat.map = true) ∧
  (ABI.ValType.usesErrorContext t = true → feat.errorContext = true) ∧
  (ABI.ValType.usesAsyncValue t = true → feat.async_ = true)

instance (feat : Features) (t : Types.ValType Nat) : Decidable (Gated feat t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A `defvaltype` is valid with semantic type `t`: it resolves to `t`, `t` satisfies the
component-model well-formedness rules (`ABI.ValType.WellFormedCM`, including
`elem_size(t, 'i64') < 2^28`), and `t` only uses enabled features. -/
structure ValidDefValType (feat : Features) (Γ : Ctx X) (d : Syntax.DefValType)
    (t : Types.ValType Nat) : Prop where
  resolve : ResolveDef Γ d t
  wf : ABI.ValType.WellFormedCM t
  gated : Gated feat t

/-- The conditions on a resolved function type: `ABI.FuncType.WellFormedCM` (strongly unique
kebab-case parameter names, well-formed types, no `borrow` in the result), gated parameter
and result types, and `async` only under 🔀. -/
def FuncTypeOk (feat : Features) (t : Types.FuncType Nat) : Prop :=
  ABI.FuncType.WellFormedCM t ∧ (∀ p ∈ t.params, Gated feat p.2) ∧
    (∀ r ∈ t.result, Gated feat r) ∧ (t.async_ = true → feat.async_ = true)

instance (feat : Features) (t : Types.FuncType Nat) : Decidable (FuncTypeOk feat t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A `functype` is valid with semantic type `t`: parameters and result resolve, the `async`
flag is kept, and `FuncTypeOk feat t`. -/
structure ValidFuncType (feat : Features) (Γ : Ctx X) (ft : Syntax.FuncType)
    (t : Types.FuncType Nat) : Prop where
  params : ResolveFields Γ ft.params t.params
  result : ResolveOpt Γ ft.result t.result
  async_ : t.async_ = ft.async_
  ok : FuncTypeOk feat t

/-! ## Executable resolution -/

/-- Resolve a `valtype` (wasmparser: "type index {i} is not a defined type"). -/
def resolveVT? (Γ : Ctx X) : Syntax.VT → Except ValidationError (Types.ValType Nat)
  | .prim p => .ok (primType p)
  | .idx i =>
    match Γ.typeSlotAt? i with
    | .error e => .error e
    | .ok s =>
      match s.def_ with
      | .val t => .ok t
      | _ => .error ⟨s!"type index {i} is not a defined type"⟩

/-- Resolve the resource named by `own`/`borrow` (wasmparser: "type index {r} is not a
resource type"). -/
def resolveResource? (Γ : Ctx X) (r : Nat) : Except ValidationError Nat :=
  match Γ.typeSlotAt? r with
  | .error e => .error e
  | .ok s =>
    match s.def_ with
    | .resource v => .ok v
    | _ => .error ⟨s!"type index {r} is not a resource type"⟩

def resolveOpt? (Γ : Ctx X) :
    Option Syntax.VT → Except ValidationError (Option (Types.ValType Nat))
  | none => .ok none
  | some v =>
    match resolveVT? Γ v with
    | .error e => .error e
    | .ok t => .ok (some t)

def resolveFields? (Γ : Ctx X) :
    List (String × Syntax.VT) → Except ValidationError (List (String × Types.ValType Nat))
  | [] => .ok []
  | (n, v) :: fs =>
    match resolveVT? Γ v, resolveFields? Γ fs with
    | .ok t, .ok ts => .ok ((n, t) :: ts)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

def resolveList? (Γ : Ctx X) :
    List Syntax.VT → Except ValidationError (List (Types.ValType Nat))
  | [] => .ok []
  | v :: vs =>
    match resolveVT? Γ v, resolveList? Γ vs with
    | .ok t, .ok ts => .ok (t :: ts)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

def resolveCases? (Γ : Ctx X) : List (String × Option Syntax.VT) →
    Except ValidationError (List (String × Option (Types.ValType Nat)))
  | [] => .ok []
  | (n, v) :: cs =>
    match resolveOpt? Γ v, resolveCases? Γ cs with
    | .ok t, .ok ts => .ok ((n, t) :: ts)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

/-- Map-key error (descriptive text, not verified against wasmparser). -/
def mapKeyError : ValidationError := ⟨"map key type must be a primitive key type"⟩

/-- Constructor-wise resolution of a `defvaltype`. -/
def resolveDef? (Γ : Ctx X) : Syntax.DefValType → Except ValidationError (Types.ValType Nat)
  | .prim p => .ok (primType p)
  | .record fs =>
    match resolveFields? Γ fs with
    | .ok ts => .ok (.record ts)
    | .error e => .error e
  | .variant cs =>
    match resolveCases? Γ cs with
    | .ok ts => .ok (.variant ts)
    | .error e => .error e
  | .list v =>
    match resolveVT? Γ v with
    | .ok t => .ok (.list t)
    | .error e => .error e
  | .fixedList v n =>
    match resolveVT? Γ v with
    | .ok t => .ok (.fixedList t n)
    | .error e => .error e
  | .tuple vs =>
    match resolveList? Γ vs with
    | .ok ts => .ok (.tuple ts)
    | .error e => .error e
  | .flags ls => .ok (.flags ls)
  | .enum ls => .ok (.enum ls)
  | .option v =>
    match resolveVT? Γ v with
    | .ok t => .ok (.option t)
    | .error e => .error e
  | .result a b =>
    match resolveOpt? Γ a, resolveOpt? Γ b with
    | .ok a', .ok b' => .ok (.result a' b')
    | .error e, _ => .error e
    | .ok _, .error e => .error e
  | .map k v =>
    match resolveVT? Γ k, resolveVT? Γ v with
    | .ok kt, .ok t =>
      match keyOfType? kt with
      | some key => .ok (.map key t)
      | none => .error mapKeyError
    | .error e, _ => .error e
    | .ok _, .error e => .error e
  | .own r =>
    match resolveResource? Γ r with
    | .ok v => .ok (.own v)
    | .error e => .error e
  | .borrow r =>
    match resolveResource? Γ r with
    | .ok v => .ok (.borrow v)
    | .error e => .error e
  | .stream a =>
    match resolveOpt? Γ a with
    | .ok a' => .ok (.stream a')
    | .error e => .error e
  | .future a =>
    match resolveOpt? Γ a with
    | .ok a' => .ok (.future a')
    | .error e => .error e

/-! ## Resolution: executable ↔ relational -/

/-! ## Error messages -/

/-- The first present error, or `fallback`. -/
def firstError (fallback : ValidationError) : List (Option ValidationError) → ValidationError
  | [] => fallback
  | some e :: _ => e
  | none :: es => firstError fallback es

/-- `some ⟨msg⟩` if `b`. -/
def errIf (b : Bool) (msg : String) : Option ValidationError :=
  if b then some ⟨msg⟩ else none

/-- The first label error of a label list, in wasmparser's wording: `{kind} name cannot be
empty`, ``{kind} name `l` is not in kebab case``, ``{kind} name `l` conflicts with previous
{prev} name `p` `` (strong uniqueness via `WIT.canonLabel`). `seen` pairs the canonical form
of each earlier label with its spelling. -/
def labelError (kind prev : String) : List (List Char × String) → List String →
    Option ValidationError
  | _, [] => none
  | seen, l :: ls =>
    if l = "" then some ⟨s!"{kind} name cannot be empty"⟩
    else if !WIT.isLabel l then some ⟨s!"{kind} name `{l}` is not in kebab case"⟩
    else match seen.lookup (WIT.canonLabel l) with
      | some p => some ⟨s!"{kind} name `{l}` conflicts with previous {prev} name `{p}`"⟩
      | none => labelError kind prev ((WIT.canonLabel l, l) :: seen) ls

/-- Feature-gate errors of a resolved type (descriptive texts, not verified against
wasmparser). -/
def gateErrors (feat : Features) (t : Types.ValType Nat) : List (Option ValidationError) :=
  [errIf (ABI.ValType.usesFixedList t && !feat.fixedLists)
      "fixed size lists require the component model fixed size list feature",
   errIf (ABI.ValType.usesMap t && !feat.map) "maps require the component model map feature",
   errIf (ABI.ValType.usesErrorContext t && !feat.errorContext)
      "`error-context` requires the component model error-context feature",
   errIf (ABI.ValType.usesAsyncValue t && !feat.async_)
      "`stream` and `future` require the component model async feature"]

/-- Node-local shape and label errors of a `defvaltype` (wasmparser wording, except the
fixed-length-zero text). -/
def nodeErrors : Syntax.DefValType → List (Option ValidationError)
  | .record fs =>
    [errIf fs.isEmpty "record type must have at least one field",
     labelError "record field" "field" [] (fs.map (·.1))]
  | .variant cs =>
    [errIf cs.isEmpty "variant type must have at least one case",
     labelError "variant case" "case" [] (cs.map (·.1))]
  | .tuple vs => [errIf vs.isEmpty "tuple type must have at least one type"]
  | .flags ls =>
    [errIf ls.isEmpty "flags must have at least one entry",
     errIf (32 < ls.length) "cannot have more than 32 flags",
     labelError "flag" "flag" [] ls]
  | .enum ls =>
    [errIf ls.isEmpty "enum type must have at least one variant",
     labelError "enum tag" "tag" [] ls]
  | .fixedList _ n => [errIf (n == 0) "fixed size lists must have more than zero elements"]
  | _ => []

/-- Deep errors of a resolved type: `stream<char>` (wasmparser wording), `borrow` in a
`stream`/`future` element (descriptive), and the `elem_size` bound (wasmparser substring
"exceeds maximum byte size"). -/
def deepErrors (t : Types.ValType Nat) : List (Option ValidationError) :=
  [errIf (WIT.ValType.streamChar t) "`stream<char>` is not valid at this time",
   errIf (WIT.ValType.badBorrow false t)
      "`stream` and `future` element types cannot contain a `borrow` type",
   errIf (ABI.ValType.anySub ABI.oversizedNode t) "value type exceeds maximum byte size"]

/-- The error reported for a resolved `defvaltype` that fails `WellFormedCM` or `Gated`.
Only the message; acceptance is decided by `checkDefValType?` on the relational conditions. -/
def explainDefValType (feat : Features) (d : Syntax.DefValType) (t : Types.ValType Nat) :
    ValidationError :=
  firstError ⟨"invalid value type"⟩ (gateErrors feat t ++ nodeErrors d ++ deepErrors t)

/-- The error reported for a resolved function type that fails `FuncTypeOk`. -/
def explainFuncType (feat : Features) (t : Types.FuncType Nat) : ValidationError :=
  let tys := t.params.map (·.2) ++ t.result.toList
  firstError ⟨"invalid function type"⟩
    ([errIf (t.async_ && !feat.async_)
        "async component functions require the component model async feature",
      labelError "function parameter" "parameter" [] (t.params.map (·.1)),
      errIf (t.result.any ABI.containsBorrow) "function result cannot contain a `borrow` type"] ++
     tys.flatMap (gateErrors feat) ++ tys.flatMap deepErrors)

/-! ## Checkers -/

/-- Validate a `defvaltype`, returning its semantic type. Sound and complete for
`ValidDefValType` (`checkDefValType?_iff`). -/
def checkDefValType? (feat : Features) (Γ : Ctx X) (d : Syntax.DefValType) :
    Except ValidationError (Types.ValType Nat) :=
  match resolveDef? Γ d with
  | .error e => .error e
  | .ok t =>
    if ABI.ValType.WellFormedCM t ∧ Gated feat t then .ok t
    else .error (explainDefValType feat d t)

/-- Validate a `functype`, returning its semantic type. Sound and complete for
`ValidFuncType` (`checkFuncType?_iff`). -/
def checkFuncType? (feat : Features) (Γ : Ctx X) (ft : Syntax.FuncType) :
    Except ValidationError (Types.FuncType Nat) :=
  match resolveFields? Γ ft.params, resolveOpt? Γ ft.result with
  | .ok ps, .ok r =>
    let t : Types.FuncType Nat := { params := ps, result := r, async_ := ft.async_ }
    if FuncTypeOk feat t then .ok t else .error (explainFuncType feat t)
  | .error e, _ => .error e
  | .ok _, .error e => .error e

/-! ## Tests -/

/-- The message of an error result (test helper). -/
def errMessage? {α : Type} : Except ValidationError α → Option String
  | .error e => some e.message
  | .ok _ => none

/-- The empty component context (tests). -/
abbrev testCtx0 : Ctx Unit := Ctx.empty .component

/-- Types: `0 = resource 7`, `1 = borrow 0`, `2 = list (borrow 0)`, `3 = u8`. -/
def testCtxRes : Ctx Unit :=
  { testCtx0 with
    types := [⟨.resource 7, 0⟩, ⟨.val (.borrow 7), 1⟩, ⟨.val (.list (.borrow 7)), 2⟩,
    ⟨.val (.prim .u8), 3⟩] }

-- record with duplicate (strongly non-unique) labels
-- borrow in a function result
-- fixed-length lists are gated by 🔧
-- `stream<char>` is rejected even with 🔀
-- `own`/`borrow` must name a resource type; `valtype` indices must name a defined type
end Silmaril.Wasm.Component.Validation

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
variable {X : Type}

/-- `resolveVT?` at a type index: the index names a defined value type. -/
theorem resolveVT?_idx_eq_ok {Γ : Ctx X} {i : Nat} {t : Types.ValType Nat} :
    resolveVT? Γ (.idx i) = .ok t ↔ Γ.type? i = some (.val t) := by
  simp only [resolveVT?, Ctx.typeSlotAt?, Ctx.listAt?, Ctx.type?]
  cases hs : Γ.types[i]? with
  | none => simp
  | some s =>
    cases hd : s.def_ <;> simp [hd]

theorem resolveVT?_eq_ok {Γ : Ctx X} {v : Syntax.VT} {t : Types.ValType Nat} :
    resolveVT? Γ v = .ok t ↔ ResolveVT Γ v t := by
  cases v with
  | prim p =>
    simp only [resolveVT?, Except.ok.injEq]
    constructor
    · rintro rfl; exact .prim p
    · rintro ⟨⟩; rfl
  | idx i =>
    rw [resolveVT?_idx_eq_ok]
    constructor
    · exact ResolveVT.idx
    · rintro ⟨⟩; assumption

/-- A `valtype` resolves to at most one type. -/
theorem ResolveVT.unique {Γ : Ctx X} {v : Syntax.VT} {t t' : Types.ValType Nat}
    (h : ResolveVT Γ v t) (h' : ResolveVT Γ v t') : t = t' := by
  have e : (Except.ok t : Except ValidationError (Types.ValType Nat)) = .ok t' :=
    (resolveVT?_eq_ok.mpr h).symm.trans (resolveVT?_eq_ok.mpr h')
  exact Except.ok.inj e

/-- `resolveOpt?` at a present `valtype`. -/
theorem resolveOpt?_some_eq_ok {Γ : Ctx X} {v : Syntax.VT} {t : Option (Types.ValType Nat)} :
    resolveOpt? Γ (some v) = .ok t ↔ ResolveOpt Γ (some v) t := by
  simp only [resolveOpt?]
  cases h : resolveVT? Γ v with
  | error e =>
    simp only [reduceCtorEq, false_iff]
    intro hr
    cases hr with
    | some h' => exact absurd (h.symm.trans (resolveVT?_eq_ok.mpr h')) (by simp)
  | ok t' =>
    have ht' : ResolveVT Γ v t' := resolveVT?_eq_ok.mp h
    simp only [Except.ok.injEq]
    constructor
    · rintro rfl; exact .some ht'
    · intro hr
      cases hr with
      | some h' => rw [ht'.unique h']

theorem resolveOpt?_eq_ok {Γ : Ctx X} {v : Option Syntax.VT} {t : Option (Types.ValType Nat)} :
    resolveOpt? Γ v = .ok t ↔ ResolveOpt Γ v t := by
  cases v with
  | none =>
    simp only [resolveOpt?, Except.ok.injEq]
    constructor
    · rintro rfl; exact .none
    · rintro ⟨⟩; rfl
  | some v => exact resolveOpt?_some_eq_ok

end Silmaril.Wasm.Component.Validation

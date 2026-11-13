module

public import Silmaril.Wasm.Spec.Basic.Defs
public import Silmaril.Wasm.Component.Reference.Bridge.Defs
public import Silmaril.Wasm.Component.Reference.Defs

@[expose] public section

/-!
# Component signatures and events for the trace-institution format

The component instance of the specification format (`Silmaril.Wasm.Spec.Format`) is over the
**reference** types and values of the Component Model, the copied formalisation of
`definitions.py` (`Silmaril.Wasm.Component.Reference`):

* `CTy`: closed WIT value types `WIT.ClosedType Nat` (resources named by `Nat`);
  `CFn`: a component function type, lists of parameter and result types;
  `CIface := Iface CFn`.
* `RVal`: reference component values (`Reference.Val`); the event payloads are
  `A = List RVal` (arguments) and `R = Outcome` (the reference outcome of a call: `returns r`
  with `r = none` for a cancelled call, `traps`, `deadlocks`, `diverges`).
  `CEvent X = Event (List RVal) Outcome X`.

**Why the reference values.** The reference values cover every WIT type (strings, lists,
flags, handles, streams, futures, error contexts), so one event type serves every stage
below, and a specification is stated in the vocabulary of the ground truth. Silmaril's component
IR (`Silmaril.Wasm.Component`) carries its own values `Silmaril.Wasm.Component.Val`, which embed by
`Reference.toRefVal` (its types by `irTy`); its traces are read through that embedding
(`Silmaril.Wasm.Spec.Component.IR`). Choosing the IR values instead would make lists, strings and
async inexpressible.

**Stages** (`CTy.level`): the user-visible type fragments, by the least stage that
needs them:

| level | types | needs |
|---|---|---|
| `0` (`Level.scalar`) | `bool`, integers, floats, `char` | flat canonical ABI |
| `1` (`Level.aggregate`) | `record`, `tuple`, `variant`, `enum`, `option`, `result`, `flags` | flat ABI with joins |
| `2` (`Level.memory`) | `string`, `list`, `fixed-list`, `map` | linear memory and `realloc` |
| `3` (`Level.async`) | `own`, `borrow`, `stream`, `future`, `error-context` | handle tables, the async ABI |

A type's level is the maximum over its components. `CFn.level` and `CIface.level` take
maxima. Silmaril's IR covers levels `0` and `1` (`irTy_level`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Spec.Component

open Silmaril.Wasm.Component (WIT.ValType WIT.Primitive)

/-! ## Types -/

/-- Closed WIT value types, resources named by `Nat`. -/
abbrev CTy : Type := Silmaril.Wasm.Component.WIT.ClosedType Nat

/-- A component function type. -/
structure CFn where
  /-- Parameter types. -/
  params : List CTy
  /-- Result types. -/
  results : List CTy

/-- Interfaces typed by component function types. -/
abbrev CIface : Type := Iface CFn

/-- Reference component values. -/
abbrev RVal : Type := Silmaril.Wasm.Component.Reference.Val

/-- Reference outcomes of a call. -/
abbrev Outcome : Type := Silmaril.Wasm.Component.Reference.Outcome

/-- Events of component programs. -/
abbrev CEvent (X : CIface) : Type := Event (List RVal) Outcome X

/-! ## Stages -/

-- The stages of component types.
namespace Level
/-- Scalars. -/
abbrev scalar : ℕ := 0
/-- Records, tuples, variants, enums, options, results, flags. -/
abbrev aggregate : ℕ := 1
/-- Strings, lists, maps (linear memory). -/
abbrev memory : ℕ := 2
/-- Handles, streams, futures, error contexts (handle tables and the async ABI). -/
abbrev async : ℕ := 3
end Level

mutual
/-- The stage of a type: the least level whose types it uses. -/
def CTy.level : CTy → ℕ
  | .ref e => nomatch e
  | .prim .string => Level.memory
  | .prim _ => Level.scalar
  | .list t => max Level.memory (CTy.level t)
  | .fixedList t _ => max Level.memory (CTy.level t)
  | .record fs => max Level.aggregate (CTy.levelFields fs)
  | .tuple ts => max Level.aggregate (CTy.levelList ts)
  | .variant cs => max Level.aggregate (CTy.levelCases cs)
  | .enum _ => Level.aggregate
  | .flags _ => Level.aggregate
  | .option t => max Level.aggregate (CTy.level t)
  | .result a b => max Level.aggregate (max (CTy.levelOpt a) (CTy.levelOpt b))
  | .map _ t => max Level.memory (CTy.level t)
  | .own _ => Level.async
  | .borrow _ => Level.async
  | .future t => max Level.async (CTy.levelOpt t)
  | .stream t => max Level.async (CTy.levelOpt t)
  | .errorContext => Level.async

/-- The level of record fields. -/
def CTy.levelFields : List (String × CTy) → ℕ
  | [] => 0
  | (_, t) :: fs => max (CTy.level t) (CTy.levelFields fs)

/-- The level of a list of types. -/
def CTy.levelList : List CTy → ℕ
  | [] => 0
  | t :: ts => max (CTy.level t) (CTy.levelList ts)

/-- The level of variant cases. -/
def CTy.levelCases : List (String × Option CTy) → ℕ
  | [] => 0
  | (_, t) :: cs => max (CTy.levelOpt t) (CTy.levelCases cs)

/-- The level of an optional type. -/
def CTy.levelOpt : Option CTy → ℕ
  | none => 0
  | some t => (CTy.level t)
end

/-- The level of a function type. -/
def CFn.level (f : CFn) : ℕ := max (CTy.levelList f.params) (CTy.levelList f.results)

/-- The level of a list of function types. -/
def CFn.levelList : List CFn → ℕ
  | [] => 0
  | f :: fs => max f.level (CFn.levelList fs)

/-- The level of an interface. -/
def CIface.level (X : CIface) : ℕ := max (CFn.levelList X.imports) (CFn.levelList X.exports)

/-! ## The IR's types as reference types -/

open Silmaril.Wasm.Component (ValTy FuncTy) in
mutual
/-- The reference type of an IR value type: record fields are labelled `f, fx, …` and variant
cases `c, cx, …` (as in `Reference.Simple.toRef`). -/
def irTy : ValTy → CTy
  | .bool => .prim .bool
  | .s8 => .prim .s8
  | .u8 => .prim .u8
  | .s16 => .prim .s16
  | .u16 => .prim .u16
  | .s32 => .prim .s32
  | .u32 => .prim .u32
  | .s64 => .prim .s64
  | .u64 => .prim .u64
  | .f32 => .prim .f32
  | .f64 => .prim .f64
  | .char => .prim .char
  | .record ts => .record (irFields 0 ts)
  | .variant cs => .variant (irCases 0 cs)

/-- `irTy` on record fields, labelled from `n`. -/
def irFields : ℕ → List ValTy → List (String × CTy)
  | _, [] => []
  | n, t :: ts => (Silmaril.Wasm.Component.Reference.tag "f" n, irTy t) :: irFields (n + 1) ts

/-- `irTy` on lists. -/
def irTys : List ValTy → List CTy
  | [] => []
  | t :: ts => irTy t :: irTys ts

/-- `irTy` on variant cases, labelled from `n`. -/
def irCases : ℕ → List (Option ValTy) → List (String × Option CTy)
  | _, [] => []
  | n, c :: cs => (Silmaril.Wasm.Component.Reference.tag "c" n, irOpt c) :: irCases (n + 1) cs

/-- `irTy` on optional payloads. -/
def irOpt : Option ValTy → Option CTy
  | none => none
  | some t => some (irTy t)
end

/-- The reference function type of an IR function type. -/
def irFn (ft : Silmaril.Wasm.Component.FuncTy) : CFn := ⟨irTys ft.params, irTys ft.results⟩

/-- The component interface of an IR component: its imports and its exports, typed. -/
def cface {M : Type} (c : Silmaril.Wasm.Component.Comp M) : CIface :=
  ⟨c.imports.map fun p => irFn p.2, c.exports.map fun x => irFn x.ty⟩

/-! ## Typing of values -/

/-- Values of the given types (pointwise, same length): the reference typing relation. -/
def Typed (ts : List CTy) (vs : List RVal) : Prop :=
  List.Forall₂ (fun t v => Silmaril.Wasm.Component.Value.Val.HasType v t) ts vs

end Silmaril.Wasm.Spec.Component

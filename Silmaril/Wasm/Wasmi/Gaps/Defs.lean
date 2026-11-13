module

public import Silmaril.Wasm.Wasmi.Observed.Defs

/-!
# The version gaps of wasmi 2.0.0: modules Wasm 3.0 accepts and wasmi refuses

A local probe (a throwaway crate over the cargo registry's `wasmi = "=0.40.0"`,
`wasmi = "=2.0.0"` with features `std`, `validate`, `stable`, `auto-dispatch`, `memory64`, and
`wast = "=263.0.0"`; not committed) compiled every `module` directive of the vendored testsuite
(`tests/wasm-conformance/wast/`, 497 modules) with `Module::new` of both versions. Both refuse
exactly the same 38 modules, with the same messages; wasmi 2.0.0's `Config` has no switch for
any of these proposals (it has switches for tail calls, extended constants, SIMD, and others
that are already on). The refusals fall into seven classes, `Gap`:

* `constGlobal`, "constant expression required: global.get of locally defined global":
  `global:373-374`, `data:89-90`, `elem:178,182`;
* `nonNull`, "function references required for non-nullable types": `elem:87,315,448-578`,
  `linking:96,112`, `local_init:3,66`, `unreached-valid:82`;
* `typedRef`, "function references required for index reference types": `br_table:3`,
  `linking:426,434`, `ref_is_null:1,71`;
* `gcHeap`, "heap types not supported without the gc feature": `ref_null:1,23`;
* `tableInit`, "tables with expression initializers require the function-references
  proposal": `global:634`;
* `exceptions`, "exceptions proposal not enabled": `imports:3,35`;
* `funcRefInstr`, "function references support is not enabled": `unreached-valid:1`.

`hasGap k m` is a syntactic check of class `k` (a sufficient condition for wasmi's refusal,
modelled on the messages and checked against the probe on the witnesses below, not derived
from wasmi's source). `instantiate200?` is **wasmi 2.0.0's instantiation** on this model: it
refuses a module with any gap, and otherwise is `Observed.instantiate?` (whose only refusal is
`constGlobal`). `witness k` is a small module with the gap, modelled on the testsuite lines:

* `constGlobal`: `Observed.gapMod`, `(global i32 (i32.const 0)) (global i32 (global.get 0))`;
* `nonNull`: `(func (param (ref extern)))`;
* `typedRef`: `(type $t (func)) (func (param (ref null $t)))`;
* `gcHeap`: `(func (result anyref) (ref.null any))`;
* `tableInit`: `(func $f) (table 1 funcref (ref.func $f))`;
* `exceptions`: `(tag)`;
* `funcRefInstr`: `(func (param funcref) (drop (ref.as_non_null (local.get 0))))`.

The probe refuses each of the seven with the message of its class, in both versions, and accepts
the control module `(func (param funcref) (result funcref) (local.get 0)) (table 1 funcref)
(global funcref (ref.null func))`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.Gaps

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The classes of modules that wasmi 2.0.0 (and 0.40.0) refuses and Wasm 3.0 accepts. -/
inductive Gap where
  | constGlobal | nonNull | typedRef | gcHeap | tableInit | exceptions | funcRefInstr
  deriving DecidableEq, Repr

/-- All seven classes. -/
def allGaps : List Gap :=
  [.constGlobal, .nonNull, .typedRef, .gcHeap, .tableInit, .exceptions, .funcRefInstr]

mutual
/-- Some instruction, also inside a structured body, satisfies `p`. -/
def anyI (p : Instr → Bool) : Instr → Bool
  | .block bt b => p (.block bt b) || anyIs p b
  | .loop bt b => p (.loop bt b) || anyIs p b
  | .tryTable bt cs b => p (.tryTable bt cs b) || anyIs p b
  | .if_ bt b₁ b₂ => p (.if_ bt b₁ b₂) || anyIs p b₁ || anyIs p b₂
  | i => p i

/-- Some instruction of the sequence, also inside a structured body, satisfies `p`. -/
def anyIs (p : Instr → Bool) : List Instr → Bool
  | [] => false
  | i :: is => anyI p i || anyIs p is
end

/-- Every expression of a module: function bodies, global and table initialisers, element
expressions and offsets, data offsets. -/
def exprs (m : Module) : List Expr :=
  m.funcs.map (·.body) ++ m.globals.map (·.init) ++ m.tables.map (·.init) ++
    m.elems.flatMap (fun e => e.init ++ match e.mode with | .active _ o => [o] | _ => []) ++
    m.data.filterMap (fun d => match d.mode with | .active _ o => some o | _ => none)

/-- Some instruction of the module satisfies `p`. -/
def anyInstr (p : Instr → Bool) (m : Module) : Bool := (exprs m).any (anyIs p)

/-- The value types of a module's declarations: function type parameters and results, function
locals, global types (defined and imported). -/
def valTypes (m : Module) : List ValType :=
  (m.typeDefinitions.flatMap fun st => match st.body with
    | .func ft => ft.params ++ ft.results
    | _ => []) ++
  m.funcs.flatMap (·.locals) ++ m.globals.map (·.type.value) ++
  m.imports.flatMap (fun i => match i.type with | .global g => [g.value] | _ => [])

/-- The reference types of a value type. -/
def refOf : ValType → List RefType
  | .ref r => [r]
  | _ => []

/-- The reference types an instruction names directly (block types, typed `select`, casts). -/
def instrRefs : Instr → List RefType
  | .block (.value t) _ | .loop (.value t) _ | .if_ (.value t) _ _ | .tryTable (.value t) _ _ =>
      refOf t
  | .select (some ts) => ts.flatMap refOf
  | .refTest r | .refCast r => [r]
  | .brOnCast _ r₁ r₂ | .brOnCastFail _ r₁ r₂ => [r₁, r₂]
  | _ => []

/-- The reference types of a module's declarations: of its value types, its tables (defined and
imported) and its element segments. -/
def refTypes (m : Module) : List RefType :=
  (valTypes m).flatMap refOf ++ m.tables.map (·.type.element) ++ m.elems.map (·.type) ++
  m.imports.flatMap (fun i => match i.type with | .table t => [t.element] | _ => [])

/-- A heap type wasmi supports: `func` or `extern`. -/
def heapOk : HeapType → Bool
  | .abstract .func | .abstract .extern => true
  | _ => false

/-- An abstract heap type (with `heapOk` false: `any`, `eq`, `i31`, `struct`, `array`, `none`,
`nofunc`, `exn`, `noexn`, `noextern`, which wasmi does not support). -/
def absHeap : HeapType → Bool
  | .abstract _ => true
  | .typeIdx _ => false

/-- An instruction of the GC proposal. -/
def gcInstr : Instr → Bool
  | .refEq | .refTest _ | .refCast _ | .brOnCast .. | .brOnCastFail .. | .refI31 | .i31Get _
  | .structNew _ | .structNewDefault _ | .structGet .. | .structSet .. | .arrayNew _
  | .arrayNewDefault _ | .arrayNewFixed .. | .arrayNewData .. | .arrayNewElem .. | .arrayGet ..
  | .arraySet _ | .arrayLen | .arrayFill _ | .arrayCopy .. | .arrayInitData .. | .arrayInitElem ..
  | .externConvertAny | .anyConvertExtern => true
  | _ => false

/-- An instruction of the exception-handling proposal. -/
def excInstr : Instr → Bool
  | .throw _ | .throwRef | .tryTable .. => true
  | _ => false

/-- An instruction of the typed function references proposal. -/
def funcRefB : Instr → Bool
  | .callRef _ | .returnCallRef _ | .brOnNull _ | .brOnNonNull _ | .refAsNonNull => true
  | _ => false

/-- A table initialiser other than the default `ref.null`. -/
def tableInitB (e : Expr) : Bool :=
  match e with
  | [.refNull _] => false
  | _ => true

/-- **The gap classes, as checks on modules.** -/
def hasGap : Gap → Module → Bool
  | .constGlobal, m => !Observed.ConstOk m
  | .nonNull, m =>
      (refTypes m).any (!·.nullable) || anyInstr (fun i => (instrRefs i).any (!·.nullable)) m
  | .typedRef, m =>
      (refTypes m).any (fun r => match r.heap with | .typeIdx _ => true | _ => false) ||
      anyInstr (fun i => match i with
        | .refNull (.typeIdx _) => true
        | i => (instrRefs i).any fun r => match r.heap with | .typeIdx _ => true | _ => false) m
  | .gcHeap, m =>
      (refTypes m).any (fun r => absHeap r.heap && !heapOk r.heap) ||
      m.typeDefinitions.any (fun st => match st.body with | .func _ => false | _ => true) ||
      anyInstr (fun i => gcInstr i || match i with
        | .refNull h => absHeap h && !heapOk h
        | i => (instrRefs i).any fun r => absHeap r.heap && !heapOk r.heap) m
  | .tableInit, m => m.tables.any (fun t => tableInitB t.init)
  | .exceptions, m =>
      !m.tags.isEmpty || m.imports.any (fun i => match i.type with | .tag _ => true | _ => false) ||
      anyInstr excInstr m
  | .funcRefInstr, m => anyInstr funcRefB m

/-- wasmi 2.0.0 refuses the module: it has some gap. -/
def refuses (m : Module) : Bool := allGaps.any (hasGap · m)

/-- **wasmi 2.0.0's instantiation**, on this model: refuse a module with a gap, otherwise
`Observed.instantiate?`. -/
def instantiate200? (s : Store Empty) (m : Module) : Option (Config Empty × Option FuncIdx) :=
  if refuses m then none else Observed.instantiate? s m

/-! ## The witnesses -/

/-- `(ref extern)`. -/
abbrev refExtern : ValType := .ref ⟨false, .abstract .extern⟩

/-- `funcref`. -/
abbrev funcref : ValType := .ref ⟨true, .abstract .func⟩

/-- A one-member recursion group with the function type `ps → rs`. -/
abbrev fty (ps rs : List ValType) : RecType := ⟨[⟨true, [], .func ⟨ps, rs⟩⟩]⟩

/-- `(func (param (ref extern)))` (`local_init.wast:3`). -/
def nonNullMod : Module where
  types := [fty [refExtern] []]
  funcs := [⟨⟨0⟩, [], []⟩]

/-- `(type $t (func)) (func (param (ref null $t)))` (`ref_is_null.wast:1`). -/
def typedRefMod : Module where
  types := [fty [] [], fty [.ref ⟨true, .typeIdx ⟨0⟩⟩] []]
  funcs := [⟨⟨1⟩, [], []⟩]

/-- `(func (result anyref) (ref.null any))` (`ref_null.wast:1`). -/
def gcHeapMod : Module where
  types := [fty [] [.ref ⟨true, .abstract .any⟩]]
  funcs := [⟨⟨0⟩, [], [.refNull (.abstract .any)]⟩]

/-- `(func $f) (table 1 funcref (ref.func $f))` (`global.wast:634`). -/
def tableInitMod : Module where
  types := [fty [] []]
  funcs := [⟨⟨0⟩, [], []⟩]
  tables := [⟨⟨.i32, ⟨1, none⟩, ⟨true, .abstract .func⟩⟩, [.refFunc ⟨0⟩]⟩]

/-- `(tag)` (`imports.wast:3`). -/
def exceptionsMod : Module where
  types := [fty [] []]
  tags := [⟨0⟩]

/-- `(func (param funcref) (drop (ref.as_non_null (local.get 0))))` (`unreached-valid.wast:1`). -/
def funcRefInstrMod : Module where
  types := [fty [funcref] []]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .refAsNonNull, .drop]⟩]

/-- The control module, which the probe accepts in both versions:
`(func (param funcref) (result funcref) (local.get 0)) (table 1 funcref)
(global funcref (ref.null func))`. -/
def controlMod : Module where
  types := [fty [funcref] [funcref]]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩]⟩]
  tables := [⟨⟨.i32, ⟨1, none⟩, ⟨true, .abstract .func⟩⟩, [.refNull (.abstract .func)]⟩]
  globals := [⟨⟨.const, funcref⟩, [.refNull (.abstract .func)]⟩]

/-- **The witness of each gap.** -/
def witness : Gap → Module
  | .constGlobal => Observed.gapMod
  | .nonNull => nonNullMod
  | .typedRef => typedRefMod
  | .gcHeap => gcHeapMod
  | .tableInit => tableInitMod
  | .exceptions => exceptionsMod
  | .funcRefInstr => funcRefInstrMod

end Silmaril.Wasm.Wasmi.Gaps

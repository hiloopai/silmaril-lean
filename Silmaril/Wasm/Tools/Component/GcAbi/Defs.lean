module

public import Silmaril.Wasm.Component.Conformance.DecodeGC.Defs
public import Silmaril.Wasm.Component.RefValid.Defs

/-!
# 🛸 The GC canonical ABI of wasmparser 1.262.0

With the 🛸 canonical option `gc`, component values cross a `canon lift` or `canon lower` as
WebAssembly GC values instead of through linear memory. wasmparser 1.262.0 checks the core
function type of such a definition against the component function type with `lower_gc`
(`crates/wasmparser/src/validator/component_types.rs`, `ComponentFuncType::lower_gc` and the
`lower_gc` of each value type), and the options with `check_options`, `check_lift` and
`check_lower` (`component.rs`). The copied reference validator has no GC ABI, so this module
adds it on top of the reference's fold:

* **`Lowers enc t s`** (the specification, a relation): the component value type `t` lowers
  to the core argument or struct/array field `s` (wasmparser's `ArgOrField`) under string
  encoding `enc`. `bool`, `s8`, `u8` go to a packed `i8` field or an `i32` argument; `s16`,
  `u16` to a packed `i16` field or an `i32` argument; `s32`, `u32`, `char`, `enum`, `flags`
  to `i32`; `s64`, `u64` to `i64`; `f32`, `f64` to themselves; `string` to a reference to an
  array of packed `i8` (`utf8`, `latin1+utf16`) or `i16` (`utf16`); `list` and fixed-length
  lists to a reference to an array whose element the element type lowers to; `record` and
  `tuple` to a reference to a struct with one field per member, each lowered; `variant`,
  `option`, `result` to a reference to the empty struct; `own`, `borrow`, `future`, `stream`,
  `error-context` to a reference to `extern`. `map` has no GC lowering in 1.262.0.
* **`ok`**: the executable check, sound for `Lowers` (`GcAbi.Thms`, `ok_sound`).
* **`FuncLowers enc ft d`**: the core function type `d` has one parameter per parameter of
  `ft`, each lowered, and one result iff `ft` has one, lowered.
* **`LiftOk`/`LowerOk`**: the conditions of a `canon lift` / `canon lower` with 🛸 options:
  `gc` exactly once; for `lift`, no `core-type` (the callee's type is the core type), the
  post-return function takes the callee's results; for `lower`, exactly one `core-type`, naming
  a core function type, which becomes the type of the new core function; the other options
  valid by the reference's `ValidCanonOpts`; and `FuncLowers`.
* **`GDef`**: a definition of a component as the `BinaryGC` decoder reads it, with the
  🛸 `lift`/`lower` kept apart (`erase`); **`gDefs?`** folds them, running the reference's
  `checkDef?` on every other definition, and **`GValidDefs`** is its relation
  (`gDefs?_sound`).
* **Value exports** (`fixExport`): wasmparser marks the value an `export` of a value creates
  as used; the copied reference leaves it unconsumed and then rejects the component, so the
  fold marks it consumed after the reference's step (`Validate` runs the fold for every
  component that exports a value).

Not covered: wasmparser's `exact` heap types (custom descriptors, not in the closed types)
and `shared` abstract heap types (the closed types have no `shared` flag); the error messages
follow wasmparser's wording but print the core types in a simplified form.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.GcAbi

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Validation
open Silmaril.Wasm.Validation (Ty DefType CValType CStorageType CCompType CHeapType)

/-- Semantic value types. -/
abbrev VT := Types.ValType Nat

/-- Semantic function types. -/
abbrev FT := Types.FuncType Nat

/-! ## Lowering a value type -/

/-- wasmparser's `ArgOrField`: a core function parameter or result, or a struct or array
field's storage type. -/
inductive Slot where
  | arg (t : CValType)
  | field (s : CStorageType)
  deriving DecidableEq, Repr

/-- `i32`. -/
abbrev i32 : CValType := .num (.int .i32)

namespace Slot

/-- `ArgOrField::as_val_type`. -/
def val? : Slot → Option CValType
  | .arg t => some t
  | .field (.val t) => some t
  | .field _ => none

/-- The composite type of a concrete reference (`as_concrete_ref`, then `types[id]`). -/
def concrete? (s : Slot) : Option CCompType :=
  match s.val? with
  | some (.refv (.ref _ (.use (.dt d)))) => Silmaril.Wasm.Validation.DefType.expand? d
  | _ => none

/-- A reference to `extern`, nullable or not. -/
def IsExtern (s : Slot) : Prop := ∃ n, s.val? = some (.refv (.ref n (.abs .extern)))

instance (s : Slot) : Decidable s.IsExtern :=
  match h : s.val? with
  | some (.refv (.ref n (.abs .extern))) => isTrue ⟨n, h⟩
  | none => isFalse fun ⟨_, e⟩ => by simp_all
  | some (.num _) | some (.vec _) | some .botv => isFalse fun ⟨_, e⟩ => by simp_all
  | some (.refv (.ref _ .bot)) | some (.refv (.ref _ (.use _))) =>
    isFalse fun ⟨_, e⟩ => by simp_all
  | some (.refv (.ref _ (.abs a))) =>
    if ha : a = .extern then isTrue (by subst ha; exact ⟨_, h⟩)
    else isFalse fun ⟨_, e⟩ => by simp_all

end Slot

/-- The element storage type a string lowers to, by encoding. -/
def strElem : ABI.StringEncoding → CStorageType
  | .utf8 | .latin1Utf16 => .pack .i8
  | .utf16 => .pack .i16

/-- The core number type of a primitive lowered to one number (`none`: the small integers,
which also fit a packed field, and `string`). -/
def primNum? : WIT.Primitive → Option Silmaril.Wasm.NumType
  | .s32 | .u32 | .char => some (.int .i32)
  | .s64 | .u64 => some (.int .i64)
  | .f32 => some (.float .f32)
  | .f64 => some (.float .f64)
  | _ => none

/-- The packed type a small integer also lowers to as a field (`bool`, `s8`, `u8`: `i8`;
`s16`, `u16`: `i16`). -/
def primPack? : WIT.Primitive → Option Silmaril.Wasm.PackType
  | .bool | .s8 | .u8 => some .i8
  | .s16 | .u16 => some .i16
  | _ => none

/-- `variant`, `option` and `result`: lowered to a reference to the empty struct. -/
def IsSum : VT → Prop
  | .variant _ | .option _ | .result _ _ => True
  | _ => False

/-- `enum` and `flags`: lowered to `i32`. -/
def IsBits : VT → Prop
  | .enum _ | .flags _ => True
  | _ => False

/-- Handles, `future`, `stream`, `error-context`: lowered to a reference to `extern`. -/
def IsHandle : VT → Prop
  | .own _ | .borrow _ | .future _ | .stream _ | .errorContext => True
  | _ => False

mutual
/-- **`lower_gc`, the specification**: the component value type lowers to the slot. -/
inductive Lowers (enc : ABI.StringEncoding) : VT → Slot → Prop
  /-- A small integer to its packed field or an `i32` argument. -/
  | small {p : WIT.Primitive} {k : Silmaril.Wasm.PackType} {s : Slot}
      (hk : primPack? p = some k) (hs : s = .field (.pack k) ∨ s = .arg i32) :
      Lowers enc (.prim p) s
  /-- A number primitive to its core number type. -/
  | num {p : WIT.Primitive} {n : Silmaril.Wasm.NumType} {s : Slot}
      (hn : primNum? p = some n) (hs : s.val? = some (.num n)) : Lowers enc (.prim p) s
  /-- `string` to a reference to an array of the encoding's code units. -/
  | string {s : Slot} {m : Silmaril.Wasm.Mutability}
      (hs : s.concrete? = some (.array (.field m (strElem enc)))) :
      Lowers enc (.prim .string) s
  /-- `list` to a reference to an array of its lowered elements. -/
  | list {e : VT} {s : Slot} {m : Silmaril.Wasm.Mutability} {st : CStorageType}
      (hs : s.concrete? = some (.array (.field m st))) (he : Lowers enc e (.field st)) :
      Lowers enc (.list e) s
  /-- A fixed-length list, as `list`. -/
  | fixedList {e : VT} {n : Nat} {s : Slot} {m : Silmaril.Wasm.Mutability} {st : CStorageType}
      (hs : s.concrete? = some (.array (.field m st))) (he : Lowers enc e (.field st)) :
      Lowers enc (.fixedList e n) s
  /-- `record` to a reference to a struct of its lowered fields. -/
  | record {fs : List (String × VT)} {s : Slot} {cs : Ty (.list .field)}
      (hs : s.concrete? = some (.struct cs)) (hf : Fields enc (fs.map (·.2)) cs.toList) :
      Lowers enc (.record fs) s
  /-- `tuple` to a reference to a struct of its lowered members. -/
  | tuple {ts : List VT} {s : Slot} {cs : Ty (.list .field)}
      (hs : s.concrete? = some (.struct cs)) (hf : Fields enc ts cs.toList) :
      Lowers enc (.tuple ts) s
  /-- `variant`, `option`, `result` to a reference to the empty struct. -/
  | sum {t : VT} {s : Slot} (ht : IsSum t) (hs : s.concrete? = some (.struct .nil)) :
      Lowers enc t s
  /-- `enum`, `flags` to `i32`. -/
  | bits {t : VT} {s : Slot} (ht : IsBits t) (hs : s.val? = some i32) : Lowers enc t s
  /-- Handles, `future`, `stream`, `error-context` to a reference to `extern`. -/
  | handle {t : VT} {s : Slot} (ht : IsHandle t) (hs : s.IsExtern) : Lowers enc t s

/-- Members lower to the struct's fields, one by one. -/
inductive Fields (enc : ABI.StringEncoding) : List VT → List (Ty .field) → Prop
  | nil : Fields enc [] []
  | cons {t : VT} {ts : List VT} {m : Silmaril.Wasm.Mutability} {st : CStorageType}
      {cs : List (Ty .field)} (h : Lowers enc t (.field st)) (hs : Fields enc ts cs) :
      Fields enc (t :: ts) (.field m st :: cs)
end

/-- The primitive rules, executable. -/
def primOk (enc : ABI.StringEncoding) (p : WIT.Primitive) (s : Slot) : Bool :=
  match primPack? p, primNum? p with
  | some k, _ => decide (s = .field (.pack k) ∨ s = .arg i32)
  | none, some n => decide (s.val? = some (.num n))
  | none, none =>
    match p, s.concrete? with
    | .string, some (.array (.field _ st)) => decide (st = strElem enc)
    | _, _ => false

/-- Continue with the element storage type of an array. -/
def onArray (c : Option CCompType) (k : CStorageType → Bool) : Bool :=
  match c with
  | some (.array (.field _ st)) => k st
  | _ => false

/-- Continue with the fields of a struct. -/
def onStruct (c : Option CCompType) (k : List (Ty .field) → Bool) : Bool :=
  match c with
  | some (.struct cs) => k cs.toList
  | _ => false

mutual
/-- **`lower_gc`, executable** (sound for `Lowers`: `ok_sound`). -/
def ok (enc : ABI.StringEncoding) : VT → Slot → Bool
  | .prim p, s => primOk enc p s
  | .ref r, _ => nomatch r
  | .list e, s => onArray s.concrete? fun st => ok enc e (.field st)
  | .fixedList e _, s => onArray s.concrete? fun st => ok enc e (.field st)
  | .record fs, s => onStruct s.concrete? fun cs => recOk enc fs cs
  | .tuple ts, s => onStruct s.concrete? fun cs => tupOk enc ts cs
  | .variant _, s | .option _, s | .result _ _, s => decide (s.concrete? = some (.struct .nil))
  | .enum _, s | .flags _, s => decide (s.val? = some i32)
  | .map _ _, _ => false
  | .own _, s | .borrow _, s | .future _, s | .stream _, s | .errorContext, s => decide s.IsExtern

/-- Record fields against struct fields. -/
def recOk (enc : ABI.StringEncoding) : List (String × VT) → List (Ty .field) → Bool
  | [], [] => true
  | (_, t) :: fs, .field _ st :: cs => ok enc t (.field st) && recOk enc fs cs
  | _, _ => false

/-- Tuple members against struct fields. -/
def tupOk (enc : ABI.StringEncoding) : List VT → List (Ty .field) → Bool
  | [], [] => true
  | t :: ts, .field _ st :: cs => ok enc t (.field st) && tupOk enc ts cs
  | _, _ => false
end

/-! ## Function types -/

/-- The parameters and results of a core function type. -/
def funcSig? (d : DefType) : Option (List CValType × List CValType) :=
  match Silmaril.Wasm.Validation.DefType.expand? d with
  | some (.func ps rs) => some (ps.toList, rs.toList)
  | _ => none

/-- The result lowers: none for none, one for one. -/
def ResultLowers (enc : ABI.StringEncoding) : Option VT → List CValType → Prop
  | none, [] => True
  | some t, [r] => Lowers enc t (.arg r)
  | _, _ => False

/-- **`ComponentFuncType::lower_gc`**: the core function type `d` has one parameter per
parameter of `ft` and one result iff `ft` has one, each lowered. -/
structure FuncLowers (enc : ABI.StringEncoding) (ft : FT) (d : DefType) : Prop where
  sig : ∃ ps rs, funcSig? d = some (ps, rs) ∧ (ft.params.map (·.2)).length = ps.length ∧
    (∀ p ∈ (ft.params.map (·.2)).zip ps, Lowers enc p.1 (.arg p.2)) ∧ ResultLowers enc ft.result rs

/-- `FuncLowers`, executable. -/
def funcOk (enc : ABI.StringEncoding) (ft : FT) (d : DefType) : Bool :=
  match funcSig? d with
  | some (ps, rs) =>
    let ts := ft.params.map (·.2)
    ts.length == ps.length && (ts.zip ps).all (fun p => ok enc p.1 (.arg p.2)) &&
      match ft.result, rs with
      | none, [] => true
      | some t, [r] => ok enc t (.arg r)
      | _, _ => false
  | none => false

/-! ## Options and the two definitions -/

/-- The options the reference knows (`gc` and `core-type` dropped). -/
def v0 (os : List BinaryGC.CanonOpt) : List Syntax.CanonOpt := os.filterMap ToRefGC.canonOpt

/-- The `core-type` indices among the options. -/
def coreTypes (os : List BinaryGC.CanonOpt) : List Nat :=
  os.filterMap fun | .coreType t => some t | _ => none

/-- How often `gc` occurs. -/
def gcCount (os : List BinaryGC.CanonOpt) : Nat := os.countP (· == .gc)

/-- The closed defined type of a core function (`none`: not a function). -/
def coreFuncDef? (Γ : Ctx Core3Extern) (f : Nat) : Option DefType :=
  match Γ.coreFunc? f with
  | some x => match x.1 with
    | .func d => some d
    | _ => none
  | none => none

/-- The closed defined type of core type `i`, if it is a function type. -/
def coreTypeFunc? (Γ : Ctx Core3Extern) (i : Nat) : Option DefType :=
  match Γ.coreType? i with
  | some (.rec_ _ _ d) => if (funcSig? d).isSome then some d else none
  | _ => none

/-- The reference's core view of the Core 3.0 profile. -/
abbrev V3 : CoreView Core3Extern := core3Profile.view.core

/-- **`canon lift` with 🛸 options** (wasmparser's `check_options`, `check_lift`,
`lower_gc`): the callee has the core function type `d`, which lowers `ft`. -/
structure LiftOk (feat : Features) (Γ : Ctx Core3Extern) (callee : Nat)
    (os : List BinaryGC.CanonOpt) (ft : FT) : Prop where
  gc : gcCount os = 1
  noCoreType : coreTypes os = []
  opts : ValidCanonOpts feat V3 Γ .lift ft (v0 os)
  callee : ∃ d, coreFuncDef? Γ callee = some d ∧ FuncLowers (CanonOpts.encoding (v0 os)) ft d ∧
    OptAll (CanonOpts.postReturnIdx? (v0 os)) fun p => ∃ dp rs,
      funcSig? d = some (dp, rs) ∧ (coreFuncDef? Γ p).bind funcSig? = some (rs, [])

/-- **`canon lower` with 🛸 options** (wasmparser's `check_options`, `check_lower`,
`lower_gc`): the `core-type` is a core function type `d` that lowers `ft`; the new core
function has type `x = func d`. -/
structure LowerOk (feat : Features) (Γ : Ctx Core3Extern) (os : List BinaryGC.CanonOpt)
    (ft : FT) (x : Core3Extern) : Prop where
  gc : gcCount os = 1
  coreType : ∃ i d, coreTypes os = [i] ∧ coreTypeFunc? Γ i = some d ∧
    FuncLowers (CanonOpts.encoding (v0 os)) ft d ∧ core3Ext? (.func d) = some x
  opts : ValidCanonOpts feat V3 Γ .lower ft (v0 os)

/-! ### Executable checks (messages in wasmparser's wording) -/

/-- Why a `lift` with 🛸 options fails, if it does. -/
def liftProblem (feat : Features) (Γ : Ctx Core3Extern) (callee : Nat)
    (os : List BinaryGC.CanonOpt) (ft : FT) : Option String :=
  if gcCount os ≠ 1 then some "canonical option `gc` is specified more than once"
  else if coreTypes os ≠ [] then some "canonical option `core-type` is not allowed in `canon lift`"
  else if ¬ ValidCanonOpts feat V3 Γ .lift ft (v0 os) then
    some (CanonOpts.explainCanonOpts feat V3 Γ .lift ft (v0 os)).message
  else match coreFuncDef? Γ callee with
    | none => some s!"core function index {callee} out of bounds"
    | some d =>
      if !funcOk (CanonOpts.encoding (v0 os)) ft d then
        some "lowered component function type does not match the core function type of the \
          `gc` lifting"
      else match CanonOpts.postReturnIdx? (v0 os) with
        | none => none
        | some p =>
          match funcSig? d, (coreFuncDef? Γ p).bind funcSig? with
          | some (_, rs), some pr =>
            if pr = (rs, []) then none
            else some "canonical option `post-return` uses a core function with an incorrect \
              signature"
          | _, _ => some "canonical option `post-return` uses a core function with an incorrect \
              signature"

/-- The new core function's type of a `lower` with 🛸 options, or why it fails. -/
def lowerCheck (feat : Features) (Γ : Ctx Core3Extern) (os : List BinaryGC.CanonOpt)
    (ft : FT) : Except String Core3Extern :=
  if gcCount os ≠ 1 then
    .error (if gcCount os = 0 then "cannot specify `core-type` without `gc`"
      else "canonical option `gc` is specified more than once")
  else match coreTypes os with
    | [] => .error "cannot specify `gc` without also specifying a `core-type` for lowerings"
    | [i] =>
      match coreTypeFunc? Γ i with
      | none => .error "canonical option `core type` must reference a core function type"
      | some d =>
        if ¬ ValidCanonOpts feat V3 Γ .lower ft (v0 os) then
          .error (CanonOpts.explainCanonOpts feat V3 Γ .lower ft (v0 os)).message
        else if !funcOk (CanonOpts.encoding (v0 os)) ft d then
          .error "declared `core-type` does not match the GC lowering of the component \
            function type"
        else match core3Ext? (.func d) with
          | some x => .ok x
          | none => .error "declared `core-type` is not a valid core function type"
    | _ => .error "canonical option `core type` is specified more than once"

/-! ## Definitions and the fold -/

/-- A definition as `BinaryGC` reads it: a reference definition, or a `lift`/`lower` with
🛸 options (kept with all their options), or a nested component. -/
inductive GDef where
  | ref (d : Syntax.Definition Silmaril.Wasm.Module)
  | lift (callee : Nat) (os : List BinaryGC.CanonOpt) (t : Nat)
  | lower (f : Nat) (os : List BinaryGC.CanonOpt)
  | comp (ds : List GDef)
  deriving Inhabited

namespace Erase

/-- One canon: 🛸 `lift`/`lower` apart, the others as `ToRefGC` maps them. -/
def canon : BinaryGC.Canon → Except String GDef
  | .lift f os t => if os.any GcCheck.isGcOpt then .ok (.lift f os t)
      else .ok (.ref (.canon (.lift f (v0 os) t)))
  | .lower f os => if os.any GcCheck.isGcOpt then .ok (.lower f os)
      else .ok (.ref (.canon (.lower f (v0 os))))
  | .p3 c => do pure (.ref (.canon (← ToRefP3.canonRef c)))

mutual
def section_ : BinaryGC.Section → Except String (List GDef)
  | .p3 s => do pure ((← ToRefP3.section_ s).map .ref)
  | .coreTypes xs => .ok (xs.map (.ref ∘ .coreType))
  | .types xs => .ok (xs.map (.ref ∘ .type))
  | .canons xs => xs.mapM canon
  | .component c => do pure [.comp (← ast c)]

def sections : List BinaryGC.Section → Except String (List GDef)
  | [] => .ok []
  | s :: ss => do pure ((← section_ s) ++ (← sections ss))

def ast : BinaryGC.Ast → Except String (List GDef)
  | .mk ss => sections ss
end

end Erase

/-- **The definitions of a `BinaryGC` component**, 🛸 `lift`/`lower` kept apart. -/
def erase (a : BinaryGC.Ast) : Except String (List GDef) := Erase.ast a

mutual
/-- The reference syntax of a definition (🛸 options dropped, as `ToRefGC`). -/
def GDef.toRef : GDef → Syntax.Definition Silmaril.Wasm.Module
  | .ref d => d
  | .lift f os t => .canon (.lift f (v0 os) t)
  | .lower f os => .canon (.lower f (v0 os))
  | .comp ds => .component (GDef.toRefs ds)

def GDef.toRefs : List GDef → List (Syntax.Definition Silmaril.Wasm.Module)
  | [] => []
  | d :: ds => d.toRef :: GDef.toRefs ds
end

mutual
/-- Does a definition list hold a 🛸 `lift`/`lower`? -/
def GDef.hasGc : GDef → Bool
  | .ref _ => false
  | .lift _ _ _ | .lower _ _ => true
  | .comp ds => GDef.hasGcs ds

def GDef.hasGcs : List GDef → Bool
  | [] => false
  | d :: ds => d.hasGc || GDef.hasGcs ds
end

/-! ## 🪙 value exports

wasmparser marks the value an `export` of a value creates as used (`add_entity` with
`ExternKind::Export`: `value_used = true`); the copied reference pushes it unconsumed
(`DState.exportItem`), so its `ComponentDone` rejects every component that exports a value
(`value index i was not used …`). The fold below marks it consumed after the reference's step
(`fixExport`). -/

/-- After a reference step `s → s'` of `d`: an `export` of a value marks the new value
consumed. -/
def fixExport (s : DefState Core3Extern) (d : Syntax.Definition Silmaril.Wasm.Module)
    (s' : DefState Core3Extern) : DefState Core3Extern :=
  match d with
  | .export_ _ ⟨.value, _⟩ _ =>
    if s'.ctx.values.length = s.ctx.values.length + 1 then
      match s'.ctx.values.getLast? with
      | some (t, _) =>
        { s' with st := s'.st.withCtx (consumedAt s'.ctx (s'.ctx.values.length - 1) t) }
      | none => s'
    else s'
  | _ => s'

mutual
/-- Does a definition export a value (here or in a nested component)? -/
def exportsValue : Syntax.Definition Silmaril.Wasm.Module → Bool
  | .export_ _ ⟨.value, _⟩ _ => true
  | .component ds => exportsValues ds
  | _ => false

def exportsValues : List (Syntax.Definition Silmaril.Wasm.Module) → Bool
  | [] => false
  | d :: ds => exportsValue d || exportsValues ds
end

mutual
/-- A reference definition as a `GDef` (nested components as `comp`). -/
def GDef.ofRef : Syntax.Definition Silmaril.Wasm.Module → GDef
  | .component ds => .comp (GDef.ofRefs ds)
  | d => .ref d

def GDef.ofRefs : List (Syntax.Definition Silmaril.Wasm.Module) → List GDef
  | [] => []
  | d :: ds => GDef.ofRef d :: GDef.ofRefs ds
end

/-- The Core 3.0 profile's step. -/
abbrev step (feat : Features) (sc : Scopes Core3Extern) (s : DefState Core3Extern)
    (d : Syntax.Definition Silmaril.Wasm.Module) :=
  checkDef? feat core3Profile core3ModuleType? sc s d

mutual
/-- **One step of the fold**: `checkDef?` on a reference definition, the 🛸 rules on a
`lift`/`lower` with 🛸 options. -/
def gDef? (feat : Features) (sc : Scopes Core3Extern) (s : DefState Core3Extern) :
    GDef → Except ValidationError (DefState Core3Extern)
  | .ref d => (step feat sc s d).map (fixExport s d)
  | .comp ds =>
    match gDefs? feat (Scopes.enter sc s.ctx .component).1
        { st := s.st.child (Scopes.enter sc s.ctx .component).2 } ds with
    | .error e => .error e
    | .ok ch =>
      if ComponentDone ch.ctx then .ok (s.step (s.st.closeComponentDef ch.st))
      else .error (doneError ch.ctx)
  | .lift callee os t =>
    match s.ctx.type? t with
    | some (.func ft) =>
      match liftProblem feat s.ctx callee os ft with
      | some e => .error ⟨e⟩
      | none =>
        .ok (s.step (s.st.withCtx (pushCanonEntity s.ctx (.func ft)))
          (canonReq s.names s.ctx (.lift callee (v0 os) t)))
    | _ => .error ⟨s!"type index {t} is not a function type"⟩
  | .lower f os =>
    match s.ctx.func? f with
    | some ft =>
      match lowerCheck feat s.ctx os ft with
      | .error e => .error ⟨e⟩
      | .ok x => .ok (s.step (s.st.withCtx (pushCanonEntity s.ctx (.coreFunc x))))
    | none => .error ⟨s!"function index {f} out of bounds"⟩

/-- The fold over definitions. -/
def gDefs? (feat : Features) (sc : Scopes Core3Extern) (s : DefState Core3Extern) :
    List GDef → Except ValidationError (DefState Core3Extern)
  | [] => .ok s
  | d :: ds =>
    match gDef? feat sc s d with
    | .ok s' => gDefs? feat sc s' ds
    | .error e => .error e
end

/-- **The validator of a component with 🛸 definitions**: the fold from the empty state, then
the reference's finishing check. -/
def check? (feat : Features) (ds : List GDef) :
    Except ValidationError (Types.ComponentType Nat Core3Extern) :=
  match gDefs? feat [] initState ds with
  | .error e => .error e
  | .ok s => if ComponentDone s.ctx then .ok (componentTypeOfDefs s.ctx) else .error (doneError s.ctx)

/-! ## The relation -/

mutual
/-- **Validity of one definition** with 🛸 rules: the reference's `ValidDef` on reference
definitions, `LiftOk`/`LowerOk` on 🛸 `lift`/`lower`. -/
inductive GValidDef (feat : Features) :
    Scopes Core3Extern → DefState Core3Extern → GDef → DefState Core3Extern → Prop
  | ref {sc : Scopes Core3Extern} {s s' : DefState Core3Extern}
      {d : Syntax.Definition Silmaril.Wasm.Module}
      (h : ValidDef feat core3Profile core3ModuleType? sc s d s') :
      GValidDef feat sc s (.ref d) (fixExport s d s')
  | comp {sc : Scopes Core3Extern} {s ch : DefState Core3Extern} {ds : List GDef}
      (h : GValidDefs feat (Scopes.enter sc s.ctx .component).1
        { st := s.st.child (Scopes.enter sc s.ctx .component).2 } ds ch)
      (hdone : ComponentDone ch.ctx) :
      GValidDef feat sc s (.comp ds) (s.step (s.st.closeComponentDef ch.st))
  | lift {sc : Scopes Core3Extern} {s : DefState Core3Extern} {callee t : Nat}
      {os : List BinaryGC.CanonOpt} {ft : FT}
      (hty : s.ctx.type? t = some (.func ft)) (h : LiftOk feat s.ctx callee os ft) :
      GValidDef feat sc s (.lift callee os t)
        (s.step (s.st.withCtx (pushCanonEntity s.ctx (.func ft)))
          (canonReq s.names s.ctx (.lift callee (v0 os) t)))
  | lower {sc : Scopes Core3Extern} {s : DefState Core3Extern} {f : Nat}
      {os : List BinaryGC.CanonOpt} {ft : FT} {x : Core3Extern}
      (hty : s.ctx.func? f = some ft) (h : LowerOk feat s.ctx os ft x) :
      GValidDef feat sc s (.lower f os) (s.step (s.st.withCtx (pushCanonEntity s.ctx (.coreFunc x))))

/-- Validity of definitions in order. -/
inductive GValidDefs (feat : Features) :
    Scopes Core3Extern → DefState Core3Extern → List GDef → DefState Core3Extern → Prop
  | nil {sc : Scopes Core3Extern} {s : DefState Core3Extern} : GValidDefs feat sc s [] s
  | cons {sc : Scopes Core3Extern} {s s' s'' : DefState Core3Extern} {d : GDef} {ds : List GDef}
      (h : GValidDef feat sc s d s') (hs : GValidDefs feat sc s' ds s'') :
      GValidDefs feat sc s (d :: ds) s''
end

/-- **A valid component with 🛸 definitions** and its type. -/
def GValid (feat : Features) (ds : List GDef) (ct : Types.ComponentType Nat Core3Extern) : Prop :=
  ∃ s, GValidDefs feat [] initState ds s ∧ ComponentDone s.ctx ∧ ct = componentTypeOfDefs s.ctx

end Silmaril.Wasm.Tools.Component.GcAbi

module

public import Silmaril.Wasm.Component.Conformance.DecodeGC.Defs
public import Silmaril.Wasm.Component.Conformance.Extra.Defs
public import Silmaril.Wasm.Tools.Component.Gates.Defs
public import Silmaril.Wasm.Tools.Component.Typed.Defs
public import Silmaril.Wasm.Tools.Component.BinaryW.Defs
public import Silmaril.Wasm.Tools.Component.GcAbi.Defs

/-!
# `wasm-tools validate` for components

The core of `wasm-tools validate` (bytecodealliance/wasm-tools 1.262.0) on a component binary,
as a pure function of the bytes and of the component-model feature flags.

* **Features.** `CFlags` holds the wasmparser flags that matter for a component: the
  component-model gates of `Silmaril.Wasm.Component.Features` (🔀 `cm-async`, 🗺️ `cm-map`,
  🏷️ `cm-implements`, 🔧 `cm-fixed-length-lists`, 📝 `cm-error-context`, 🚝
  `cm-more-async-builtins`, 🚟 `cm-async-stackful`, 🧵 `cm-threading`, ➡️ `cm-forward`,
  🐘 `cm64`, 📡 `cm-accessors`, 🔗 `cm-canon-names`, 🪙 `cm-values`,
  🪺 `cm-nested-names`) and 🛸 `cm-gc`. `CFlags.default` is wasmparser's
  `WasmFeatures::default()` at 1.262.0 (`crates/wasmparser/src/features.rs`: `cm_async`,
  `cm_map` and `cm_implements` on, the other component gates off; `cm_gc` off);
  `CFlags.all` is `--features all`.
* **Decoding.** `decode F b`: the verified `BinaryP3` grammar (component-model `Binary.md` at
  `d095e2f`) and its lowering `toRefP3` to the reference syntax (`Conformance.decodeP3`), when
  it succeeds and its result has no 🪙 value `externdesc`; otherwise wasmparser's reading
  `BinaryW` (WebAssembly 3.0 core types and shared memory limits in component type sections,
  the 🛸 canonical options, value bounds written `0x02 valtype` as wasmparser reads them), whose
  🛸 `lift`/`lower` are kept apart (`GcAbi.erase`). The 🛸 options need `cm-gc` (`gcOptsUsed`,
  wasmparser: "canonical option `gc` requires the `cm-gc` feature").
* **Validation.** `checkCore3? F.feat c`, the copied reference validator over the Core 3.0
  profile, sound for `ValidComponentCore3` (every core module is `ModuleValid`, every
  definition is valid by the rules of `Validation/Defs`); for a component with 🛸
  `lift`/`lower` or a value export, the extended fold `GcAbi.check?` instead (the reference's
  step on every other definition, wasmparser's GC canonical ABI `lower_gc` on 🛸 `lift`/`lower`,
  exported values marked used as wasmparser does), sound for `GcAbi.GValid`. Then the
  executable rules of `Conformance.Extra` (`extraProblem`: SemVer, attributes, duplicate core
  imports, annotated names) that the copied validator lacks, and the rules of `Gates`
  (`version-suffix`, `context.get`/`set` immediates) and `Typed` (`task.return` results without
  `borrow`, 📡 accessor and constructor types, also in type declarations, inline value exports
  without `borrow`, type nesting and size limits) that neither has (`gateAll`).

`check F b` returns the component's type, or the step that rejected it (`Error`). The
specification theorems are in `Validate.Thms`:

* `check_sound`: an accepted binary is accepted by `Accepts`: it is in the binary grammar
  (`DecodesAs`) and its decoding is `ValidComponentCore3` at `F.feat`, or it is wasmparser's
  reading (`DecodesExt`) and `GcAbi.GValid`; and no extra or gate rule fires;
* `check_ok_iff`: `check` succeeds exactly when the decoder succeeds, the reference checker
  accepts and the extra rules find nothing (the definition, unfolded);
* `default_le_all`: the default flags are below `--features all`.

Completeness is not claimed (the copied checker is not proved complete; see the header of
`Silmaril/Raw/Wasm/Component/Validation/Check.lean`); agreement with wasm-tools is tested
(`tools/wasm-tools/tests/compval/validate.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Validate

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Validation

/-- The component-model flags of wasmparser's `WasmFeatures` that the component validator
reads: the gates of the reference (`feat`) and 🛸 `cm-gc` (`gc`). -/
structure CFlags where
  feat : Features
  gc : Bool
  deriving Repr, DecidableEq

namespace CFlags

/-- wasmparser's default at 1.262.0: 🔀 🗺️ 🏷️ on. -/
def default : CFlags := ⟨Features.p3, false⟩

/-- `--features all`. -/
def all : CFlags := ⟨Features.all, true⟩

/-- Pointwise order. -/
def le (a b : CFlags) : Prop := Features.le a.feat b.feat ∧ (a.gc = true → b.gc = true)

end CFlags

mutual
/-- Does a `BinaryGC` component use a 🛸 canonical option (`gc` or `core-type`)? -/
def gcOptsSections : List BinaryGC.Section → Bool
  | [] => false
  | .canons xs :: ss =>
    xs.any (fun
      | .lift _ os _ | .lower _ os => os.any GcCheck.isGcOpt
      | .p3 _ => false) || gcOptsSections ss
  | .component c :: ss => gcOptsUsed c || gcOptsSections ss
  | _ :: ss => gcOptsSections ss

def gcOptsUsed : BinaryGC.Ast → Bool
  | .mk ss => gcOptsSections ss
end

/-! ## 🪙 value bounds -/

/-- A 🪙 value `externdesc`. -/
def isValueDesc : Syntax.ExternDesc → Bool
  | .value _ => true
  | _ => false

mutual
/-- A value `externdesc` in a type definition's declarators. -/
def vDefType : Syntax.DefType → Bool
  | .component ds => vCDecls ds
  | .instance_ ds => vIDecls ds
  | _ => false

def vIDecl : Syntax.InstanceDecl → Bool
  | .type t => vDefType t
  | .export_ _ d => isValueDesc d
  | _ => false

def vIDecls : List Syntax.InstanceDecl → Bool
  | [] => false
  | d :: ds => vIDecl d || vIDecls ds

def vCDecl : Syntax.ComponentDecl → Bool
  | .import_ _ d => isValueDesc d
  | .decl d => vIDecl d

def vCDecls : List Syntax.ComponentDecl → Bool
  | [] => false
  | d :: ds => vCDecl d || vCDecls ds
end

mutual
/-- A value `externdesc` in a definition (imports, ascribed exports, type declarators). -/
def vDef {M : Type} : Syntax.Definition M → Bool
  | .component ds => vDefs ds
  | .type t => vDefType t
  | .import_ _ d => isValueDesc d
  | .export_ _ _ (some d) => isValueDesc d
  | _ => false

def vDefs {M : Type} : List (Syntax.Definition M) → Bool
  | [] => false
  | d :: ds => vDef d || vDefs ds
end

/-- Does the component have a 🪙 value `externdesc` anywhere (where `Binary.md`'s
`valuebound` and wasmparser's `0x02 valtype` differ)? -/
def hasValueDesc (c : RefComponent) : Bool := vDefs c

/-! ## The decoder -/

/-- A decoded component: reference syntax, or definitions for the extended fold
(`GcAbi.check?`: 🛸 `lift`/`lower`, or value exports, which the reference mishandles). -/
inductive Decoded where
  | ref (c : RefComponent)
  | ext (ds : List GcAbi.GDef)

/-- Which validator a decoding needs: the extended fold with 🛸 `lift`/`lower` or a value
export. -/
def needsExt (ds : List GcAbi.GDef) : Bool :=
  GcAbi.GDef.hasGcs ds || GcAbi.exportsValues (GcAbi.GDef.toRefs ds)

/-- The wasmparser reading (`BinaryW`), refusing the 🛸 options without `cm-gc`; `e` is the
error reported when it fails. -/
def decodeW (F : CFlags) (b : ByteArray) (e : String) : Except String Decoded :=
  match BinaryW.parse b with
  | .error _ => .error e
  | .ok a =>
    if !F.gc && gcOptsUsed a then .error "canonical option `gc` requires the `cm-gc` feature"
    else match GcAbi.erase a with
      | .error e => .error e
      | .ok ds => if needsExt ds then .ok (.ext ds) else .ok (.ref (GcAbi.GDef.toRefs ds))

/-- **The decoder under `F`**: `BinaryP3` and `toRefP3` when that succeeds without a 🪙 value
`externdesc`; otherwise wasmparser's reading `BinaryW` (WebAssembly 3.0 core types, 🛸
options, value bounds `0x02 t`), whose 🛸 `lift`/`lower` are kept apart. Components with 🛸
`lift`/`lower` or value exports go to the extended fold. -/
def decode (F : CFlags) (b : ByteArray) : Except String Decoded :=
  match decodeP3 b with
  | .ok d =>
    if hasValueDesc d then decodeW F b "invalid value type: wasmparser reads a value bound as \
      `0x02 valtype`"
    else if GcAbi.exportsValues d then .ok (.ext (GcAbi.GDef.ofRefs d))
    else .ok (.ref d)
  | .error e => decodeW F b e

/-- The verified `BinaryP3` grammar, without a 🪙 value `externdesc`. -/
def DecodesP3 (b : ByteArray) (c : RefComponent) : Prop :=
  ∃ a, (BinaryP3.componentG (b.size + 1)).G b.data.toList a ∧ toRefP3 a = .ok c ∧
    hasValueDesc c = false

/-- **wasmparser's reading**: `b` parses with `BinaryW` to definitions `ds` (🛸 options only
under `cm-gc`). -/
def DecodesW (F : CFlags) (b : ByteArray) (ds : List GcAbi.GDef) : Prop :=
  ∃ a, BinaryW.parse b = .ok a ∧ (F.gc = true ∨ gcOptsUsed a = false) ∧ GcAbi.erase a = .ok ds

/-- **The binary grammar**: `b` decodes to the reference component `c` through the verified
`BinaryP3` grammar, or through wasmparser's reading `BinaryW` (🛸 options dropped). -/
def DecodesAs (F : CFlags) (b : ByteArray) (c : RefComponent) : Prop :=
  DecodesP3 b c ∨ ∃ ds, DecodesW F b ds ∧ c = GcAbi.GDef.toRefs ds

/-- The definitions of the extended fold: wasmparser's reading, or the `BinaryP3` decoding
(nested components as `comp`). -/
def DecodesExt (F : CFlags) (b : ByteArray) (ds : List GcAbi.GDef) : Prop :=
  DecodesW F b ds ∨ ∃ c, DecodesP3 b c ∧ ds = GcAbi.GDef.ofRefs c

/-- Why a binary was rejected. -/
inductive Error where
  /-- The decoder rejected the bytes. -/
  | malformed (msg : String)
  /-- The reference validator rejected the component. -/
  | invalid (msg : String)
  /-- One of the extra rules (`Conformance.Extra`) rejected it. -/
  | extra (msg : String)
  /-- One of the gate rules (`Gates`) rejected it. -/
  | gate (msg : String)
  deriving Repr, DecidableEq

/-- The message after `error: ` (the class of upstream's message; the text is the
reference's, which follows wasmparser's where the copied validator knows it). -/
def Error.message : Error → String
  | .malformed e => s!"failed to parse WebAssembly component: {e}"
  | .invalid e => s!"component failed to validate: {e}"
  | .extra e => s!"component failed to validate: {e}"
  | .gate e => s!"component failed to validate: {e}"

/-- The rules beyond the reference and `Conformance.Extra`: the syntactic `Gates` and the
typed `Typed` rules (`task.return` without `borrow`, 📡 accessors, constructors, type
nesting and size limits). -/
def gateAll (F : CFlags) (c : RefComponent) : Option String :=
  Gates.gateProblem F.feat c <|> Typed.walkProblem F.feat c

/-- The extra and gate rules after the reference accepted with type `ct`. -/
def finish (F : CFlags) (c : RefComponent) (ct : Types.ComponentType Nat Core3Extern) :
    Except Error (Types.ComponentType Nat Core3Extern) :=
  match Extra.extraProblem F.feat.nestedNames c with
  | some e => .error (.extra e)
  | none =>
    match gateAll F c with
    | some e => .error (.gate e)
    | none => .ok ct

/-- **The validator**: decode, `checkCore3?` (or, with 🛸 `lift`/`lower`, the fold
`GcAbi.check?`), then the extra rules. -/
def check (F : CFlags) (b : ByteArray) :
    Except Error (Types.ComponentType Nat Core3Extern) :=
  match decode F b with
  | .error e => .error (.malformed e)
  | .ok (.ref c) =>
    match checkCore3? F.feat c with
    | .error e => .error (.invalid e.message)
    | .ok ct => finish F c ct
  | .ok (.ext ds) =>
    match GcAbi.check? F.feat ds with
    | .error e => .error (.invalid e.message)
    | .ok ct => finish F (GcAbi.GDef.toRefs ds) ct

/-- What `wasm-tools validate` accepts (the specification side): a decoding `c` that is
valid, by the reference (`ValidComponentCore3`) or by the extended fold (`GcAbi.GValid`: the
reference's rules, the GC ABI, value exports used; `c` then is the decoding with 🛸 options
dropped), and
on which the extra and gate rules find nothing. -/
def Accepts (F : CFlags) (b : ByteArray) (c : RefComponent)
    (ct : Types.ComponentType Nat Core3Extern) : Prop :=
  ((DecodesAs F b c ∧ ValidComponentCore3 F.feat c ct) ∨
    (∃ ds, DecodesExt F b ds ∧ c = GcAbi.GDef.toRefs ds ∧ GcAbi.GValid F.feat ds ct)) ∧
    Extra.extraProblem F.feat.nestedNames c = none ∧ gateAll F c = none

/-! ## Module or component -/

/-- The kind of a binary, from its preamble (`\0asm`, then version `01 00 00 00` for a core
module, `0d 00 01 00` for a component), as wasmparser's `Parser` reads it. -/
inductive Kind where
  | module
  | component
  | unknown
  deriving Repr, DecidableEq

/-- Read the preamble. -/
def kindOf (b : ByteArray) : Kind :=
  if b.size < 8 then .unknown
  else if b[0]! = 0x00 ∧ b[1]! = 0x61 ∧ b[2]! = 0x73 ∧ b[3]! = 0x6d then
    if b[4]! = 0x01 ∧ b[5]! = 0x00 ∧ b[6]! = 0x00 ∧ b[7]! = 0x00 then .module
    else if b[4]! = 0x0d ∧ b[5]! = 0x00 ∧ b[6]! = 0x01 ∧ b[7]! = 0x00 then .component
    else .unknown
  else .unknown

end Silmaril.Wasm.Tools.Component.Validate

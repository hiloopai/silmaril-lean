module

public import Silmaril.Wasm.Lime1.ToCore.Modules

/-!
# 3.0 to Lime compilers: the Lime-preserving variant and export APIs

Part (3) of the 3.0 → Lime compiler (docs/projects/wasm-wasi.md, "3.0 to Lime compiler"). A
**compiler** takes a Core 3.0 module to a Lime1 module, or fails. Lime-only code is the image of
`Lime1.Module.toCore`; a compiler is **Lime-preserving** when it returns `l` on `l.toCore`.

* `Compiler`, `LimePreserving`, `Correct R c` (every output, read back in Core 3.0 through
  `Lime1.Module.toCore`, is related to its input by `R`);
* `limeView M`: the Lime1 module whose Core image is exactly `M`, if any. It is
  `Lime1.Module.ofCore? M` guarded by `ElemsCanon M` (every element segment typed `funcref`):
  the decoder alone also accepts the non-null `(ref func)` element type, so its output is the
  input only up to element types (`Lime1Inst.module_retract`);
* **`limePres c`**: the Lime-preserving variant of a compiler `c`: the identity (as a Lime1
  module) on Lime-only input, `c` elsewhere;
* `naivePres c`: the variant short-circuiting on the bare decoder (refuted as an identity in
  `Thms`);
* instruction level: `InstrCompiler` (a Core instruction to a Lime1 instruction sequence),
  `instrPres t` (Lime1 instructions are kept, as singletons), `exprCompile t` (map and
  concatenate);
* export APIs: `ApiTy` (resolved export types), `Module.exportApi` (the names and resolved types
  of a module's exports, in order), `ApiTy.lime` (the types a Lime1 module can export) and
  `ApiLime` (every resolved export type is a Lime type).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Preserve

open Silmaril.Wasm

/-! ## Compilers and the Lime-preserving variant -/

/-- **A 3.0 → Lime compiler**: a Core 3.0 module to a Lime1 module, or failure. -/
abbrev Compiler := Silmaril.Wasm.Module → Option Lime1.Module

/-- A compiler is **Lime-preserving** when it is the identity on Lime-only code: on the Core
image of a Lime1 module it returns that module. -/
def LimePreserving (c : Compiler) : Prop :=
  ∀ l : Lime1.Module, c l.toCore = some l

/-- A compiler is **correct for `R`** when each output, read back in Core 3.0, is related to the
input by `R` (for instance: same behaviours at the export API). -/
def Correct (R : Silmaril.Wasm.Module → Silmaril.Wasm.Module → Prop) (c : Compiler) : Prop :=
  ∀ M l, c M = some l → R M l.toCore

/-- Every element segment is typed `funcref`, the type `Lime1.Elem.toCore` assigns. -/
def ElemsCanon (M : Silmaril.Wasm.Module) : Bool :=
  M.elems.all fun e => decide (e.type = V1.funcref)

/-- **The Lime view** of a Core module: the Lime1 module whose Core image is exactly `M`. -/
def limeView (M : Silmaril.Wasm.Module) : Option Lime1.Module :=
  match Lime1.Module.ofCore? M with
  | some l => if ElemsCanon M then some l else none
  | none => none

/-- **The Lime-preserving variant of a compiler**: keep Lime-only code, compile the rest. -/
def limePres (c : Compiler) : Compiler := fun M =>
  match limeView M with
  | some l => some l
  | none => c M

/-- The naive variant, short-circuiting on the bare decoder `Lime1.Module.ofCore?`. -/
def naivePres (c : Compiler) : Compiler := fun M =>
  match Lime1.Module.ofCore? M with
  | some l => some l
  | none => c M

/-! ## Instruction level -/

/-- An instruction compiler: a Core instruction to a Lime1 instruction sequence, or failure. -/
abbrev InstrCompiler := Silmaril.Wasm.Instr → Option Lime1.Expr

/-- The Lime-preserving variant of an instruction compiler: a Lime1 instruction is kept. -/
def instrPres (t : InstrCompiler) : InstrCompiler := fun i =>
  match Lime1.Instr.ofCore? i with
  | some j => some [j]
  | none => t i

/-- Compile an expression instruction by instruction and concatenate. -/
def exprCompile (t : InstrCompiler) (es : Silmaril.Wasm.Expr) : Option Lime1.Expr :=
  (es.mapM t).map List.flatten

/-! ## Export APIs -/

/-- A resolved export type. Function and tag types are resolved to their sub type (the type
definition at their type index), so the API does not track recursion-group identity. -/
inductive ApiTy where
  | func (t : SubType)
  | table (t : TableType)
  | memory (t : MemoryType)
  | global (t : GlobalType)
  | tag (t : SubType)
  deriving DecidableEq, Repr

/-- Imported table types. -/
def Module.impTables (M : Silmaril.Wasm.Module) : List TableType :=
  M.imports.filterMap fun i => match i.type with | .table t => some t | _ => none

/-- Imported memory types. -/
def Module.impMems (M : Silmaril.Wasm.Module) : List MemoryType :=
  M.imports.filterMap fun i => match i.type with | .memory t => some t | _ => none

/-- Imported global types. -/
def Module.impGlobals (M : Silmaril.Wasm.Module) : List GlobalType :=
  M.imports.filterMap fun i => match i.type with | .global t => some t | _ => none

/-- Imported tag types. -/
def Module.impTags (M : Silmaril.Wasm.Module) : List TypeIdx :=
  M.imports.filterMap fun i => match i.type with | .tag t => some t | _ => none

/-- The sub type at a type index. -/
def Module.typeAt (M : Silmaril.Wasm.Module) (x : TypeIdx) : Option SubType :=
  M.typeDefinitions[x.value.val]?

/-- The resolved type of an export index (`none` when an index is out of range). -/
def Module.resolve (M : Silmaril.Wasm.Module) : ExternIdx → Option ApiTy
  | .func i => (M.functionTypes[i.value.val]?).bind fun x => (Module.typeAt M x).map .func
  | .table i => ((Module.impTables M ++ M.tables.map Table.type)[i.value.val]?).map .table
  | .memory i => ((Module.impMems M ++ M.memories)[i.value.val]?).map .memory
  | .global i => ((Module.impGlobals M ++ M.globals.map Global.type)[i.value.val]?).map .global
  | .tag i =>
    ((Module.impTags M ++ M.tags)[i.value.val]?).bind fun x => (Module.typeAt M x).map .tag

/-- **The export API** of a module: export names and resolved types, in order. -/
def Module.exportApi (M : Silmaril.Wasm.Module) : List (String × Option ApiTy) :=
  M.exports.map fun e => (e.name, Module.resolve M e.index)

/-- A Lime value type: a number type. -/
def limeVal : ValType → Bool
  | .num _ => true
  | _ => false

/-- Limits that fit 32-bit addresses. -/
def fits32 (l : Limits) : Bool :=
  decide (l.min.val < 2 ^ 32) && l.max.all fun n => decide (n.val < 2 ^ 32)

/-- **The export types a Lime1 module can have**: final parent-free function types over number
types, `i32` tables of `funcref` and `i32` memories with 32-bit limits, number-typed globals;
never a tag. -/
def ApiTy.lime : ApiTy → Bool
  | .func ⟨true, [], .func ft⟩ => ft.params.all limeVal && ft.results.all limeVal
  | .func _ => false
  | .table t => decide (t.address = .i32) && decide (t.element = V1.funcref) && fits32 t.limits
  | .memory t => decide (t.address = .i32) && fits32 t.limits
  | .global t => limeVal t.value
  | .tag _ => false

/-- Every resolved type of an API is a Lime type. -/
def ApiLime (api : List (String × Option ApiTy)) : Prop :=
  ∀ p ∈ api, ∀ t, p.2 = some t → t.lime = true

end Silmaril.Wasm.LimeCompile.Preserve

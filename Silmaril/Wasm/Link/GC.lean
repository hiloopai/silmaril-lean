module

public import Silmaril.Wasm.Validation.Check.ValidateFinal

/-! # A partial static linker for memory-free GC modules

`link? namespace provider consumer` merges the two source modules. The provider
must be import-free; the consumer may import only provider functions in that
namespace. Imports resolve by export name and checked closed function subtyping.
Consumer type groups, function references and globals are relocated into the
combined index spaces. Every index addition checks the unsigned 32-bit bound.

The supported profile has functions, GC types and globals, but no memories,
tables, tags, segments or start functions. Unsupported instruction forms reject.
Both inputs and the final merged module must pass Core 3.0 validation. This is
an executable linker for this profile; general semantic preservation is not
proved here.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC

open Silmaril.Wasm

def shiftIdx? {kind : IndexKind} (offset : Nat) (i : Idx kind) : Option (Idx kind) :=
  Idx.ofNat? (offset + i.toNat)

def heap? (offset : Nat) : HeapType → Option HeapType
  | .abstract a => some (.abstract a)
  | .typeIdx i => (.typeIdx ·) <$> shiftIdx? offset i

def refType? (offset : Nat) (r : RefType) : Option RefType := do
  pure ⟨r.nullable, ← heap? offset r.heap⟩

def valType? (offset : Nat) : ValType → Option ValType
  | .num n => some (.num n)
  | .vec v => some (.vec v)
  | .ref r => (.ref ·) <$> refType? offset r

def storageType? (offset : Nat) : StorageType → Option StorageType
  | .val v => (.val ·) <$> valType? offset v
  | .packed p => some (.packed p)

def fieldType? (offset : Nat) (f : FieldType) : Option FieldType := do
  pure ⟨f.mutability, ← storageType? offset f.storage⟩

def compositeType? (offset : Nat) : CompositeType → Option CompositeType
  | .func f => do
    pure (.func ⟨← f.params.mapM (valType? offset), ← f.results.mapM (valType? offset)⟩)
  | .struct fs => (.struct ·) <$> fs.mapM (fieldType? offset)
  | .array f => (.array ·) <$> fieldType? offset f

def subType? (offset : Nat) (s : SubType) : Option SubType := do
  pure ⟨s.final_, ← s.supertypes.mapM (shiftIdx? offset), ← compositeType? offset s.body⟩

/-- Source type indices are absolute, including references to members of their
own recursion group. Shift all uses while preserving the groups themselves. -/
def recType? (offset : Nat) (r : RecType) : Option RecType :=
  (RecType.mk ·) <$> r.types.mapM (subType? offset)

def blockType? (offset : Nat) : BlockType → Option BlockType
  | .empty => some .empty
  | .value v => (.value ·) <$> valType? offset v
  | .typeIdx i => (.typeIdx ·) <$> shiftIdx? offset i

structure Relocation where
  types : Nat
  functions : Nat
  globals : Nat
  imports : List FuncIdx

/-- Imported consumer functions become provider function indices; consumer
definitions follow the provider definitions. -/
def function? (r : Relocation) (i : FuncIdx) : Option FuncIdx :=
  if i.toNat < r.imports.length then r.imports[i.toNat]?
  else Idx.ofNat? (r.functions + (i.toNat - r.imports.length))

/-- Relocate the supported instruction fragment. Local/label/field indices
belong to their enclosing function, block or type and remain unchanged. -/
def instruction? (r : Relocation) (i : Instr) : Option Instr :=
  match i with
  | .block t body => do
    pure (.block (← blockType? r.types t)
      (← body.attach.mapM fun nested => instruction? r nested.val))
  | .loop t body => do
    pure (.loop (← blockType? r.types t)
      (← body.attach.mapM fun nested => instruction? r nested.val))
  | .if_ t yes no => do
    pure (.if_ (← blockType? r.types t)
      (← yes.attach.mapM fun nested => instruction? r nested.val)
      (← no.attach.mapM fun nested => instruction? r nested.val))
  | .select none => some i
  | .select (some ts) => do pure (.select (some (← ts.mapM (valType? r.types))))
  | .call f => (.call ·) <$> function? r f
  | .returnCall f => (.returnCall ·) <$> function? r f
  | .refFunc f => (.refFunc ·) <$> function? r f
  | .callRef t => (.callRef ·) <$> shiftIdx? r.types t
  | .returnCallRef t => (.returnCallRef ·) <$> shiftIdx? r.types t
  | .globalGet g => (.globalGet ·) <$> shiftIdx? r.globals g
  | .globalSet g => (.globalSet ·) <$> shiftIdx? r.globals g
  | .refNull h => (.refNull ·) <$> heap? r.types h
  | .refTest t => (.refTest ·) <$> refType? r.types t
  | .refCast t => (.refCast ·) <$> refType? r.types t
  | .brOnCast l source target => do
    pure (.brOnCast l (← refType? r.types source) (← refType? r.types target))
  | .brOnCastFail l source target => do
    pure (.brOnCastFail l (← refType? r.types source) (← refType? r.types target))
  | .structNew t => (.structNew ·) <$> shiftIdx? r.types t
  | .structNewDefault t => (.structNewDefault ·) <$> shiftIdx? r.types t
  | .structGet sign t field => do pure (.structGet sign (← shiftIdx? r.types t) field)
  | .structSet t field => do pure (.structSet (← shiftIdx? r.types t) field)
  | .arrayNew t => (.arrayNew ·) <$> shiftIdx? r.types t
  | .arrayNewDefault t => (.arrayNewDefault ·) <$> shiftIdx? r.types t
  | .arrayNewFixed t n => do pure (.arrayNewFixed (← shiftIdx? r.types t) n)
  | .arrayGet sign t => do pure (.arrayGet sign (← shiftIdx? r.types t))
  | .arraySet t => (.arraySet ·) <$> shiftIdx? r.types t
  | .arrayFill t => (.arrayFill ·) <$> shiftIdx? r.types t
  | .arrayCopy dst src => do pure (.arrayCopy (← shiftIdx? r.types dst) (← shiftIdx? r.types src))
  | .nop | .unreachable | .drop | .return_
  | .localGet _ | .localSet _ | .localTee _
  | .br _ | .brIf _ | .brTable _ _ | .brOnNull _ | .brOnNonNull _
  | .refIsNull | .refAsNonNull | .refEq | .refI31 | .i31Get _ | .arrayLen
  | .externConvertAny | .anyConvertExtern
  | .intConst _ _ | .floatConst _ _ | .intUnOp _ _ | .intBinOp _ _
  | .intTestOp _ _ | .intRelOp _ _
  | .floatUnOp _ _ | .floatBinOp _ _ | .floatRelOp _ _ | .convert _ => some i
  | _ => none
termination_by sizeOf i
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem nested.property
  all_goals omega

def instructions? (r : Relocation) (body : List Instr) : Option (List Instr) :=
  body.mapM (instruction? r)

def func? (r : Relocation) (f : Func) : Option Func := do
  pure ⟨← shiftIdx? r.types f.type, ← f.locals.mapM (valType? r.types),
    ← instructions? r f.body⟩

def global? (r : Relocation) (g : Global) : Option Global := do
  pure ⟨⟨g.type.mutability, ← valType? r.types g.type.value⟩, ← instructions? r g.init⟩

def export? (r : Relocation) (e : Export) : Option Export := do
  let idx ← match e.index with
    | .func f => (.func ·) <$> function? r f
    | .global g => (.global ·) <$> shiftIdx? r.globals g
    | _ => none
  pure ⟨e.name, idx⟩

def inProfile (m : Module) : Bool :=
  m.memories.isEmpty && m.tables.isEmpty && m.tags.isEmpty &&
  m.data.isEmpty && m.elems.isEmpty && m.start.isNone &&
  m.imports.all (fun i => match i.type with | .func _ => true | _ => false)

/-- Legacy exact closed-type matching, retained for explicit compatibility checks. -/
def resolveImportsExact? (namespaceName : String) (provider consumer : Module)
    (providerType consumerType : Validation.CModuleType) : Option (List FuncIdx) :=
  (consumer.imports.zip consumerType.imports).mapM fun (entry, expected) => do
    if entry.moduleName != namespaceName then none else do
      let .func _ := entry.type | none
      let .func expected := expected | none
      let (actualExport, actualType) ← (provider.exports.zip providerType.exports).find?
        (fun (e, _) => e.name == entry.name)
      let .func f := actualExport.index | none
      let .func actual := actualType | none
      if actual = expected then some f else none

/-- Resolve by original namespace, export name, and closed function subtyping.
The exact-type branch preserves every legacy success; the fallback uses the
proved-sound Core subtyping checker. -/
def resolveImports? (namespaceName : String) (provider consumer : Module)
    (providerType consumerType : Validation.CModuleType) : Option (List FuncIdx) :=
  (consumer.imports.zip consumerType.imports).mapM fun (entry, expected) => do
    if entry.moduleName != namespaceName then none else do
      let .func _ := entry.type | none
      let .func expected := expected | none
      let (actualExport, actualType) ← (provider.exports.zip providerType.exports).find?
        (fun (e, _) => e.name == entry.name)
      let .func f := actualExport.index | none
      let .func actual := actualType | none
      if actual = expected then some f else
        if Validation.Sub.check {} actual expected then some f else none

def assemble? (namespaceName : String) (provider consumer : Module) : Option Module := do
  if !(inProfile provider && inProfile consumer && provider.imports.isEmpty) then none else do
    let providerType ← Validation.validate? provider
    let consumerType ← Validation.validate? consumer
    if provider.typeDefinitions.length + consumer.typeDefinitions.length ≥ 2^32 ||
        provider.funcs.length + consumer.funcs.length ≥ 2^32 ||
        provider.globals.length + consumer.globals.length ≥ 2^32 then none else do
      let imports ← resolveImports? namespaceName provider consumer providerType consumerType
      let relocation : Relocation :=
        ⟨provider.typeDefinitions.length, provider.funcs.length, provider.globals.length, imports⟩
      let types ← consumer.types.mapM (recType? relocation.types)
      let funcs ← consumer.funcs.mapM (func? relocation)
      let globals ← consumer.globals.mapM (global? relocation)
      let exports ← consumer.exports.mapM (export? relocation)
      -- The provider needs no relocation, but the same fragment restriction
      -- applies to both modules; identity relocation checks its instructions.
      let identity : Relocation := ⟨0, 0, 0, []⟩
      let providerFuncs ← provider.funcs.mapM (func? identity)
      let providerGlobals ← provider.globals.mapM (global? identity)
      pure {
        types := provider.types ++ types
        funcs := providerFuncs ++ funcs
        globals := providerGlobals ++ globals
        exports := provider.exports ++ exports }

def validated? (m : Module) : Option Module :=
  if (Validation.validate? m).isSome then some m else none

/-- A genuine two-input partial static linker. It rejects unsupported shapes,
unresolved imports, type mismatches, index overflow and invalid merged code. -/
def link? (namespaceName : String) (provider consumer : Module) : Option Module := do
  validated? (← assemble? namespaceName provider consumer)

theorem validated?_sound {m result : Module} (h : validated? m = some result) :
    Validation.ModuleValid result := by
  unfold validated? at h
  split at h
  · rename_i hv
    cases h
    exact Validation.validate?_isSome_iff.mp hv
  · cases h

theorem link?_valid {namespaceName provider consumer result}
    (h : link? namespaceName provider consumer = some result) : Validation.ModuleValid result := by
  obtain ⟨m, _, hv⟩ := Option.bind_eq_some_iff.mp h
  exact validated?_sound hv

end Silmaril.Wasm.Link.GC

module

public import Silmaril.Wasm.Component.Codec.Defs
public import Silmaril.Wasm.Component.BinaryP3.Encode.Defs
public import Silmaril.Wasm.Perf.CoreDecode.Defs

/-!
# `wasm-tools component unbundle`

Upstream (`UnbundleOpts::run`, `src/bin/wasm-tools/component.rs` of wasm-tools 1.262.0):

1. a non-component input is written back unchanged;
2. the core modules of the component, nested components included, in the order the parser
   meets them (`modulesOf`), are extracted when larger than the threshold (`flags`);
3. each extracted module's imports and exports become a module type (`moduleType`): its
   function types are interned in a new core type section at the front of the component
   (`CoreTypeInterner`, one entry per distinct type, across modules) and aliased into the
   module type on first use (`ModuleTypeCreator`, `alias outer 1 i`);
4. the component starts with that core type section and an import section of
   `unbundled-moduleN` modules at those types;
5. the original sections follow, with every reference to a core type or a core module of the
   *top-level* component shifted past the new ones (`mapAst`: wasm-encoder's
   `ReencodeComponent` with upstream's `ModuleExtractor` hooks: `type_index` and
   `module_index` at depth 0, `outer_type_index` and `outer_module_index` when the alias
   reaches depth 0), the `component-name` sections renamed the same way (`renameNames`), and
   each extracted module replaced by an `alias outer DEPTH N` of its import (`extract`).

`mapAst` is functorial in the index maps (`Silmaril.Wasm.Tools.Component.Unbundle.Thms`:
`mapAst_id`, `mapAst_comp`), so the shift is undone by the opposite shift (`unshift_shift`):
the rewrite loses nothing and touches only core-type and core-module positions of the top level.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Unbundle

open Silmaril.Wasm.Component.Binary (CoreType ModuleDecl CoreImportDesc CoreFuncType CoreValType
  Limits ExternDesc Alias AliasTarget ItemSort CoreSort SortIdx DefType ComponentDecl InstanceDecl
  CoreInstanceExpr InstanceExpr Import Export ExternName)
open Silmaril.Wasm.Component.BinaryP3 (Section Ast Canon)

/-! ## Index maps -/

/-- What happens to core-type and core-module indices of the top-level component. -/
structure IxMap where
  ty : Nat → Nat := id
  mod : Nat → Nat := id

def IxMap.id : IxMap := {}

def IxMap.comp (f g : IxMap) : IxMap := ⟨f.ty ∘ g.ty, f.mod ∘ g.mod⟩

/-- Shift by `t` core types and `m` core modules (`ModuleExtractor`). -/
def IxMap.shift (t m : Nat) : IxMap := ⟨(· + t), (· + m)⟩

def IxMap.unshift (t m : Nat) : IxMap := ⟨(· - t), (· - m)⟩

/-- `type_index` at depth `d`. -/
def tyAt (f : IxMap) (d i : Nat) : Nat := if d = 0 then f.ty i else i
/-- `outer_type_index count i` at depth `d`. -/
def outerTyAt (f : IxMap) (d c i : Nat) : Nat := if d = c then f.ty i else i
/-- `module_index` at depth `d`. -/
def modAt (f : IxMap) (d i : Nat) : Nat := if d = 0 then f.mod i else i
/-- `outer_module_index count i` at depth `d`. -/
def outerModAt (f : IxMap) (d c i : Nat) : Nat := if d = c then f.mod i else i

def mapModuleDecl (f : IxMap) (d : Nat) : ModuleDecl → ModuleDecl
  | .alias c i => .alias c (outerTyAt f d c i)
  | x => x

/-- A core type at depth `d` (a module type's declarations are one level deeper). -/
def mapCoreType (f : IxMap) (d : Nat) : CoreType → CoreType
  | .module ds => .module (ds.map (mapModuleDecl f (d + 1)))
  | x => x

def mapExternDesc (f : IxMap) (d : Nat) : ExternDesc → ExternDesc
  | .coreModule i => .coreModule (tyAt f d i)
  | x => x

def mapAlias (f : IxMap) (d : Nat) (a : Alias) : Alias :=
  match a.sort, a.target with
  | .core .module, .outer c i => { a with target := .outer c (outerModAt f d c i) }
  | .core .type, .outer c i => { a with target := .outer c (outerTyAt f d c i) }
  | _, _ => a

def mapSortIdx (f : IxMap) (d : Nat) (s : SortIdx) : SortIdx :=
  match s.sort with
  | .core .module => { s with idx := modAt f d s.idx }
  | _ => s

mutual
def mapDefType (f : IxMap) (d : Nat) : DefType → DefType
  | .component ds => .component (mapCDecls f (d + 1) ds)
  | .instance ds => .instance (mapIDecls f (d + 1) ds)
  | t => t

def mapCDecls (f : IxMap) (d : Nat) : List ComponentDecl → List ComponentDecl
  | [] => []
  | x :: xs => mapCDecl f d x :: mapCDecls f d xs

def mapCDecl (f : IxMap) (d : Nat) : ComponentDecl → ComponentDecl
  | .import n desc => .import n (mapExternDesc f d desc)
  | .inst i => .inst (mapIDecl f d i)

def mapIDecls (f : IxMap) (d : Nat) : List InstanceDecl → List InstanceDecl
  | [] => []
  | x :: xs => mapIDecl f d x :: mapIDecls f d xs

def mapIDecl (f : IxMap) (d : Nat) : InstanceDecl → InstanceDecl
  | .coreType t => .coreType (mapCoreType f d t)
  | .type t => .type (mapDefType f d t)
  | .alias a => .alias (mapAlias f d a)
  | .export n desc => .export n (mapExternDesc f d desc)
end

def mapCanon (f : IxMap) (d : Nat) : Canon → Canon
  | .threadSpawnRef sh ft => .threadSpawnRef sh (tyAt f d ft)
  | .threadSpawnIndirect sh ft tbl => .threadSpawnIndirect sh (tyAt f d ft) tbl
  | .threadNewIndirect ft tbl => .threadNewIndirect (tyAt f d ft) tbl
  | c => c

def mapCoreInstance (f : IxMap) (d : Nat) : CoreInstanceExpr → CoreInstanceExpr
  | .instantiate m args => .instantiate (modAt f d m) args
  | x => x

def mapInstance (f : IxMap) (d : Nat) : InstanceExpr → InstanceExpr
  | .instantiate c args => .instantiate c (args.map fun (n, s) => (n, mapSortIdx f d s))
  | .exports es => .exports (es.map fun (n, s) => (n, mapSortIdx f d s))

def mapImport (f : IxMap) (d : Nat) (i : Import) : Import := { i with desc := mapExternDesc f d i.desc }

def mapExport (f : IxMap) (d : Nat) (e : Export) : Export :=
  { e with item := mapSortIdx f d e.item, desc := e.desc.map (mapExternDesc f d) }

mutual
/-- **The index rewrite** of a component at depth `d` (custom sections and core modules are
untouched here). -/
def mapAst (f : IxMap) (d : Nat) : Ast → Ast
  | .mk ss => .mk (mapSections f d ss)

def mapSections (f : IxMap) (d : Nat) : List Section → List Section
  | [] => []
  | s :: ss => mapSection f d s :: mapSections f d ss

def mapSection (f : IxMap) (d : Nat) : Section → Section
  | .coreInstances xs => .coreInstances (xs.map (mapCoreInstance f d))
  | .coreTypes xs => .coreTypes (xs.map (mapCoreType f d))
  | .component c => .component (mapAst f (d + 1) c)
  | .instances xs => .instances (xs.map (mapInstance f d))
  | .aliases xs => .aliases (xs.map (mapAlias f d))
  | .types xs => .types (xs.map (mapDefType f d))
  | .canons xs => .canons (xs.map (mapCanon f d))
  | .imports xs => .imports (xs.map (mapImport f d))
  | .exports xs => .exports (xs.map (mapExport f d))
  | s => s
end

/-! ## The modules, and their extraction -/

mutual
/-- The core modules of a component, nested components included, in parser order. -/
def modulesOf : Ast → List ByteArray
  | .mk ss => modulesOfList ss

def modulesOfList : List Section → List ByteArray
  | [] => []
  | .coreModule b :: ss => b :: modulesOfList ss
  | .component c :: ss => modulesOf c ++ modulesOfList ss
  | _ :: ss => modulesOfList ss
end

/-- Extraction state: the position in `modulesOf` and the next import index. -/
structure XSt where
  pos : Nat := 0
  next : Nat := 0

mutual
/-- Replace each module whose flag is set by an outer alias of its import. -/
def extract (flags : List Bool) (d : Nat) : Ast → XSt → Ast × XSt
  | .mk ss, st => let (ss', st') := extractList flags d ss st; (.mk ss', st')

def extractList (flags : List Bool) (d : Nat) : List Section → XSt → List Section × XSt
  | [], st => ([], st)
  | .coreModule b :: ss, st =>
    let (s, st') : Section × XSt :=
      if flags[st.pos]?.getD false then
        (.aliases [⟨.core .module, .outer d st.next⟩], { pos := st.pos + 1, next := st.next + 1 })
      else (.coreModule b, { st with pos := st.pos + 1 })
    let (ss', st'') := extractList flags d ss st'
    (s :: ss', st'')
  | .component c :: ss, st =>
    let (c', st') := extract flags (d + 1) c st
    let (ss', st'') := extractList flags d ss st'
    (.component c' :: ss', st'')
  | s :: ss, st =>
    let (ss', st') := extractList flags d ss st
    (s :: ss', st')
end

/-! ## `component-name` sections -/

section Names
open Silmaril.Parse.ByteParse

/-- Read a LEB128 `u32` at `i`. -/
def readU32 (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  match (u32 : Parser Nat) b b.size i with
  | Res.ok n j => some (n, j)
  | Res.err _ => none

/-- Read `n` (index, name) pairs of a name map at `i`, up to `e`. -/
def readNameMap (b : ByteArray) (e : Nat) : Nat → Nat → Option (List (Nat × List UInt8) × Nat)
  | 0, i => some ([], i)
  | n + 1, i => do
    let (idx, i) ← readU32 b i
    let (len, i) ← readU32 b i
    if i + len > e then none
    let nm := (b.extract i (i + len)).toList
    let (rest, j) ← readNameMap b e n (i + len)
    pure ((idx, nm) :: rest, j)

/-- Rename one `sort names` subsection (contents `c`) whose sort is a core module (`0x00 0x11`)
or a core type (`0x00 0x10`) at depth `d`; any other subsection is unchanged. -/
def renameSub (f : IxMap) (d : Nat) (c : ByteArray) : Option (List UInt8) := do
  if c.size < 2 || c[0]! != 0x00 then return c.toList
  let g : Nat → Nat ← match c[1]! with
    | 0x11 => pure (modAt f d)
    | 0x10 => pure (tyAt f d)
    | _ => return c.toList
  let (n, i) ← readU32 c 2
  let (m, j) ← readNameMap c c.size n i
  if j != c.size then none
  let body ← Enc.vec (fun (p : Nat × List UInt8) => do
    let a ← Enc.u32 (g p.1)
    let l ← Enc.u32 p.2.length
    pure (a ++ l ++ p.2)) m
  pure ([(0x00 : UInt8), c[1]!] ++ body)

/-- Rename every subsection of a `component-name` section's contents; `none` when malformed. -/
def renameSubs (f : IxMap) (d : Nat) (b : ByteArray) : Nat → Nat → Option (List UInt8)
  | 0, _ => some []
  | fuel + 1, i =>
    if i ≥ b.size then some []
    else do
      let id := b[i]!
      let (sz, j) ← readU32 b (i + 1)
      if j + sz > b.size then none
      let c := b.extract j (j + sz)
      let c' ← if id == 0x01 then renameSub f d c else some c.toList
      let s ← Enc.u32 c'.length
      let rest ← renameSubs f d b fuel (j + sz)
      pure ((id :: s) ++ c' ++ rest)

end Names

mutual
/-- Rename the `component-name` sections of a component at depth `d` (a malformed one is kept). -/
def renameNames (f : IxMap) (d : Nat) : Ast → Ast
  | .mk ss => .mk (renameNamesList f d ss)

def renameNamesList (f : IxMap) (d : Nat) : List Section → List Section
  | [] => []
  | .custom n data :: ss =>
    let data' := if n == "component-name" then
        match renameSubs f d data data.size 0 with
        | some l => ⟨l.toArray⟩
        | none => data
      else data
    .custom n data' :: renameNamesList f d ss
  | .component c :: ss => .component (renameNames f (d + 1) c) :: renameNamesList f d ss
  | s :: ss => s :: renameNamesList f d ss
end

/-! ## Module types of the extracted modules -/

open Silmaril.Wasm in
/-- A core value type of a module, as the component binary has them. -/
def valType : ValType → Except String CoreValType
  | .num (.int .i32) => .ok .i32
  | .num (.int .i64) => .ok .i64
  | .num (.float .f32) => .ok .f32
  | .num (.float .f64) => .ok .f64
  | .vec .v128 => .ok .v128
  | .ref ⟨true, .abstract .func⟩ => .ok .funcref
  | .ref ⟨true, .abstract .extern⟩ => .ok .externref
  | _ => .error "unsupported core type to translate"

open Silmaril.Wasm in
def limits (a : AddrType) (l : Silmaril.Wasm.Limits) : Except String Component.Binary.Limits :=
  match a with
  | .i32 => .ok ⟨l.min.val, l.max.map (·.val)⟩
  | .i64 => .error "64-bit memories and tables are not supported in module types here"

/-- The interner of `CoreTypeInterner`: the core type section being built, and the outer index
of each function type already in it. -/
structure Interner where
  section_ : List CoreType := []
  intern : List (CoreFuncType × Nat) := []

/-- A module type being built (`ModuleTypeCreator`). -/
structure Creator where
  decls : List ModuleDecl := []
  intern : List (CoreFuncType × Nat) := []
  count : Nat := 0

/-- `ModuleTypeCreator::convert_func`: the local index of a function type in the module type,
aliased from the outer section (added there on first use). -/
def convertFunc (ft : CoreFuncType) (it : Interner) (cr : Creator) : Nat × Interner × Creator :=
  match cr.intern.lookup ft with
  | some l => (l, it, cr)
  | none =>
    let (o, it') := match it.intern.lookup ft with
      | some o => (o, it)
      | none =>
        let o := it.section_.length
        (o, ({ section_ := it.section_ ++ [CoreType.func ft], intern := it.intern ++ [(ft, o)] } : Interner))
    let cr' : Creator :=
      { decls := cr.decls ++ [ModuleDecl.alias 1 o], intern := cr.intern ++ [(ft, cr.count)], count := cr.count + 1 }
    (cr.count, it', cr')

open Silmaril.Wasm in
/-- The function type at type index `t` of a module: a final type with no supertypes. -/
def funcTypeAt (m : Module) (t : Nat) : Except String CoreFuncType := do
  match m.typeDefinitions[t]? with
  | some ⟨true, [], .func ft⟩ =>
    pure ⟨← ft.params.mapM valType, ← ft.results.mapM valType⟩
  | _ => throw "unsupported core type to translate"

open Silmaril.Wasm in
/-- `convert_entity_type`: the description of an extern type in the module type. -/
def entity (m : Module) (t : ExternType) (it : Interner) (cr : Creator) :
    Except String (CoreImportDesc × Interner × Creator) := do
  match t with
  | .func ti =>
    let ft ← funcTypeAt m ti.value.val
    let (l, it, cr) := convertFunc ft it cr
    pure (.func l, it, cr)
  | .tag ti =>
    let ft ← funcTypeAt m ti.value.val
    let (l, it, cr) := convertFunc ft it cr
    pure (.tag l, it, cr)
  | .table tt =>
    pure (.table (← valType (.ref tt.element)) (← limits tt.address tt.limits), it, cr)
  | .memory mt => pure (.memory (← limits mt.address mt.limits), it, cr)
  | .global gt => pure (.global (← valType gt.value) (gt.mutability == .var), it, cr)

open Silmaril.Wasm in
/-- The extern type of an export. -/
def exportType (m : Module) : ExternIdx → Except String ExternType
  | .func i => match m.functionTypes[i.value.val]? with
    | some t => .ok (.func t)
    | none => .error "export index out of bounds"
  | .table i =>
    let ts := (m.imports.filterMap fun im => match im.type with | .table t => some t | _ => none) ++
      m.tables.map (·.type)
    match ts[i.value.val]? with | some t => .ok (.table t) | none => .error "export index out of bounds"
  | .memory i =>
    let ts := (m.imports.filterMap fun im => match im.type with | .memory t => some t | _ => none) ++
      m.memories
    match ts[i.value.val]? with | some t => .ok (.memory t) | none => .error "export index out of bounds"
  | .global i =>
    let ts := (m.imports.filterMap fun im => match im.type with | .global t => some t | _ => none) ++
      m.globals.map (·.type)
    match ts[i.value.val]? with | some t => .ok (.global t) | none => .error "export index out of bounds"
  | .tag i =>
    let ts := (m.imports.filterMap fun im => match im.type with | .tag t => some t | _ => none) ++
      m.tags
    match ts[i.value.val]? with | some t => .ok (.tag t) | none => .error "export index out of bounds"

/-- The module type of one extracted module (imports, then exports, in order), added to the
interner; returns its index in the core type section. -/
def moduleType (bytes : ByteArray) (it : Interner) : Except String (Nat × Interner) := do
  let some m := Silmaril.Wasm.Perf.CoreDecode.decodeF bytes
    | throw "failed to validate core wasm module found in component"
  let mut it := it
  let mut cr : Creator := {}
  for im in m.imports do
    let (desc, it', cr') ← entity m im.type it cr
    it := it'
    cr := { cr' with decls := cr'.decls ++ [.import im.moduleName im.name desc] }
  for ex in m.exports do
    let (desc, it', cr') ← entity m (← exportType m ex.index) it cr
    it := it'
    cr := { cr' with decls := cr'.decls ++ [.export ex.name desc] }
  pure (it.section_.length, { it with section_ := it.section_ ++ [.module cr.decls] })

/-! ## The subcommand -/

def isComponent (b : ByteArray) : Bool :=
  b.size ≥ 8 && b[0]! == 0x00 && b[1]! == 0x61 && b[2]! == 0x73 && b[3]! == 0x6d &&
    b[6]! == 0x01 && b[7]! == 0x00

/-- **`wasm-tools component unbundle --threshold T`**: the output bytes and the extracted
modules, in order (written as `unbundled-moduleN.wasm`). -/
def unbundle (input : ByteArray) (threshold : Nat) : Except String (ByteArray × List ByteArray) := do
  if !isComponent input then return (input, [])
  let c ← match Silmaril.Wasm.Component.Codec.decodeLax input with
    | .ok c => pure c
    | .error _ => throw "failed to parse the component (outside the verified component grammar)"
  let mods := modulesOf c
  let flags := mods.map fun m => decide (m.size > threshold)
  let ext := mods.filter fun m => decide (m.size > threshold)
  let mut it : Interner := {}
  let mut tys : List Nat := []
  for m in ext do
    let (ti, it') ← moduleType m it
    it := it'
    tys := tys ++ [ti]
  let k := IxMap.shift it.section_.length ext.length
  let (c', _) := extract flags 0 (renameNames k 0 (mapAst k 0 c)) {}
  let imports : List Import := tys.zipIdx.map fun (ti, n) =>
    ⟨⟨s!"unbundled-module{n}", .plain0⟩, .coreModule ti⟩
  let out : Ast := .mk (.coreTypes it.section_ :: .imports imports :: c'.sections)
  match Silmaril.Wasm.Component.BinaryP3.encode out with
  | some b => pure (b, ext)
  | none => throw "a number or size exceeds 2^32"

end Silmaril.Wasm.Tools.Component.Unbundle

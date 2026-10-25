module

public import Silmaril.Wasm.V2.Instructions
public import Silmaril.Wasm.Declaration

/-!
# WebAssembly 2.0 modules

Transcribed from `specification/wasm-2.0/1-syntax.spectec`, section `Modules`
(`1-syntax:534-578`), and `2-syntax-aux.spectec` (`2-syntax-aux:80-97`), at
WebAssembly/spec revision `608711107b7f1edb13efd57b7d79b49477462d36`.

**Deviation: import descriptors.** `1-syntax:564` writes
`import = IMPORT name name externtype`, with `externtype` carrying a whole
`functype` for function imports. The binary format encodes a *type index*
(`A-binary` would need `0x00 x:Btypeidx`; `A-binary:139` instead writes
`0x00 ft:Bfunctype` and marks it `;; TODO: typeidx`), the W3C 2.0 text has
`importdesc ::= func typeidx | …`, the reference interpreter reads a type
index, and Core 3.0 SpecTec has been fixed to `0x00 x:Btypeidx => FUNC (_IDX x)`
(`5.2-binary.types:103`). We therefore carry an `ImportDesc` with a `TypeIdx`
and resolve it against the type section with `importType?`; the *resolved*
`ExternType` is SpecTec's `externtype` unchanged. See `Silmaril.Wasm.V2.Validation`.
-/

@[expose] public section

namespace Silmaril.Wasm.V2

/-- `externidx ::= FUNC funcidx | GLOBAL globalidx | TABLE tableidx | MEM memidx`
(`1-syntax:560`). -/
inductive ExternIdx where
  | func (index : FuncIdx)
  | global (index : GlobalIdx)
  | table (index : TableIdx)
  | memory (index : MemIdx)
  deriving DecidableEq, Repr

/-- The syntactic import descriptor; see the module documentation. -/
inductive ImportDesc where
  | func (type : TypeIdx)
  | table (type : TableType)
  | memory (type : MemoryType)
  | global (type : GlobalType)
  deriving DecidableEq, Repr

/-- `import ::= IMPORT name name externtype` (`1-syntax:564`). -/
structure Import where
  moduleName : String
  name : String
  desc : ImportDesc
  deriving DecidableEq, Repr

/-- `export ::= EXPORT name externidx` (`1-syntax:562`). -/
structure Export where
  name : String
  index : ExternIdx
  deriving DecidableEq, Repr

/-- `func ::= FUNC typeidx local* expr` (`1-syntax:545`), with
`local ::= LOCAL valtype` (`1-syntax:543`). -/
abbrev Func := Declaration.Func ValType Expr

namespace Func
abbrev mk := @Declaration.Func.mk ValType Expr
@[simp] abbrev type (f : Func) := Declaration.Func.type f
@[simp] abbrev locals (f : Func) := Declaration.Func.locals f
@[simp] abbrev body (f : Func) := Declaration.Func.body f
end Func

/-- `global ::= GLOBAL globaltype expr` (`1-syntax:547`). -/
abbrev Global := Declaration.Global GlobalType Expr

namespace Global
abbrev mk := @Declaration.Global.mk GlobalType Expr
@[simp] abbrev type (g : Global) := Declaration.Global.type g
@[simp] abbrev init (g : Global) := Declaration.Global.init g
end Global

/-- `elemmode ::= ACTIVE tableidx expr | PASSIVE | DECLARE` (`1-syntax:538`). -/
inductive ElemMode where
  | active (table : TableIdx) (offset : Expr)
  | passive
  | declare
  deriving Repr

/-- `datamode ::= ACTIVE memidx expr | PASSIVE` (`1-syntax:539`). -/
inductive DataMode where
  | active (memory : MemIdx) (offset : Expr)
  | passive
  deriving Repr

/-- `elem ::= ELEM reftype expr* elemmode` (`1-syntax:553`). -/
structure Elem where
  type : RefType
  init : List Expr
  mode : ElemMode
  deriving Repr

/-- `data ::= DATA byte* datamode` (`1-syntax:555`). -/
structure Data where
  bytes : ByteArray
  mode : DataMode
  deriving Repr

/-- `module ::= MODULE type* import* func* global* table* mem* elem* data*
start? export*` (`1-syntax:567`). -/
structure Module where
  types : List FuncType := []
  imports : List Import := []
  funcs : List Func := []
  globals : List Global := []
  tables : List TableType := []
  memories : List MemoryType := []
  elems : List Elem := []
  data : List Data := []
  start : Option FuncIdx := none
  exports : List Export := []
  deriving Repr

/-! ## Index spaces

Imports precede definitions in every index space. -/

namespace Module

/-- The resolved external type of an import descriptor, against a type section.
Corresponds to SpecTec's already-resolved `externtype` in `import`. -/
def importType? (types : List FuncType) : ImportDesc → Option ExternType
  | .func i => (types[i.toNat]?).map ExternType.func
  | .table t => some (.table t)
  | .memory t => some (.memory t)
  | .global t => some (.global t)

def importedFunctions (m : Module) : List TypeIdx :=
  m.imports.filterMap fun i => match i.desc with | .func t => some t | _ => none

def importedGlobals (m : Module) : List GlobalType :=
  m.imports.filterMap fun i => match i.desc with | .global t => some t | _ => none

def importedTables (m : Module) : List TableType :=
  m.imports.filterMap fun i => match i.desc with | .table t => some t | _ => none

def importedMemories (m : Module) : List MemoryType :=
  m.imports.filterMap fun i => match i.desc with | .memory t => some t | _ => none

/-- `$funcsxt(ixt*) ft*`: imported function types followed by defined ones. -/
def functionTypes (m : Module) : List TypeIdx :=
  m.importedFunctions ++ m.funcs.map Declaration.Func.type

def globalTypes (m : Module) : List GlobalType :=
  m.importedGlobals ++ m.globals.map Declaration.Global.type

def tableTypes (m : Module) : List TableType := m.importedTables ++ m.tables

def memoryTypes (m : Module) : List MemoryType := m.importedMemories ++ m.memories

/-- `C.ELEMS`: the element type of each element segment. -/
def elemTypes (m : Module) : List RefType := m.elems.map Elem.type

@[simp] theorem functionTypes_length (m : Module) :
    m.functionTypes.length = m.importedFunctions.length + m.funcs.length := by
  simp [functionTypes]

end Module

/-! ## Free data indices

`$dataidx_instr`, `$dataidx_instrs`, `$dataidx_expr`, `$dataidx_func`,
`$dataidx_funcs` (`2-syntax-aux:80-97`). The binary format uses
`$dataidx_funcs(func*) = eps` as the condition under which the data count
section may be absent (`A-binary:941`).

**Deviation: `$dataidx_instr` must recurse.** `2-syntax-aux:81-87` defines

```
def $dataidx_instr(MEMORY.INIT x) = x
def $dataidx_instr(DATA.DROP x) = x
def $dataidx_instr(in) = eps
def $dataidx_instrs(instr instr'*) = $dataidx_instr(instr) $dataidx_instrs(instr'*)
```

which never looks inside the body of a `BLOCK`, `LOOP` or `IF`. Taken literally,
a module whose only `memory.init` is nested inside a block has
`$dataidx_funcs(func*) = eps` and may omit the data count section. The reference
interpreter rejects that module: `interpreter/binary/decode.ml:1299-1301` requires
a data count section whenever `Free.(func f).datas` is non-empty, and
`interpreter/syntax/free.ml:135-193` recurses through `Block`, `Loop` and `If`.
Wasm 3.0 SpecTec replaces the definition with the recursive
`$free_list($free_func(func)*).DATAS` (`wasm-3.0/1.4-syntax.modules.spectec:145`).
We use the recursive reading. See `Silmaril.Wasm.V2.Validation`. -/

namespace Instr

/-- `$dataidx_instr(instr)` (`2-syntax-aux:80-83`), recursing into nested bodies;
see the section documentation. -/
def dataIdxs : Instr → List DataIdx
  | .memoryInit x => [x]
  | .dataDrop x => [x]
  | .block _ body | .loop _ body => body.attach.flatMap fun i => dataIdxs i.val
  | .if_ _ left right =>
      (left.attach.flatMap fun i => dataIdxs i.val) ++
        (right.attach.flatMap fun i => dataIdxs i.val)
  | _ => []
  termination_by instruction => sizeOf instruction
  decreasing_by
    all_goals exact Nat.lt_trans (List.sizeOf_lt_of_mem i.property) (by simp; omega)

/-- The literal, non-recursive reading of `2-syntax-aux:80-83`, kept so that the
deviation above has a checkable counterexample. -/
def dataIdxsShallow : Instr → List DataIdx
  | .memoryInit x => [x]
  | .dataDrop x => [x]
  | _ => []

end Instr

namespace Expr

/-- `$dataidx_expr(expr)` (`2-syntax-aux:89-90`). -/
def dataIdxs (e : Expr) : List DataIdx := e.flatMap Instr.dataIdxs

/-- The literal, non-recursive reading; see `Instr.dataIdxsShallow`. -/
def dataIdxsShallow (e : Expr) : List DataIdx := e.flatMap Instr.dataIdxsShallow

end Expr

namespace Module

/-- `$dataidx_funcs(func*)` (`2-syntax-aux:95-97`). -/
def funcDataIdxs (m : Module) : List DataIdx :=
  m.funcs.flatMap fun f => Expr.dataIdxs (Declaration.Func.body f)

end Module

/-- The two readings differ: a nested `memory.init` is invisible to the literal
`2-syntax-aux:80-83` definition. -/
theorem dataIdxs_ne_dataIdxsShallow :
    ∃ i : Instr, Instr.dataIdxs i ≠ Instr.dataIdxsShallow i :=
  ⟨.block (.result none) [.memoryInit ⟨0, Nat.two_pow_pos 32⟩], by
    simp [Instr.dataIdxs, Instr.dataIdxsShallow]⟩

end Silmaril.Wasm.V2

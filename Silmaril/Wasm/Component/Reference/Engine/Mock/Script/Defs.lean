module

public import Silmaril.Wasm.Component.Engine.Interface

/-!
# Script programs of the Mock core engine

The reference test suite `run_tests.py` (`design/mvp/canonical-abi/run_tests.py` of component-model
a25fc0b, next to the pinned `definitions.py`)
implements core functions as Python lambdas that call canon built-ins and read or write
memories of arbitrary size and address type (`'i32'` or `'i64'`). The Mock engine
(`Engine/Mock.lean`) transcribes such functions as *Script* programs: a small first-order
register language whose modules are plain data with decidable equality. It is not WebAssembly:
it has no operand stack, no structured control and no validation beyond scoping of indices
(`Module.validate`). It exists so that component-level tests can be ported, and so that the
canonical ABI's memory64 paths can be executed (Lime1 and V1 only have i32 memories).

* Registers are `List FlatValue`, indexed by `Nat`. Reading a register at or beyond the
  current register-file length (one past the highest register written so far) traps; writing
  past the end pads the gap with `i32` zeros, so those intermediate registers read as `i32` 0.
* `call f args results` calls the function with module-local index `f` (imports first, as in
  WebAssembly); `callIndirect` goes through a funcref table (trapping, like `call_indirect`,
  unless the callee's type equals the declared type) and `callAddr` through a function address
  held in a register (checking only the argument types). Host functions become callouts of the
  engine.
* Memory accesses name a module-local memory, a pointer register (which must hold an integer of
  the memory's address type) and a static offset; bounds are checked on the natural-number
  effective address, so an i64 address is never truncated.
* Control flow is by explicit program counter (`branchIfZero`, `jump`), so loops are allowed;
  falling off the end of the code traps.

Sizes of Mock memories are in BYTES (not pages), including in the `CoreExternType.memory`
limits that the engine reports for them. Mock tables carry an address type (`i32` or `i64`), so
the memory64/table64 paths (`thread.new-indirect` with an `i64` table index) can be exercised.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Mock

/-- Binary integer operators. Comparisons produce an `i32` 0 or 1; shifts take the shift
amount modulo the width, as in WebAssembly. -/
inductive BinOp where
  | add | sub | mul | and | or | xor | shl | shrU
  | eq | ne | ltU | leU | gtU | geU
  deriving DecidableEq, Repr

/-- Script instructions. Register, function, memory, table and global operands are `Nat`
indices; function, memory, table and global indices are module-local. -/
inductive Instr where
  /-- `r := v`. -/
  | const (r : Nat) (v : FlatValue)
  /-- `r := args[i]`. -/
  | arg (r i : Nat)
  /-- `dst := src`. -/
  | mov (dst src : Nat)
  /-- `dst := a op b` at integer type `t`. -/
  | binop (t : IntType) (op : BinOp) (dst a b : Nat)
  /-- `dst := (a == 0)` as an `i32`. -/
  | eqz (t : IntType) (dst a : Nat)
  /-- `dst := i32.wrap_i64 a`. -/
  | wrap (dst a : Nat)
  /-- `dst := i64.extend_i32_u a`. -/
  | extendU (dst a : Nat)
  /-- Call module function `f` with the values of registers `args`; the results are written
  to registers `results`. -/
  | call (f : Nat) (args results : List Nat)
  /-- Call the function stored at the table index held in register `idx` of table `tbl`. The
  index register must hold an integer of the table's address type; as in `call_indirect`, the
  call traps unless the callee's type is exactly `ft`. -/
  | callIndirect (tbl idx : Nat) (ft : V1.FuncType) (args results : List Nat)
  /-- Call the function whose store address is held (as an integer) in register `fReg`. There is
  no signature check beyond the argument value types matching the callee's parameters (a result
  count mismatch traps when the results are written back). -/
  | callAddr (fReg : Nat) (args results : List Nat)
  /-- `dst := zero-extended little-endian load of n bytes` at integer type `t`
  (`n ≤ t.width / 8`). -/
  | load (t : IntType) (n dst mem ptr offset : Nat)
  /-- Store the low `n` bytes of integer register `src` (little-endian). -/
  | store (n mem ptr offset src : Nat)
  /-- Write literal bytes. -/
  | memWrite (mem ptr offset : Nat) (bytes : List UInt8)
  /-- `dst := memory size in bytes`, as an integer of the memory's address type. -/
  | memSize (dst mem : Nat)
  /-- `dst := global g`. -/
  | globalGet (dst g : Nat)
  /-- `global g := src` (traps if immutable or of another type). -/
  | globalSet (g src : Nat)
  /-- If register `r` holds zero, continue at `target`, else at the next instruction. -/
  | branchIfZero (r target : Nat)
  /-- Continue at `target`. -/
  | jump (target : Nat)
  /-- Return the values of registers `regs`. -/
  | ret (regs : List Nat)
  | trap
  deriving DecidableEq, Repr

/-- `dst := i32.load (mem, ptr + offset)`. -/
abbrev Instr.load32 (dst mem ptr offset : Nat) : Instr := .load .i32 4 dst mem ptr offset

/-- `i32.store (mem, ptr + offset) src` (the low 4 bytes of `src`). -/
abbrev Instr.store32 (mem ptr offset src : Nat) : Instr := .store 4 mem ptr offset src

/-- A Script function: its flat core type and its code. -/
structure Func where
  type : V1.FuncType
  code : List Instr
  deriving DecidableEq, Repr

/-- A module-local extern index (the target of an export). -/
inductive ExternKindIdx where
  | func (i : Nat)
  | memory (i : Nat)
  | table (i : Nat)
  | global (i : Nat)
  deriving DecidableEq, Repr

/-- A Script module. Imports are positional; each index space lists imports first.
Memories are `(address type, size in bytes)`; tables are `(address type, entries)` whose
entries are module-local function indices (`none` is a null entry); globals are
`(initial value, mutable)`. The start function is a module-local function index of type
`[] → []`. -/
structure Module where
  imports : List (String × String × CoreExternType) := []
  funcs : List Func := []
  memories : List (AddrType × Nat) := []
  tables : List (AddrType × List (Option Nat)) := []
  globals : List (FlatValue × Bool) := []
  exports : List (String × ExternKindIdx) := []
  start : Option Nat := none
  deriving DecidableEq, Repr

namespace Module

variable (m : Module)

def importedFuncTypes : List V1.FuncType :=
  m.imports.filterMap fun | (_, _, .func t) => some t | _ => none

def importedMemories : List CoreExternType :=
  m.imports.filterMap fun | (_, _, t@(.memory ..)) => some t | _ => none

def importedTables : List CoreExternType :=
  m.imports.filterMap fun | (_, _, t@(.table ..)) => some t | _ => none

def importedGlobals : List CoreExternType :=
  m.imports.filterMap fun | (_, _, t@(.global ..)) => some t | _ => none

/-- The function index space's types. -/
def funcTypes : List V1.FuncType := m.importedFuncTypes ++ m.funcs.map (·.type)

/-- The memory index space's types (Mock limits in bytes). -/
def memoryTypes : List CoreExternType :=
  m.importedMemories ++ m.memories.map fun (a, n) => .memory a n (some n)

def tableTypes : List CoreExternType :=
  m.importedTables ++ m.tables.map fun (a, es) => .table a es.length (some es.length)

def globalTypes : List CoreExternType :=
  m.importedGlobals ++ m.globals.map fun (v, mu) => .global v.type mu

/-- The type of a module-local extern index. -/
def externIdxType? : ExternKindIdx → Option CoreExternType
  | .func i => (m.funcTypes[i]?).map .func
  | .memory i => m.memoryTypes[i]?
  | .table i => m.tableTypes[i]?
  | .global i => m.globalTypes[i]?

/-- Exports with their types (exports with out-of-range indices are dropped; they make the
module invalid). -/
def exportTypes : List (String × CoreExternType) :=
  m.exports.filterMap fun (n, e) => (m.externIdxType? e).map (n, ·)

/-- Scoping of one instruction: all module-local indices in range, jump targets at most the
code length. Register indices are unconstrained. -/
def instrWellScoped (len : Nat) : Instr → Bool
  | .call f _ _ => decide (f < m.funcTypes.length)
  | .callIndirect t _ _ _ _ => decide (t < m.tableTypes.length)
  | .load _ _ _ mem _ _ | .store _ mem _ _ _ | .memWrite mem _ _ _ | .memSize _ mem =>
    decide (mem < m.memoryTypes.length)
  | .globalGet _ g | .globalSet g _ => decide (g < m.globalTypes.length)
  | .branchIfZero _ l | .jump l => decide (l ≤ len)
  | _ => true

/-- Decidable validity of a Script module: imports are functions, memories, tables or
globals (no tags); instructions are well scoped; table entries, exports and the start
function are in range; export names are distinct (as in core validation); and the start
function has type `[] → []`. -/
def validate : Bool :=
  m.imports.all (fun | (_, _, .tag _) => false | _ => true) &&
  m.funcs.all (fun f => f.code.all (m.instrWellScoped f.code.length)) &&
  m.tables.all (fun (_, es) =>
    es.all fun | none => true | some i => decide (i < m.funcTypes.length)) &&
  m.exports.all (fun (_, e) => (m.externIdxType? e).isSome) &&
  decide (m.exports.map (·.1)).Nodup &&
  (match m.start with
    | none => true
    | some i => decide (m.funcTypes[i]? = some ⟨[], []⟩))

/-- Module validity. -/
def Valid : Prop := m.validate = true

instance : Decidable m.Valid := inferInstanceAs (Decidable (m.validate = true))

end Module

end Silmaril.Wasm.Component.Engine.Mock

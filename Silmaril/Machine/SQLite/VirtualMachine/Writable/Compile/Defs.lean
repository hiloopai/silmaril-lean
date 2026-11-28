module

public import Silmaril.Machine.SQLite.VirtualMachine.Writable.Defs

/-! A small statement language, its source footprint, and a compilation
relation into raw writable VDBE bytecode.

The statements name tables by stable `TableId`. `Stmt.footprint` is computed
from the statement alone: it does not look at a catalog, at generated code, at
an execution trace or at any certificate. The compilation relation `Compiles`
is relational in where it finds each table: any slot and root that the catalog
resolves to the table may be used, so aliased slots are legitimate targets.
Code shapes follow SQLite's usual layout (an `Init` jump to trailing
`Transaction`s that return with `Goto`), but these templates are hand-written
for this model. They are not SQLite's code generator and make no claim about
the programs SQLite emits for the corresponding SQL. -/

@[expose] public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile

open Silmaril.Formats.Sqlite

/-- Constants an `INSERT … VALUES` can load with modeled opcodes. -/
inductive Literal where
  | integer (value : Int64)
  | text (value : String)
  | null
  deriving DecidableEq

def Literal.value : Literal → Value
  | .integer value => .integer value
  | .text value => .text value
  | .null => .null

inductive Stmt where
  /-- `SELECT c0, …, c(width-1) FROM table` -/
  | scan (table : TableId) (width : Nat)
  /-- `INSERT INTO table VALUES (values)` with a fresh rowid. -/
  | insert (table : TableId) (values : List Literal)
  /-- `DELETE FROM table WHERE rowid = key` -/
  | deleteRowid (table : TableId) (key : Int64)
  /-- `INSERT INTO target SELECT c0, …, c(width-1) FROM source` -/
  | copy (source target : TableId) (width : Nat)
  deriving DecidableEq

def readTouches (table : TableId) : List Touch := [.db table.db .read, .table table .read]
def writeTouches (table : TableId) : List Touch := [.db table.db .write, .table table .write]

/-- Source footprint, by cases on the statement only. -/
def Stmt.footprint : Stmt → List Touch
  | .scan table _ => readTouches table
  | .insert table _ => writeTouches table
  | .deleteRowid table _ => writeTouches table
  | .copy source target _ => readTouches source ++ writeTouches target

/-- The table a statement writes, if any. -/
def Stmt.target? : Stmt → Option TableId
  | .scan _ _ => none
  | .insert table _ => some table
  | .deleteRowid table _ => some table
  | .copy _ target _ => some target

/-- A database slot and root page at which a table is reached. -/
structure Location where
  slot : Nat
  root : Nat

/-- `OpenRead`/`OpenWrite` need a positive immediate root. -/
def Locates (cat : Catalog) (location : Location) (table : TableId) : Prop :=
  0 < location.root ∧ cat.resolve location.slot location.root = some table

instance (cat : Catalog) (location : Location) (table : TableId) :
    Decidable (Locates cat location table) :=
  inferInstanceAs (Decidable (_ ∧ _))

namespace Code

def named (name : String) (p1 p2 p3 : Int := 0) (p4 : Vdbe.P4 := .none) : RawInstruction :=
  {opcode := .name name, p1 := p1, p2 := p2, p3 := p3, p4 := p4}

def init (target : Nat) : RawInstruction := named "Init" 0 target
def goto (target : Nat) : RawInstruction := named "Goto" 0 target
def halt : RawInstruction := named "Halt"
def transaction (slot : Nat) (mode : Mode) : RawInstruction :=
  named "Transaction" slot (match mode with | .read => 0 | .write => 1)
def openRead (cursor : Nat) (location : Location) : RawInstruction :=
  named "OpenRead" cursor location.root location.slot
def openWrite (cursor : Nat) (location : Location) : RawInstruction :=
  named "OpenWrite" cursor location.root location.slot
def rewind (cursor target : Nat) : RawInstruction := named "Rewind" cursor target
def next (cursor target : Nat) : RawInstruction := named "Next" cursor target
def column (cursor index destination : Nat) : RawInstruction :=
  named "Column" cursor index destination
def resultRow (first count : Nat) : RawInstruction := named "ResultRow" first count
def newRowid (cursor destination : Nat) : RawInstruction := named "NewRowid" cursor destination
def makeRecord (first count destination : Nat) : RawInstruction :=
  named "MakeRecord" first count destination
def insert (cursor record key : Nat) : RawInstruction := named "Insert" cursor record key
def delete (cursor : Nat) : RawInstruction := named "Delete" cursor
def seekRowid (cursor target key : Nat) : RawInstruction := named "SeekRowid" cursor target key
def int64 (value : Int64) (destination : Nat) : RawInstruction :=
  named "Int64" 0 destination 0 (.integer value.toInt)

def load (destination : Nat) : Literal → RawInstruction
  | .integer value => int64 value destination
  | .text value => named "String8" 0 destination 0 (.text value)
  | .null => named "Null" 0 destination destination

def columns (cursor width first : Nat) : List RawInstruction :=
  (List.range width).map fun index => column cursor index (first + index)

def loads : Nat → List Literal → List RawInstruction
  | _, [] => []
  | first, value :: rest => load first value :: loads (first + 1) rest

/-- Registers `1 … width` hold the row. -/
def scan (location : Location) (width : Nat) : RawProgram :=
  (([init (6 + width), openRead 0 location, rewind 0 (5 + width)] ++ columns 0 width 1 ++
    [resultRow 1 width, next 0 3, halt, transaction location.slot .read, goto 1]) : List _).toArray

/-- Register `1` holds the rowid, `2 … n+1` the values, `n+2` the record. -/
def insertValues (location : Location) (values : List Literal) : RawProgram :=
  let n := values.length
  (([init (6 + n), openWrite 0 location, newRowid 0 1] ++ loads 2 values ++
    [makeRecord 2 n (n + 2), Code.insert 0 (n + 2) 1, halt,
      transaction location.slot .write, goto 1]) : List _).toArray

def deleteRowid (location : Location) (key : Int64) : RawProgram :=
  #[init 6, openWrite 0 location, int64 key 1, seekRowid 0 5 1, delete 0, halt,
    transaction location.slot .write, goto 1]

/-- Cursor `0` reads, cursor `1` writes; registers `2 … width+1` hold the row. -/
def copy (source target : Location) (width : Nat) : RawProgram :=
  (([init (9 + width), openRead 0 source, openWrite 1 target, rewind 0 (8 + width)] ++
    columns 0 width 2 ++
    [makeRecord 2 width (2 + width), newRowid 1 1, Code.insert 1 (2 + width) 1, next 0 4, halt,
      transaction source.slot .read, transaction target.slot .write, goto 1]) : List _).toArray

end Code

/-- Compilation relation. Text literals must be NUL-free, as `String8` requires. -/
inductive Compiles (cat : Catalog) : Stmt → RawProgram → Prop where
  | scan {table location width} (locates : Locates cat location table) :
      Compiles cat (.scan table width) (Code.scan location width)
  | insert {table location values} (locates : Locates cat location table)
      (nulFree : ∀ text, Literal.text text ∈ values → text.contains '\x00' = false) :
      Compiles cat (.insert table values) (Code.insertValues location values)
  | deleteRowid {table location key} (locates : Locates cat location table) :
      Compiles cat (.deleteRowid table key) (Code.deleteRowid location key)
  | copy {source target sourceAt targetAt width}
      (sourceLocates : Locates cat sourceAt source) (targetLocates : Locates cat targetAt target) :
      Compiles cat (.copy source target width) (Code.copy sourceAt targetAt width)

/-- A script compiles statement by statement. -/
inductive CompilesScript (cat : Catalog) : List Stmt → List RawProgram → Prop where
  | nil : CompilesScript cat [] []
  | cons {stmt stmts code codes} : Compiles cat stmt code → CompilesScript cat stmts codes →
      CompilesScript cat (stmt :: stmts) (code :: codes)

/-- Footprint of a script: the union of its statements' source footprints. -/
def scriptFootprint (stmts : List Stmt) : Footprint :=
  Footprint.ofList (stmts.flatMap Stmt.footprint)

/-! ### Bridge obligations

These are stated, not discharged. Nothing in this repository proves them for
SQLite, and none of them is a refinement claim. `Thms` shows what each one
yields when assumed. -/

/-- Compilation provenance: the program given to the VM is the `Compiles`
image of a statement whose source footprint lies in `footprint`. For SQLite,
this is a claim about `sqlite3_prepare` and its code generator. -/
def CompilationProvenance (footprint : Footprint) (cat : Catalog) (code : RawProgram) : Prop :=
  ∃ stmt, (∀ touch ∈ stmt.footprint, footprint.allows touch = true) ∧ Compiles cat stmt code

/-- Callback provenance: every transition of an instruction the model does not
decode meets the fallback contract under `footprint`. That includes the
callbacks of `Function`/`PureFunc` (where `ATTACH`, `DETACH` and
`load_extension` take effect), virtual-table and subprogram opcodes. The
catalog is a run parameter, so for SQLite this also requires those callbacks
to leave slot and root resolution unchanged for the run. -/
def CallbackProvenance (footprint : Footprint) (callbacks : Fallback) : Prop :=
  FallbackSafe footprint callbacks

/-- Statements reached from `stmt` through `causes` (trigger bodies,
foreign-key actions, view expansions) and, transitively, what they cause. -/
inductive Reaches (causes : Stmt → List Stmt) (stmt : Stmt) : Stmt → Prop where
  | direct {sub} : sub ∈ causes stmt → Reaches causes stmt sub
  | step {mid sub} : Reaches causes stmt mid → sub ∈ causes mid → Reaches causes stmt sub

/-- Transitive table touch: the source footprint of `stmt` already covers
every statement it reaches. Choosing `causes` for SQLite (which triggers fire,
which cascades apply) is part of the obligation. -/
def TransitiveTouch (causes : Stmt → List Stmt) (stmt : Stmt) : Prop :=
  ∀ sub, Reaches causes stmt sub → ∀ touch ∈ sub.footprint, touch ∈ stmt.footprint

end Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile

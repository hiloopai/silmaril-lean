module

public import Silmaril.Formats.Sqlite.Vdbe.Defs

/-! A writable VDBE fragment over logical database and table identities.

The read-only core (`Silmaril.Formats.Sqlite.Vdbe`) binds a cursor to a table
snapshot and addresses tables by VM operands. Writes need more: the identity of
the table a cursor modifies has to be stable across aliases, cursors over the
same table have to see each other's writes, and an inserted row needs a record
value. This module is therefore a separate layer. It reuses the raw bytecode
carrier and the core decoder (`Vdbe.RawInstruction`, `Vdbe.decode?`), adds
decoders for six write-path opcodes, and runs everything over its own
configuration.

Opcode references follow SQLite 3.54.1 (https://www.sqlite.org/opcode.html).

Model.
* Identity. A `Catalog` resolves a database slot (the P1/P3 `iDb` operand) to a
  stable `DbId` and a root page of that database to a stable `TableKey`. Every
  policy, event and frame is stated on `TableId = (DbId, TableKey)`, never on
  slot numbers, schema names or root pages, so two slots attached to the same
  database, or two roots that name one table, cannot be used to sidestep a
  policy. The catalog is fixed for a run.
* Policy. A `Footprint` is a decidable set of `Touch`es: a transaction on a
  database in a mode, or a cursor on a table in a mode. Configured databases are
  those with some allowed database touch. The guard is checked at the three
  touch points (`Transaction`, `OpenRead`, `OpenWrite`); a denied touch is a
  fault, not a filter on the input program.
* State. `Config` holds registers (scalar values or abstract records), cursors
  with provenance (`TableId` and mode; the position is a rowid, so a cursor sees
  writes made through other cursors), the transaction mode of every opened
  database, the working store that writes modify, and the committed store.
* Commit. Simple autocommit for one statement over an in-memory store:
  `Halt 0` publishes the working store as the committed store and emits
  `commit`. A fault, a nonzero halt or exhausted fuel publishes nothing. There
  is no claim about SQLite's journals, savepoints, rollback or durability.
* Events. `touch` (a granted open), `write t` (a write attempt that changed
  the working copy of `t`), `commit`, and result rows. The theorems tie `write`
  events to the actual store transition, so they are not decorative. This
  follows the split in `Silmaril.Machine.SqliteVfs.TrackA.Write`, where write
  attempts precede a separate commit point that its rollback-journal profile
  realizes as phase-two journal deletion. Here the commit point is abstract:
  there is no journal, and relating `commit` to that deletion is a separate
  obligation. A write that faults leaves no event and no state change; a
  refused touch is visible only as the `denied` fault.
* Fallback. Raw instructions that do not decode are unmodeled. The executable
  `run` faults on them. The relation `Trace` accepts any `Fallback` transition;
  the theorems require only `FallbackSafe`.

Explicitly out of scope: schema changes (DDL, `ParseSchema`, `CreateBtree`,
`Destroy` and autovacuum root moves), so the catalog cannot change; indexes and
their consistency (index opcodes are unmodeled, and an index root may only be
catalogued as an ordinary table key); triggers, foreign-key actions and other
subprograms (`Program`, `FkCounter`); views, which SQLite expands at prepare
time; `ATTACH`, `DETACH` and `load_extension`; the temp database is an ordinary `DbId` with no special treatment; affinities,
record serialization, schema-cookie checks, change counters and hooks;
concurrency, locking and busy handling; and native code.

Opcodes versus callbacks. Opcode coverage here means the twenty constructors
of `Instr`, reached by `decode?`. `ATTACH`, `DETACH` and `load_extension` are
not opcodes: in the pinned source (`src/attach.c`, `src/func.c` at
57520227c95396ce39ba6ecaac8d475b78dd3964) `codeAttach` emits an `OP_Function`
call through `sqlite3VdbeAddFunctionCall`, whose callback is `attachFunc` or
`detachFunc`, and `load_extension()` is the SQL function `loadExt`. Such
`Function`/`PureFunc` instructions, like trigger `Program`s, are unmodeled here.
Their callback effects are constrained only by `FallbackSafe`, which cannot
change the catalog. This module has no abstract attach or extension action;
any added later is an abstraction of a callback effect, not opcode coverage. -/

@[expose] public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Writable

open Silmaril.Formats.Sqlite

abbrev RawInstruction := Vdbe.RawInstruction
abbrev RawProgram := Vdbe.RawProgram

/-- Stable logical identity of a database, independent of the slot or schema
name under which a connection currently reaches it. -/
structure DbId where
  id : Nat
  deriving DecidableEq, Repr

/-- Stable logical identity of a table within one database, independent of its
current root page. -/
structure TableKey where
  id : Nat
  deriving DecidableEq, Repr

structure TableId where
  db : DbId
  key : TableKey
  deriving DecidableEq, Repr

inductive Mode where
  | read
  | write
  deriving DecidableEq, Repr

/-- The connection's name resolution: slot `0` is `main`, slot `1` is `temp`
and later slots are attached databases in SQLite's numbering. Neither map need
be injective. -/
structure Catalog where
  slot : Nat → Option DbId
  root : DbId → Nat → Option TableKey

def Catalog.resolve (cat : Catalog) (slot root : Nat) : Option TableId := do
  let db ← cat.slot slot
  let key ← cat.root db root
  return ⟨db, key⟩

abbrev Row := List Value

/-- Rows of a rowid table in scan order. The operations keep ascending rowids
when they start from ascending rowids; safety does not depend on it. -/
abbrev Rows := List (Int × Row)

/-- `none` means the table does not exist in the store. -/
abbrev Store := TableId → Option Rows

def Store.set (store : Store) (table : TableId) (rows : Rows) : Store :=
  fun other => if other = table then some rows else store other

def Rows.lookup (key : Int) (rows : Rows) : Option Row :=
  (rows.find? fun entry => entry.1 == key).map Prod.snd

/-- The first rowid after `key` in scan order. -/
def Rows.after (key : Int) (rows : Rows) : Option Int :=
  (rows.find? fun entry => decide (key < entry.1)).map Prod.fst

def Rows.erase (key : Int) (rows : Rows) : Rows :=
  rows.filter fun entry => entry.1 != key

/-- Insert in ascending position, replacing an existing row with the same rowid
(`OP_Insert` overwrites). -/
def Rows.upsert (key : Int) (row : Row) : Rows → Rows
  | [] => [(key, row)]
  | (other, old) :: rest =>
      if key = other then (key, row) :: rest
      else if key < other then (key, row) :: (other, old) :: rest
      else (other, old) :: upsert key row rest

/-- One more than the largest rowid, or `1` for an empty table. -/
def Rows.nextRowid (rows : Rows) : Int :=
  match (rows.map Prod.fst).max? with
  | none => 1
  | some largest => largest + 1

/-- A footprint element. New kinds of touch (index, schema, attach, function)
are added as constructors; statements quantify over `Footprint.allows`. -/
inductive Touch where
  | db (db : DbId) (mode : Mode)
  | table (table : TableId) (mode : Mode)
  deriving DecidableEq, Repr

/-- A decidable set of permitted touches. -/
structure Footprint where
  allows : Touch → Bool

namespace Footprint

def top : Footprint := ⟨fun _ => true⟩

def ofList (touches : List Touch) : Footprint := ⟨fun touch => touches.contains touch⟩

def union (left right : Footprint) : Footprint :=
  ⟨fun touch => left.allows touch || right.allows touch⟩

def Le (small large : Footprint) : Prop :=
  ∀ touch, small.allows touch = true → large.allows touch = true

/-- Drop every write touch. SQLite checks `PRAGMA query_only` at the same
touch point, `OP_Transaction` with nonzero P2 (`src/vdbe.c` at the pinned
commit); that is a correspondence of placement, not a theorem about SQLite. -/
def readOnly (footprint : Footprint) : Footprint :=
  ⟨fun touch => match touch with
    | .db _ .write | .table _ .write => false
    | touch => footprint.allows touch⟩

def Configured (footprint : Footprint) (db : DbId) : Prop :=
  ∃ mode, footprint.allows (.db db mode) = true

def Writes (footprint : Footprint) (table : TableId) : Prop :=
  footprint.allows (.table table .write) = true

end Footprint

inductive Event where
  /-- A granted transaction or cursor open. -/
  | touch (touch : Touch)
  /-- An attempted, uncommitted change of the working copy of a table. -/
  | write (table : TableId)
  /-- Autocommit publication of the working store. -/
  | commit
  | row (cells : List Value)
  deriving DecidableEq

def Event.Allowed (footprint : Footprint) : Event → Prop
  | .touch granted => footprint.allows granted = true
  | .write table => footprint.Writes table
  | .commit | .row _ => True

/-- Register contents: a scalar or a record built by `MakeRecord`. Records are
abstract value lists; their serialization is not modeled. -/
inductive Cell where
  | value (value : Value)
  | record (fields : Row)
  deriving DecidableEq

structure Cursor where
  table : TableId
  mode : Mode
  /-- Current rowid; `none` means unpositioned or past the end. -/
  position : Option Int := none
  deriving DecidableEq, Repr

/-- Whether an open transaction mode admits a cursor of `mode`. -/
def Mode.covers : Option Mode → Mode → Bool
  | some .write, _ => true
  | some .read, .read => true
  | _, _ => false

/-- `Transaction` never downgrades: a write transaction stays a write transaction. -/
def Mode.upgrade : Option Mode → Mode → Mode
  | some .write, _ => .write
  | _, mode => mode

structure Config where
  pc : Nat := 0
  registers : Nat → Cell := fun _ => .value .null
  cursors : Nat → Option Cursor := fun _ => none
  transactions : DbId → Option Mode := fun _ => none
  working : Store
  committed : Store
  rows : List Row := []
  halted : Option Nat := none

def Config.initial (store : Store) : Config := {working := store, committed := store}

namespace Config

def advance (c : Config) : Config := {c with pc := c.pc + 1}
def jump (c : Config) (target : Nat) : Config := {c with pc := target}

def write (c : Config) (register : Nat) (cell : Cell) : Config :=
  {c with registers := fun index => if index = register then cell else c.registers index}

def writeNull (c : Config) (first last : Nat) : Config :=
  {c with registers := fun index =>
    if first ≤ index ∧ index ≤ max first last then .value .null else c.registers index}

def copyRegisters : Nat → Nat → Nat → Config → Config
  | 0, _, _, c => c
  | count + 1, source, destination, c =>
      copyRegisters count (source + 1) (destination + 1) (c.write destination (c.registers source))

def setCursor (c : Config) (identifier : Nat) (cursor : Cursor) : Config :=
  {c with cursors := fun index => if index = identifier then some cursor else c.cursors index}

/-- The scalar contents of `count` registers from `first`, or `none` if one
holds a record. -/
def scalars (c : Config) (first count : Nat) : Option Row :=
  (List.range count).mapM fun offset =>
    match c.registers (first + offset) with
    | .value value => some value
    | .record _ => none

end Config

/-- Modeled instructions. Scalar and read opcodes come from the core decoder. -/
inductive Instr where
  | init (target : Nat)
  | goto (target : Nat)
  | halt (code : Nat)
  | integer (value : Int64) (destination : Nat)
  | string8 (value : String) (destination : Nat)
  | null (first last : Nat)
  | copy (source destination additional : Nat)
  | transaction (slot : Nat) (mode : Mode)
  | openRead (cursor root slot : Nat)
  | openWrite (cursor root slot : Nat)
  | rewind (cursor emptyTarget : Nat)
  | next (cursor loopTarget : Nat)
  | seekRowid (cursor missingTarget keyRegister : Nat)
  | column (cursor column destination : Nat)
  | rowid (cursor destination : Nat)
  | newRowid (cursor destination : Nat)
  | makeRecord (first count destination : Nat)
  | insert (cursor record key : Nat)
  | delete (cursor : Nat)
  | resultRow (first count : Nat)
  deriving DecidableEq, Repr

def Instr.ofCore : Vdbe.Instruction → Instr
  | .init target => .init target
  | .goto target => .goto target
  | .halt code => .halt code
  | .integer value destination => .integer value.toInt64 destination
  | .int64 value destination => .integer value destination
  | .string8 value destination => .string8 value destination
  | .null first last => .null first last
  | .copy source destination additional => .copy source destination additional
  | .openRead cursor root database => .openRead cursor root database
  | .rewind cursor target => .rewind cursor target
  | .next cursor target => .next cursor target
  | .column cursor index destination => .column cursor index destination
  | .rowid cursor destination => .rowid cursor destination
  | .resultRow first count => .resultRow first count
  | .seekRowid cursor target key => .seekRowid cursor target key

/-- Decode the write-path opcodes, and everything else through `Vdbe.decode?`.
Accepted forms:
* Transaction: P1 slot, P2 `0` read or `1`/`2` write. The schema cookie in
  P3–P5 is not checked, so the model never reports `SQLITE_SCHEMA`.
* OpenWrite: P1 cursor, positive immediate root P2, P3 slot, P4 none or a
  nonnegative column count, P5 zero (no `OPFLAG_P2ISREG`).
* NewRowid: P1 cursor, positive P2, P3 zero (no AUTOINCREMENT register).
* MakeRecord: positive P1 and P3, P2 count, no P4 affinity string.
* Insert: P1 cursor, positive record and key registers, P4 none or the table
  name, P5 only `OPFLAG_NCHANGE` and `OPFLAG_LASTROWID` (counters only).
* Delete: P1 cursor, P2 zero or `OPFLAG_NCHANGE`, P3 zero, P4 none or the table
  name, P5 zero.
Other operand forms are unmodeled. -/
def decode? (raw : RawInstruction) : Option Instr :=
  match raw.opcode.name? with
  | some "Transaction" =>
      match raw.p4 with
      | .none | .integer _ =>
          if raw.p2 = 0 then (Vdbe.operand? raw.p1).map (.transaction · .read)
          else if raw.p2 = 1 ∨ raw.p2 = 2 then (Vdbe.operand? raw.p1).map (.transaction · .write)
          else none
      | _ => none
  | some "OpenWrite" =>
      let countOk : Bool := match raw.p4 with
        | .none => true
        | .integer count => decide (0 ≤ count)
        | _ => false
      if raw.p5 = 0 ∧ countOk then do
        return .openWrite (← Vdbe.operand? raw.p1) (← Vdbe.register? raw.p2) (← Vdbe.operand? raw.p3)
      else none
  | some "NewRowid" =>
      if raw.p3 = 0 ∧ raw.p4 = Vdbe.P4.none ∧ raw.p5 = 0 then do
        return .newRowid (← Vdbe.operand? raw.p1) (← Vdbe.register? raw.p2)
      else none
  | some "MakeRecord" =>
      if raw.p4 = Vdbe.P4.none ∧ raw.p5 = 0 then do
        return .makeRecord (← Vdbe.register? raw.p1) (← Vdbe.operand? raw.p2) (← Vdbe.register? raw.p3)
      else none
  | some "Insert" =>
      let nameOk : Bool := match raw.p4 with
        | .none | .text _ => true
        | _ => false
      if nameOk ∧ (raw.p5 = 0 ∨ raw.p5 = 1 ∨ raw.p5 = 32 ∨ raw.p5 = 33) then do
        return .insert (← Vdbe.operand? raw.p1) (← Vdbe.register? raw.p2) (← Vdbe.register? raw.p3)
      else none
  | some "Delete" =>
      let nameOk : Bool := match raw.p4 with
        | .none | .text _ => true
        | _ => false
      if nameOk ∧ (raw.p2 = 0 ∨ raw.p2 = 1) ∧ raw.p3 = 0 ∧ raw.p5 = 0 then
        (Vdbe.operand? raw.p1).map .delete
      else none
  | _ => (Vdbe.decode? raw).map Instr.ofCore

inductive Fault where
  | programCounter (pc : Nat)
  | alreadyHalted
  | noDatabase (slot : Nat)
  | noTable (slot root : Nat)
  | missingTable (table : TableId)
  | denied (touch : Touch)
  | noTransaction (db : DbId) (mode : Mode)
  | missingCursor (cursor : Nat)
  | readOnlyCursor (cursor : Nat)
  | noCurrentRow (cursor : Nat)
  | notInteger (register : Nat)
  | notRecord (register : Nat)
  | recordValue (register : Nat)
  | rowidRange (key : Int)
  | unmodeled (raw : RawInstruction)
  deriving DecidableEq

/-- Open a cursor. Resolution, the policy guard, the transaction check and the
existence check happen in that order; only success changes the state. -/
def openCursor (footprint : Footprint) (cat : Catalog) (c : Config)
    (identifier root slot : Nat) (mode : Mode) : Except Fault (List Event × Config) :=
  match cat.resolve slot root with
  | none => .error (.noTable slot root)
  | some table =>
      if footprint.allows (.table table mode) = false then .error (.denied (.table table mode))
      else if Mode.covers (c.transactions table.db) mode = false then
        .error (.noTransaction table.db mode)
      else match c.working table with
        | none => .error (.missingTable table)
        | some _ => .ok ([.touch (.table table mode)],
            (c.setCursor identifier ⟨table, mode, none⟩).advance)

/-- The positioned row of a cursor, read from the working store. -/
def currentRow (c : Config) (identifier : Nat) : Except Fault (Cursor × Int × Row) :=
  match c.cursors identifier with
  | none => .error (.missingCursor identifier)
  | some cursor => match cursor.position with
    | none => .error (.noCurrentRow identifier)
    | some key => match (c.working cursor.table).bind (Rows.lookup key) with
      | none => .error (.noCurrentRow identifier)
      | some row => .ok (cursor, key, row)

/-- A write-mode cursor and the working rows of its table. -/
def writeCursor (c : Config) (identifier : Nat) : Except Fault (Cursor × Rows) :=
  match c.cursors identifier with
  | none => .error (.missingCursor identifier)
  | some cursor =>
      if cursor.mode = .read then .error (.readOnlyCursor identifier)
      else match c.working cursor.table with
        | none => .error (.missingTable cursor.table)
        | some rows => .ok (cursor, rows)

def inInt64 (key : Int) : Bool := decide (-(2^63 : Int) ≤ key ∧ key < 2^63)

/-- One modeled instruction. -/
def exec (footprint : Footprint) (cat : Catalog) (instr : Instr) (c : Config) :
    Except Fault (List Event × Config) :=
  match instr with
  | .init target => .ok ([], c.jump (if target = 0 then c.pc + 1 else target))
  | .goto target => .ok ([], c.jump target)
  | .halt code =>
      if code = 0 then .ok ([.commit], {c with halted := some 0, committed := c.working})
      else .ok ([], {c with halted := some code})
  | .integer value destination => .ok ([], (c.write destination (.value (.integer value))).advance)
  | .string8 value destination => .ok ([], (c.write destination (.value (.text value))).advance)
  | .null first last => .ok ([], (c.writeNull first last).advance)
  | .copy source destination additional =>
      .ok ([], (Config.copyRegisters (additional + 1) source destination c).advance)
  | .transaction slot mode =>
      match cat.slot slot with
      | none => .error (.noDatabase slot)
      | some db =>
          if footprint.allows (.db db mode) = false then .error (.denied (.db db mode))
          else .ok ([.touch (.db db mode)],
            {c with transactions := fun other =>
              if other = db then some (Mode.upgrade (c.transactions db) mode)
              else c.transactions other}.advance)
  | .openRead identifier root slot => openCursor footprint cat c identifier root slot .read
  | .openWrite identifier root slot => openCursor footprint cat c identifier root slot .write
  | .rewind identifier target =>
      match c.cursors identifier with
      | none => .error (.missingCursor identifier)
      | some cursor => match c.working cursor.table with
        | none => .error (.missingTable cursor.table)
        | some rows => match rows.head? with
          | none => .ok ([], (c.setCursor identifier {cursor with position := none}).jump target)
          | some entry =>
              .ok ([], (c.setCursor identifier {cursor with position := some entry.1}).advance)
  | .next identifier target =>
      match c.cursors identifier with
      | none => .error (.missingCursor identifier)
      | some cursor => match cursor.position with
        | none => .error (.noCurrentRow identifier)
        | some key => match c.working cursor.table with
          | none => .error (.missingTable cursor.table)
          | some rows => match rows.after key with
            | none => .ok ([], (c.setCursor identifier {cursor with position := none}).advance)
            | some later =>
                .ok ([], (c.setCursor identifier {cursor with position := some later}).jump target)
  | .seekRowid identifier target register =>
      match c.cursors identifier with
      | none => .error (.missingCursor identifier)
      | some cursor => match c.registers register with
        | .value (.integer key) => match c.working cursor.table with
          | none => .error (.missingTable cursor.table)
          | some rows => match rows.lookup key.toInt with
            | none => .ok ([], (c.setCursor identifier {cursor with position := none}).jump target)
            | some _ =>
                .ok ([], (c.setCursor identifier {cursor with position := some key.toInt}).advance)
        | _ => .error (.notInteger register)
  | .column identifier index destination =>
      match currentRow c identifier with
      | .error fault => .error fault
      | .ok (_, _, row) => .ok ([], (c.write destination (.value (row[index]?.getD .null))).advance)
  | .rowid identifier destination =>
      match currentRow c identifier with
      | .error fault => .error fault
      | .ok (_, key, _) =>
          if inInt64 key then .ok ([], (c.write destination (.value (.integer (Int64.ofInt key)))).advance)
          else .error (.rowidRange key)
  | .newRowid identifier destination =>
      match writeCursor c identifier with
      | .error fault => .error fault
      | .ok (_, rows) =>
          if inInt64 rows.nextRowid then
            .ok ([], (c.write destination (.value (.integer (Int64.ofInt rows.nextRowid)))).advance)
          else .error (.rowidRange rows.nextRowid)
  | .makeRecord first count destination =>
      match c.scalars first count with
      | none => .error (.recordValue first)
      | some fields => .ok ([], (c.write destination (.record fields)).advance)
  | .insert identifier record key =>
      match writeCursor c identifier with
      | .error fault => .error fault
      | .ok (cursor, rows) => match c.registers key, c.registers record with
        | .value (.integer rowid), .record fields =>
            .ok ([.write cursor.table],
              {c with working := c.working.set cursor.table (rows.upsert rowid.toInt fields)}.advance)
        | .value (.integer _), _ => .error (.notRecord record)
        | _, _ => .error (.notInteger key)
  | .delete identifier =>
      match writeCursor c identifier with
      | .error fault => .error fault
      | .ok (cursor, rows) => match cursor.position with
        | none => .error (.noCurrentRow identifier)
        | some key => match rows.lookup key with
          | none => .error (.noCurrentRow identifier)
          | some _ => .ok ([.write cursor.table],
              {c with working := c.working.set cursor.table (rows.erase key)}.advance)
  | .resultRow first count =>
      match c.scalars first count with
      | none => .error (.recordValue first)
      | some cells => .ok ([.row cells], {c with rows := c.rows ++ [cells]}.advance)

/-- Transitions of raw instructions that do not decode. -/
abbrev Fallback := RawInstruction → Config → List Event → Config → Prop

/-- The fallback that has no transitions; the executable `run` uses it. -/
def Fallback.none : Fallback := fun _ _ _ _ => False

/-- Per-transition contract shared by modeled steps and fallback steps:
permitted events, preserved provenance (`Inv`, below), working-store changes
only on logged tables, and committed-store changes only by publishing the
working store together with a `commit` event. -/
structure Contract (footprint : Footprint) (c : Config) (events : List Event) (c' : Config) :
    Prop where
  allowed : ∀ event ∈ events, event.Allowed footprint
  working : ∀ table, Event.write table ∉ events → c'.working table = c.working table
  committed : c'.committed = c.committed ∨ (Event.commit ∈ events ∧ c'.committed = c'.working)

/-- Provenance invariant: every open database was granted by the footprint, and
every cursor was opened by a granted touch under a covering transaction. -/
structure Inv (footprint : Footprint) (c : Config) : Prop where
  transactions : ∀ db mode, c.transactions db = some mode → footprint.allows (.db db mode) = true
  cursors : ∀ identifier cursor, c.cursors identifier = some cursor →
    footprint.allows (.table cursor.table cursor.mode) = true ∧
      Mode.covers (c.transactions cursor.table.db) cursor.mode = true

/-- The only obligation on unmodeled behavior. A fallback may halt, fault,
skip, or change registers, cursors and stores, provided each transition meets
`Contract` and preserves `Inv`. -/
def FallbackSafe (footprint : Footprint) (fallback : Fallback) : Prop :=
  ∀ raw c events c', Inv footprint c → fallback raw c events c' →
    Contract footprint c events c' ∧ Inv footprint c'

inductive Step (footprint : Footprint) (cat : Catalog) (fallback : Fallback) (code : RawProgram) :
    Config → List Event → Config → Prop where
  | modeled {c raw instr events c'} (active : c.halted = none)
      (fetch : code[c.pc]? = some raw) (decoded : decode? raw = some instr)
      (exec : exec footprint cat instr c = .ok (events, c')) :
      Step footprint cat fallback code c events c'
  | fallback {c raw events c'} (active : c.halted = none)
      (fetch : code[c.pc]? = some raw) (unmodeled : decode? raw = none)
      (step : fallback raw c events c') :
      Step footprint cat fallback code c events c'

/-- Finite execution prefixes. -/
inductive Trace (footprint : Footprint) (cat : Catalog) (fallback : Fallback) (code : RawProgram) :
    Config → List Event → Config → Prop where
  | nil (c) : Trace footprint cat fallback code c [] c
  | cons {c₁ c₂ c₃ events₁ events₂} :
      Step footprint cat fallback code c₁ events₁ c₂ →
      Trace footprint cat fallback code c₂ events₂ c₃ →
      Trace footprint cat fallback code c₁ (events₁ ++ events₂) c₃

def step (footprint : Footprint) (cat : Catalog) (code : RawProgram) (c : Config) :
    Except Fault (List Event × Config) :=
  if c.halted.isSome then .error .alreadyHalted else
    match code[c.pc]? with
    | none => .error (.programCounter c.pc)
    | some raw => match decode? raw with
      | none => .error (.unmodeled raw)
      | some instr => exec footprint cat instr c

inductive Result where
  | halted
  | exhausted
  | fault (reason : Fault)
  deriving DecidableEq

structure Outcome where
  events : List Event
  config : Config
  result : Result

/-- Run at most `fuel` steps. A fault leaves the state of the faulting step. -/
def run (footprint : Footprint) (cat : Catalog) (code : RawProgram) : Nat → Config → Outcome
  | fuel, c =>
      if c.halted.isSome then ⟨[], c, .halted⟩ else
        match fuel with
        | 0 => ⟨[], c, .exhausted⟩
        | fuel + 1 =>
          match step footprint cat code c with
          | .error fault => ⟨[], c, .fault fault⟩
          | .ok (events, after) =>
            match run footprint cat code fuel after with
            | ⟨rest, final, result⟩ => ⟨events ++ rest, final, result⟩

/-- Tables outside `changed` are equal in both stores. -/
def Frame (changed : TableId → Prop) (before after : Store) : Prop :=
  ∀ table, ¬ changed table → after table = before table

/-! ### Bytecode footprint -/

/-- The touch a modeled instruction requests, resolved through the catalog.
Only the three guarded opcodes request touches. -/
def Instr.touch? (cat : Catalog) : Instr → Option Touch
  | .transaction slot mode => (cat.slot slot).map (Touch.db · mode)
  | .openRead _ root slot => (cat.resolve slot root).map (Touch.table · .read)
  | .openWrite _ root slot => (cat.resolve slot root).map (Touch.table · .write)
  | _ => none

/-- Every touch a program can request, read off the code. -/
def staticTouches (cat : Catalog) (code : RawProgram) : List Touch :=
  code.toList.filterMap fun raw => (decode? raw).bind (Instr.touch? cat)

/-- A raw instruction is modeled and any touch it requests is permitted. -/
def rawWithin (footprint : Footprint) (cat : Catalog) (raw : RawInstruction) : Bool :=
  match decode? raw with
  | none => false
  | some instr => (instr.touch? cat).all footprint.allows

/-- The syntactic bytecode restriction: every instruction is modeled and every
touch it requests is in the footprint. This looks only at the code. -/
def within (footprint : Footprint) (cat : Catalog) (code : RawProgram) : Bool :=
  code.toList.all (rawWithin footprint cat)

/-- The semantic bytecode restriction: unguarded execution prefixes from a
fresh configuration emit only permitted events, for every store and every
fallback, including fallbacks that violate `FallbackSafe`. -/
def TargetRestricted (footprint : Footprint) (cat : Catalog) (code : RawProgram) : Prop :=
  ∀ (fallback : Fallback) (store : Store) (events : List Event) (c' : Config),
    Trace Footprint.top cat fallback code (Config.initial store) events c' →
      ∀ event ∈ events, event.Allowed footprint

/-! ### Autocommit composition -/

/-- Run statements one after another, each as its own autocommit program
starting from the previous committed store. -/
def runScript (footprint : Footprint) (cat : Catalog) (fuel : Nat) :
    List RawProgram → Store → List Event × Store
  | [], store => ([], store)
  | code :: rest, store =>
      match run footprint cat code fuel (Config.initial store) with
      | ⟨events, final, _⟩ =>
        match runScript footprint cat fuel rest final.committed with
        | (later, last) => (events ++ later, last)

end Silmaril.Machine.SQLite.VirtualMachine.Writable

module

/-! Source-derived connection security gates of SQLite 3.54.1.

Line references `sqlite3.c:N` are to the tracked amalgamation
`corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c`
(SHA-256 `0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52`).
The source map is `docs/projects/sqlite-connection-security.md`.

The model has the connection flag bits read by the gates below, the client
operations that write them, and one Boolean decision for each gate:

* SQL-function usability (`sqlite3ExprFunctionUsable`, prepare phase);
* virtual-table read and write usability by risk level (prepare phase);
* extension loading through the C API and through the SQL function (step phase);
* the open flags and slot check of `ATTACH` (step phase);
* the write-transaction refusal of `OP_Transaction` (step phase).

`run` decides a finite sequence of client operations and requests, in order.
Each decision uses the flags current at its position in the sequence.

Not covered (proof obligations): the C or ELF code, the parser and code
generator that produce the requests, the authorizer, automatic reprepare
after statement expiry, URI parsing, b-tree read-only refusal, raw SQL or
database bytes, callback bodies, and every other flag. Passing a gate is not
a commit: the attempted effect may still fail. -/

@[expose] public section

namespace Silmaril.Machine.SQLite.ConnectionSecurity

/-- When a gate is decided. `prepare` covers `sqlite3_prepare*`, including
reprepare inside `sqlite3_step`. `step` covers execution of the compiled
program and the bodies of SQL functions it calls. -/
inductive Phase where
  | prepare
  | step
  deriving DecidableEq, Repr

/-- Compile-time options of a build that the gates below depend on. -/
structure Build where
  /-- `SQLITE_OMIT_LOAD_EXTENSION` is not defined. Without it there is no
  `sqlite3_load_extension` and no `load_extension()` SQL function. -/
  loadExtension : Bool
  /-- `SQLITE_TRUSTED_SCHEMA` is undefined or nonzero (sqlite3.c:191850). -/
  trustedSchemaDefault : Bool
  /-- `SQLITE_ENABLE_LOAD_EXTENSION` is defined (sqlite3.c:191887). -/
  loadExtensionDefault : Bool
  /-- `SQLITE_DEFAULT_DEFENSIVE` is defined (sqlite3.c:191908). -/
  defensiveDefault : Bool
  deriving DecidableEq, Repr

/-- The pinned native default configuration: only `-DSQLITE_THREADSAFE=1`
(`corpus/sqlite/build.sh`, `default`). -/
def Build.pinnedDefault : Build where
  loadExtension := true
  trustedSchemaDefault := true
  loadExtensionDefault := false
  defensiveDefault := false

/-- The pinned `small` variant, which defines `SQLITE_OMIT_LOAD_EXTENSION`. -/
def Build.pinnedSmall : Build := { Build.pinnedDefault with loadExtension := false }

/-- The `sqlite3.flags` bits read by the modeled gates. -/
structure Flags where
  /-- `SQLITE_TrustedSchema`. -/
  trustedSchema : Bool
  /-- `SQLITE_Defensive`. No modeled gate reads it. It is kept so that the
  client operations can write it. -/
  defensive : Bool
  /-- `SQLITE_QueryOnly`. -/
  queryOnly : Bool
  /-- `SQLITE_CorruptRdOnly`, set after `SQLITE_CORRUPT` in a transaction. -/
  corruptReadOnly : Bool
  /-- `SQLITE_LoadExtension`: the C-API bit. -/
  loadExtensionApi : Bool
  /-- `SQLITE_LoadExtFunc`: the SQL-function bit. -/
  loadExtensionSql : Bool
  /-- `SQLITE_AttachWrite`. -/
  attachWrite : Bool
  /-- `SQLITE_AttachCreate`. -/
  attachCreate : Bool
  deriving DecidableEq, Repr

/-- Flags of a freshly opened connection (`openDatabase`, sqlite3.c:191843-191915). -/
def Flags.atOpen (build : Build) : Flags where
  trustedSchema := build.trustedSchemaDefault
  defensive := build.defensiveDefault
  queryOnly := false
  corruptReadOnly := false
  loadExtensionApi := build.loadExtensionDefault
  loadExtensionSql := false
  attachWrite := true
  attachCreate := true

/-- Boolean `sqlite3_db_config` options with a modeled bit (table at
sqlite3.c:189354-189377). -/
inductive DbConfigOption where
  | enableLoadExtension
  | trustedSchema
  | defensive
  | enableAttachWrite
  | enableAttachCreate
  deriving DecidableEq, Repr

/-- Flag-type PRAGMAs with a modeled bit (sqlite3.c:145163, 145282). -/
inductive FlagPragma where
  | trustedSchema
  | queryOnly
  deriving DecidableEq, Repr

/-- Client operations that write modeled flags. -/
inductive ClientOp where
  /-- `sqlite3_db_config(db, op, onoff, pRes)`: positive sets, zero clears,
  negative leaves the bit unchanged (sqlite3.c:189380-189392). -/
  | dbConfig (option : DbConfigOption) (onoff : Int)
  /-- `sqlite3_enable_load_extension(db, onoff)` (sqlite3.c:144463-144475). -/
  | enableLoadExtension (on : Bool)
  /-- Preparing `PRAGMA name=value`. The bit is written while the PRAGMA is
  compiled (`PragTyp_FLAG`, sqlite3.c:146474-146513), not when it is stepped. -/
  | pragma (name : FlagPragma) (on : Bool)
  /-- A transaction that hit `SQLITE_CORRUPT` (sqlite3.c:105784). -/
  | markCorrupt
  deriving DecidableEq, Repr

/-- The phase in which each client operation takes effect. -/
def ClientOp.phase : ClientOp → Phase
  | .pragma .. => .prepare
  | _ => .step

/-- Write one bit as `sqlite3_db_config` does. -/
def setBit (onoff : Int) (old : Bool) : Bool :=
  if 0 < onoff then true else if onoff = 0 then false else old

/-- Apply `sqlite3_db_config` to the modeled bits. `ENABLE_LOAD_EXTENSION`
writes only `SQLITE_LoadExtension` (sqlite3.c:189359). -/
def DbConfigOption.apply (option : DbConfigOption) (onoff : Int) (flags : Flags) : Flags :=
  match option with
  | .enableLoadExtension => { flags with loadExtensionApi := setBit onoff flags.loadExtensionApi }
  | .trustedSchema => { flags with trustedSchema := setBit onoff flags.trustedSchema }
  | .defensive => { flags with defensive := setBit onoff flags.defensive }
  | .enableAttachWrite => { flags with attachWrite := setBit onoff flags.attachWrite }
  | .enableAttachCreate => { flags with attachCreate := setBit onoff flags.attachCreate }

def ClientOp.apply : ClientOp → Flags → Flags
  | .dbConfig option onoff, flags => option.apply onoff flags
  | .enableLoadExtension on, flags =>
      { flags with loadExtensionApi := on, loadExtensionSql := on }
  | .pragma .trustedSchema on, flags => { flags with trustedSchema := on }
  | .pragma .queryOnly on, flags => { flags with queryOnly := on }
  | .markCorrupt, flags => { flags with corruptReadOnly := true }

/-- Where an expression or table reference being compiled came from. -/
inductive Origin where
  /-- Top-level SQL of the statement being prepared. -/
  | direct
  /-- A TEMP trigger or view body. `sqlite3FixInit` sets `bTemp` for
  `iDb == 1` (sqlite3.c:126412), so no `EP_FromDDL` mark is made. -/
  | tempSchema
  /-- A non-TEMP schema object: trigger, view, index, CHECK, DEFAULT or
  generated column (sqlite3.c:112852, 115451, 126335, 126373). -/
  | persistentSchema
  deriving DecidableEq, Repr

/-- The compilation site of one request. -/
structure Site where
  origin : Origin
  /-- The statement was prepared with `SQLITE_PREPARE_FROM_DDL` (sqlite3.c:4856). -/
  prepareFromDdl : Bool := false
  /-- The code is generated for a trigger body (`pParse->pToplevel != 0`). -/
  inTrigger : Bool := false
  deriving DecidableEq, Repr

/-- `EP_FromDDL`, or `SQLITE_PREPARE_FROM_DDL` on the whole statement
(sqlite3.c:114168-114169, 155728). -/
def Site.fromDdl (site : Site) : Bool :=
  site.origin == .persistentSchema || site.prepareFromDdl

/-- Internal function-definition bits: `SQLITE_FUNC_DIRECT` (the same bit as
`SQLITE_DIRECTONLY`) and `SQLITE_FUNC_UNSAFE` (sqlite3.c:19250-19252). -/
structure FunctionFlags where
  direct : Bool
  unsafeBit : Bool
  deriving DecidableEq, Repr

/-- `sqlite3_create_function*` flags. `SQLITE_INNOCUOUS` is the same bit as
`SQLITE_FUNC_UNSAFE` with the opposite meaning: `sqlite3CreateFunc` inverts it
(sqlite3.c:190346-190355). -/
def FunctionFlags.ofCreate (directOnly innocuous : Bool) : FunctionFlags :=
  ⟨directOnly, !innocuous⟩

/-- Built-in `FUNCTION()` entries carry neither bit (sqlite3.c:19334). -/
def FunctionFlags.builtin : FunctionFlags := ⟨false, false⟩

/-- Built-in `SFUNCTION()` entries such as `load_extension` carry both
(sqlite3.c:19341-19342, 137655). -/
def FunctionFlags.sideEffectBuiltin : FunctionFlags := ⟨true, true⟩

/-- Prepare-phase function check. `sqlite3ExprFunctionUsable` is reached only
for functions with `DIRECT` or `UNSAFE` (sqlite3.c:111763, 118376). It rejects
a schema-originated call to a DIRECTONLY function, or to an UNSAFE function
while `trusted_schema` is off (sqlite3.c:114161-114185). -/
def functionUsable (flags : Flags) (site : Site) (fn : FunctionFlags) : Bool :=
  if fn.direct || fn.unsafeBit then
    !(site.fromDdl && (fn.direct || !flags.trustedSchema))
  else true

/-- `VTable.eVtabRisk` (sqlite3.c:19619-19623). -/
inductive VtabRisk where
  | low
  | normal
  | high
  deriving DecidableEq, Repr

def VtabRisk.level : VtabRisk → Nat
  | .low => 0
  | .normal => 1
  | .high => 2

/-- Risk options of `sqlite3_vtab_config` made by `xConnect`. -/
inductive VtabOption where
  | innocuous
  | directOnly
  deriving DecidableEq, Repr

/-- Each connect starts at `normal` (sqlite3.c:163206), and the last option
wins (sqlite3.c:163974-163980). -/
def VtabRisk.configure (options : List VtabOption) : VtabRisk :=
  options.foldl (fun _ option => match option with
    | .innocuous => .low
    | .directOnly => .high) .normal

/-- The largest permitted risk: `normal` with `trusted_schema` on, `low` with
it off. -/
def allowedRisk (flags : Flags) : Nat := if flags.trustedSchema then 1 else 0

/-- Prepare-phase read check on a virtual table in a `FROM` clause
(sqlite3.c:155727-155733). -/
def vtabReadUsable (flags : Flags) (site : Site) (risk : VtabRisk) : Bool :=
  !(site.fromDdl && decide (allowedRisk flags < risk.level))

/-- Prepare-phase write check on a virtual table with `xUpdate`
(`vtabIsReadOnly`, sqlite3.c:133303-133322). It keys on any trigger, TEMP
triggers included, rather than on `EP_FromDDL`. -/
def vtabWriteUsable (flags : Flags) (site : Site) (risk : VtabRisk) : Bool :=
  !((site.inTrigger || site.prepareFromDdl) && decide (allowedRisk flags < risk.level))

inductive ExtensionApi where
  /-- `sqlite3_load_extension`. -/
  | c
  /-- The `load_extension()` SQL function. -/
  | sql
  deriving DecidableEq, Repr

/-- Step-phase load gate. The C API tests `SQLITE_LoadExtension`
(sqlite3.c:144300). The SQL function first tests `SQLITE_LoadExtFunc`
(sqlite3.c:136111), then calls the C API, so it needs both bits. -/
def loadExtensionPermitted (build : Build) (flags : Flags) : ExtensionApi → Bool
  | .c => build.loadExtension && flags.loadExtensionApi
  | .sql => build.loadExtension && flags.loadExtensionSql && flags.loadExtensionApi

/-- Access bits of `sqlite3_open_v2`-style flags. -/
structure OpenFlags where
  readOnly : Bool
  readWrite : Bool
  create : Bool
  deriving DecidableEq, Repr

/-- Open flags passed to `sqlite3BtreeOpen` by `ATTACH`, given the flags
produced by `sqlite3ParseUri` (sqlite3.c:126064-126069). -/
def attachOpenFlags (flags : Flags) (parsed : OpenFlags) : OpenFlags :=
  if !flags.attachWrite then ⟨true, false, false⟩
  else if !flags.attachCreate then { parsed with create := false }
  else parsed

/-- `ATTACH` slot check: `nDb` counts `main` and `temp` (sqlite3.c:126023). -/
def attachSlotAvailable (databases limit : Nat) : Bool := decide (databases < limit + 2)

/-- Modeled requests. -/
inductive Request where
  | callFunction (site : Site) (fn : FunctionFlags)
  | readVtab (site : Site) (risk : VtabRisk)
  | writeVtab (site : Site) (risk : VtabRisk)
  | loadExtension (api : ExtensionApi)
  /-- `parsed` is the `sqlite3ParseUri` result, `databases` is `db->nDb`, and
  `limit` is `SQLITE_LIMIT_ATTACHED`. -/
  | attach (parsed : OpenFlags) (databases limit : Nat)
  /-- `OP_Transaction` with nonzero P2, on any database including `temp`. -/
  | beginWrite
  deriving DecidableEq, Repr

def Request.phase : Request → Phase
  | .callFunction .. | .readVtab .. | .writeVtab .. => .prepare
  | .loadExtension _ | .attach .. | .beginWrite => .step

/-- The attempted effect that follows a passing gate. -/
inductive Effect where
  /-- The function is compiled into the program, so `OP_Function` may call
  its callback. -/
  | functionCallback (site : Site) (fn : FunctionFlags)
  | vtabRead (site : Site) (risk : VtabRisk)
  | vtabWrite (site : Site) (risk : VtabRisk)
  /-- Execution reaches the body of `sqlite3LoadExtension` past its gate. -/
  | extensionLoad (api : ExtensionApi)
  /-- `sqlite3BtreeOpen` is attempted with these flags. -/
  | attachOpen (flags : OpenFlags)
  /-- `sqlite3BtreeBeginTrans` is attempted with a nonzero write flag. -/
  | writeTransaction
  deriving DecidableEq, Repr

inductive Event where
  | client (op : ClientOp)
  /-- The gate refused the request: a prepare error or a step error. -/
  | refused (phase : Phase) (request : Request)
  /-- The gate passed. The effect is attempted, not committed. -/
  | attempted (phase : Phase) (effect : Effect)
  deriving DecidableEq, Repr

/-- Decide one request with the current flags. -/
def decideRequest (build : Build) (flags : Flags) : Request → Option Effect
  | .callFunction site fn =>
      if functionUsable flags site fn then some (.functionCallback site fn) else none
  | .readVtab site risk =>
      if vtabReadUsable flags site risk then some (.vtabRead site risk) else none
  | .writeVtab site risk =>
      if vtabWriteUsable flags site risk then some (.vtabWrite site risk) else none
  | .loadExtension api =>
      if loadExtensionPermitted build flags api then some (.extensionLoad api) else none
  | .attach parsed databases limit =>
      if attachSlotAvailable databases limit then
        some (.attachOpen (attachOpenFlags flags parsed))
      else none
  | .beginWrite =>
      -- sqlite3.c:100544-100552
      if flags.queryOnly || flags.corruptReadOnly then none else some .writeTransaction

def Request.event (build : Build) (flags : Flags) (request : Request) : Event :=
  match decideRequest build flags request with
  | some effect => .attempted request.phase effect
  | none => .refused request.phase request

inductive Item where
  | client (op : ClientOp)
  | request (request : Request)
  deriving DecidableEq, Repr

/-- Flags after a client sequence. -/
def Item.apply : Item → Flags → Flags
  | .client op, flags => op.apply flags
  | .request _, flags => flags

def after (flags : Flags) (items : List Item) : Flags :=
  items.foldl (fun flags item => item.apply flags) flags

/-- Decide a finite client sequence in order. -/
def run (build : Build) : Flags → List Item → List Event
  | _, [] => []
  | flags, .client op :: rest => .client op :: run build (op.apply flags) rest
  | flags, .request request :: rest => request.event build flags :: run build flags rest

/-- The disabled profile. Extension loading is off, `query_only` is on,
`ATTACH` cannot write, and `trusted_schema` is off. The SQL-function load bit
is not constrained, because that path also needs the C-API bit. -/
structure Disabled (flags : Flags) : Prop where
  untrusted : flags.trustedSchema = false
  noLoadApi : flags.loadExtensionApi = false
  queryOnly : flags.queryOnly = true
  noAttachWrite : flags.attachWrite = false

/-- Attempted effects that the disabled profile is intended to exclude. -/
def Effect.Forbidden : Effect → Prop
  | .functionCallback site fn => site.fromDdl = true ∧ (fn.direct = true ∨ fn.unsafeBit = true)
  | .vtabRead site risk => site.fromDdl = true ∧ risk ≠ .low
  | .vtabWrite site risk => (site.inTrigger = true ∨ site.prepareFromDdl = true) ∧ risk ≠ .low
  | .extensionLoad _ => True
  | .attachOpen access => access.readWrite = true ∨ access.create = true
  | .writeTransaction => True

/-- A client operation that keeps every disabled flag set disabled. -/
def ClientOp.KeepsDisabled (op : ClientOp) : Prop :=
  ∀ flags, Disabled flags → Disabled (op.apply flags)

def Item.KeepsDisabled : Item → Prop
  | .client op => op.KeepsDisabled
  | .request _ => True

end Silmaril.Machine.SQLite.ConnectionSecurity

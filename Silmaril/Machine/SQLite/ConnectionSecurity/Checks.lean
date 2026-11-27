module

import Silmaril.Machine.SQLite.ConnectionSecurity.Thms

/-! Kernel checks for the SQLite connection security gates: the pinned
open-time flags, phase labels, how the order of client operations changes the
extension-loading and function decisions, non-vacuity and necessity of the
disabled profile, which client operations keep it, and axiom guards.
Everything here is model-only. -/

namespace Silmaril.Machine.SQLite.ConnectionSecurity.Checks

open Silmaril.Machine.SQLite.ConnectionSecurity

/-! ### Pinned open-time flags

These agree with `sqlite3_db_config(db, op, -1, &v)` read on a fresh
connection of the pinned x86-64 `libsqlite3.so` (see the source map). -/

example : Flags.atOpen .pinnedDefault =
    { trustedSchema := true, defensive := false, queryOnly := false,
      corruptReadOnly := false, loadExtensionApi := false, loadExtensionSql := false,
      attachWrite := true, attachCreate := true } := rfl

example : ∀ api, loadExtensionPermitted .pinnedDefault (Flags.atOpen .pinnedDefault) api = false := by
  intro api; cases api <;> rfl

/-! ### Phases -/

example (site : Site) (fn : FunctionFlags) : (Request.callFunction site fn).phase = .prepare := rfl
example (site : Site) (risk : VtabRisk) : (Request.readVtab site risk).phase = .prepare := rfl
example (api : ExtensionApi) : (Request.loadExtension api).phase = .step := rfl
example (parsed : OpenFlags) (n limit : Nat) : (Request.attach parsed n limit).phase = .step := rfl
example : Request.beginWrite.phase = .step := rfl
example (name : FlagPragma) (on : Bool) : (ClientOp.pragma name on).phase = .prepare := rfl
example (option : DbConfigOption) (onoff : Int) : (ClientOp.dbConfig option onoff).phase = .step := rfl

/-! ### C API versus SQL function authority -/

private def libraryOpen : Flags := Flags.atOpen .pinnedDefault

/-- `SQLITE_DBCONFIG_ENABLE_LOAD_EXTENSION=1` enables only the C API. -/
example :
    run .pinnedDefault libraryOpen
      [.client (.dbConfig .enableLoadExtension 1),
       .request (.loadExtension .c), .request (.loadExtension .sql)] =
    [.client (.dbConfig .enableLoadExtension 1),
     .attempted .step (.extensionLoad .c),
     .refused .step (.loadExtension .sql)] := rfl

/-- `sqlite3_enable_load_extension(db, 1)` enables both. The decision uses the
flags current at the step, so a refusal earlier in the sequence does not
carry forward. -/
example :
    run .pinnedDefault libraryOpen
      [.request (.loadExtension .sql), .client (.enableLoadExtension true),
       .request (.loadExtension .sql)] =
    [.refused .step (.loadExtension .sql), .client (.enableLoadExtension true),
     .attempted .step (.extensionLoad .sql)] := rfl

/-- Clearing only the C-API bit after enabling both also stops the SQL path. -/
example :
    run .pinnedDefault libraryOpen
      [.client (.enableLoadExtension true), .client (.dbConfig .enableLoadExtension 0),
       .request (.loadExtension .sql)] =
    [.client (.enableLoadExtension true), .client (.dbConfig .enableLoadExtension 0),
     .refused .step (.loadExtension .sql)] := rfl

/-- The `small` variant omits both paths, even after enabling. -/
example :
    run .pinnedSmall (Flags.atOpen .pinnedSmall)
      [.client (.enableLoadExtension true), .request (.loadExtension .c)] =
    [.client (.enableLoadExtension true), .refused .step (.loadExtension .c)] := rfl

/-! ### trusted_schema is origin-scoped -/

private def appFunction : FunctionFlags := FunctionFlags.ofCreate false false
private def directSite : Site := ⟨.direct, false, false⟩
private def schemaSite : Site := ⟨.persistentSchema, false, true⟩

/-- With `trusted_schema` off, a non-INNOCUOUS application function passes in
direct SQL and is refused at a persistent-schema site. -/
example :
    run .pinnedDefault libraryOpen
      [.client (.pragma .trustedSchema false),
       .request (.callFunction directSite appFunction),
       .request (.callFunction schemaSite appFunction)] =
    [.client (.pragma .trustedSchema false),
     .attempted .prepare (.functionCallback directSite appFunction),
     .refused .prepare (.callFunction schemaSite appFunction)] := rfl

/-- `SQLITE_PREPARE_FROM_DDL` makes direct SQL schema-originated. -/
example : functionUsable { libraryOpen with trustedSchema := false }
    ⟨.direct, true, false⟩ appFunction = false := rfl

/-- DIRECTONLY is refused at a persistent-schema site even with
`trusted_schema` on, and passes in direct SQL. -/
example : functionUsable libraryOpen schemaSite FunctionFlags.sideEffectBuiltin = false := rfl
example : functionUsable libraryOpen directSite FunctionFlags.sideEffectBuiltin = true := rfl

/-- Built-in `FUNCTION()` entries pass everywhere. -/
example : functionUsable { libraryOpen with trustedSchema := false } schemaSite
    FunctionFlags.builtin = true := rfl

/-- Virtual-table risk: last option wins, starting at `normal`. -/
example : VtabRisk.configure [] = .normal := rfl
example : VtabRisk.configure [.directOnly, .innocuous] = .low := rfl
example : VtabRisk.configure [.innocuous, .directOnly] = .high := rfl
example : vtabReadUsable libraryOpen schemaSite .normal = true := rfl
example : vtabReadUsable libraryOpen schemaSite .high = false := rfl
example : vtabReadUsable { libraryOpen with trustedSchema := false } schemaSite .normal = false := rfl

/-! ### ATTACH -/

private def rwc : OpenFlags := ⟨false, true, true⟩

example : attachOpenFlags libraryOpen rwc = rwc := rfl
example : attachOpenFlags { libraryOpen with attachCreate := false } rwc = ⟨false, true, false⟩ := rfl
example : attachOpenFlags { libraryOpen with attachWrite := false } rwc = ⟨true, false, false⟩ := rfl
/-- `main` and `temp` plus ten attached databases fill the default limit. -/
example : attachSlotAvailable 12 10 = false := rfl
example : attachSlotAvailable 2 0 = false := rfl

/-! ### The disabled profile: reachable, non-vacuous and necessary -/

private def disabledFlags : Flags :=
  after libraryOpen
    [.client (.dbConfig .trustedSchema 0), .client (.pragma .queryOnly true),
     .client (.dbConfig .enableAttachWrite 0)]

private theorem disabledFlags_disabled : Disabled disabledFlags := ⟨rfl, rfl, rfl, rfl⟩

/-- Under the profile, direct calls and read-only ATTACH are still attempted.
Writes and schema-originated unsafe calls are refused. -/
example :
    run .pinnedDefault disabledFlags
      [.request (.callFunction directSite appFunction),
       .request (.attach rwc 2 10),
       .request .beginWrite,
       .request (.callFunction schemaSite appFunction),
       .request (.loadExtension .sql)] =
    [.attempted .prepare (.functionCallback directSite appFunction),
     .attempted .step (.attachOpen ⟨true, false, false⟩),
     .refused .step .beginWrite,
     .refused .prepare (.callFunction schemaSite appFunction),
     .refused .step (.loadExtension .sql)] := rfl

/-- Without `query_only`, a write transaction is attempted, and it is a
forbidden effect. -/
example : decideRequest .pinnedDefault { disabledFlags with queryOnly := false } .beginWrite =
    some .writeTransaction := rfl
example : Effect.writeTransaction.Forbidden := trivial

/-- Without the ATTACH-write restriction, a creating ATTACH is attempted. -/
example : decideRequest .pinnedDefault { disabledFlags with attachWrite := true } (.attach rwc 2 10) =
    some (.attachOpen rwc) := rfl

/-! ### Which client operations keep the profile -/

example (option : DbConfigOption) : (ClientOp.dbConfig option (-1)).KeepsDisabled := by
  intro flags hd
  cases option <;> exact ⟨hd.untrusted, hd.noLoadApi, hd.queryOnly, hd.noAttachWrite⟩

example (onoff : Int) : (ClientOp.dbConfig .defensive onoff).KeepsDisabled :=
  fun _ hd => ⟨hd.untrusted, hd.noLoadApi, hd.queryOnly, hd.noAttachWrite⟩

example : (ClientOp.enableLoadExtension false).KeepsDisabled :=
  fun _ hd => ⟨hd.untrusted, rfl, hd.queryOnly, hd.noAttachWrite⟩

example : ClientOp.markCorrupt.KeepsDisabled :=
  fun _ hd => ⟨hd.untrusted, hd.noLoadApi, hd.queryOnly, hd.noAttachWrite⟩

/-- A later PRAGMA prepared on the same connection can reverse the profile.
Making it durable needs an authorizer or API-level state, neither of which is
modeled here. -/
example : ¬ (ClientOp.pragma .trustedSchema true).KeepsDisabled :=
  fun h => nomatch (h disabledFlags disabledFlags_disabled).untrusted
example : ¬ (ClientOp.pragma .queryOnly false).KeepsDisabled :=
  fun h => nomatch (h disabledFlags disabledFlags_disabled).queryOnly
example : ¬ (ClientOp.dbConfig .enableLoadExtension 1).KeepsDisabled :=
  fun h => nomatch (h disabledFlags disabledFlags_disabled).noLoadApi
example : ¬ (ClientOp.enableLoadExtension true).KeepsDisabled :=
  fun h => nomatch (h disabledFlags disabledFlags_disabled).noLoadApi

/-! ### Axiom guards -/

/--
info: 'Silmaril.Machine.SQLite.ConnectionSecurity.run_disabled' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms run_disabled

/--
info: 'Silmaril.Machine.SQLite.ConnectionSecurity.functionUsable_eq_false_iff' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms functionUsable_eq_false_iff

/--
info: 'Silmaril.Machine.SQLite.ConnectionSecurity.untrusted_direct_call_usable' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms untrusted_direct_call_usable

/--
info: 'Silmaril.Machine.SQLite.ConnectionSecurity.loadExtensionPermitted_dbConfig_zero' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms loadExtensionPermitted_dbConfig_zero

/--
info: 'Silmaril.Machine.SQLite.ConnectionSecurity.attachOpenFlags_of_attachWrite_false' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms attachOpenFlags_of_attachWrite_false

/--
info: 'Silmaril.Machine.SQLite.ConnectionSecurity.run_append' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms run_append

/--
info: 'Silmaril.Machine.SQLite.ConnectionSecurity.run_take_disabled' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms run_take_disabled

end Silmaril.Machine.SQLite.ConnectionSecurity.Checks

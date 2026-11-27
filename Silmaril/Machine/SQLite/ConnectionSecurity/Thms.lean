module

public import Silmaril.Machine.SQLite.ConnectionSecurity.Defs
import Silmaril.Proofs.Machine.SQLite.ConnectionSecurity

/-! Theorems about the source-derived SQLite connection security gates.

These are statements about the model in `Defs`, which transcribes cited
source branches. They are not proofs about `libsqlite3`. The parser and code
generator that produce requests, the authorizer, reprepare, raw SQL and
database bytes, callback bodies, and native code remain obligations. -/

public section

namespace Silmaril.Machine.SQLite.ConnectionSecurity

/-! ### Functions: origin, DIRECTONLY and INNOCUOUS -/

/-- Exactly when the prepare-phase function check rejects a call:
schema-originated, and either DIRECTONLY, or UNSAFE (not INNOCUOUS) while
`trusted_schema` is off. -/
theorem functionUsable_eq_false_iff (flags : Flags) (site : Site) (fn : FunctionFlags) :
    functionUsable flags site fn = false ↔
      site.fromDdl = true ∧
        (fn.direct = true ∨ (fn.unsafeBit = true ∧ flags.trustedSchema = false)) :=
  Proofs.Machine.SQLite.ConnectionSecurity.functionUsable_eq_false_iff flags site fn

/-- `trusted_schema=OFF` is not a ban on direct calls. Outside
schema-originated sites the function check passes for every flag setting,
including DIRECTONLY and non-INNOCUOUS functions. -/
theorem functionUsable_of_not_fromDdl {flags : Flags} {site : Site} (fn : FunctionFlags)
    (h : site.fromDdl = false) : functionUsable flags site fn = true :=
  Proofs.Machine.SQLite.ConnectionSecurity.functionUsable_of_not_fromDdl fn h

/-- The model-only instance: with `trusted_schema` off, a direct top-level call
to a function registered without `SQLITE_INNOCUOUS` passes the gate. -/
theorem untrusted_direct_call_usable (flags : Flags) (inTrigger : Bool) :
    functionUsable { flags with trustedSchema := false }
      ⟨.direct, false, inTrigger⟩ (FunctionFlags.ofCreate false false) = true :=
  functionUsable_of_not_fromDdl _ rfl

/-- DIRECTONLY is rejected at every schema-originated site, whatever
`trusted_schema` is. -/
theorem functionUsable_directOnly_fromDdl (flags : Flags) {site : Site} (innocuous : Bool)
    (h : site.fromDdl = true) :
    functionUsable flags site (FunctionFlags.ofCreate true innocuous) = false :=
  (functionUsable_eq_false_iff _ _ _).2 ⟨h, .inl rfl⟩

/-- An INNOCUOUS function without DIRECTONLY passes at every site. -/
theorem functionUsable_innocuous (flags : Flags) (site : Site) :
    functionUsable flags site (FunctionFlags.ofCreate false true) = true := rfl

/-- TEMP schema objects are not schema-originated for this check. -/
theorem tempSchema_not_fromDdl (inTrigger : Bool) :
    (Site.mk .tempSchema false inTrigger).fromDdl = false := rfl

/-! ### Virtual tables -/

/-- Reads outside schema-originated sites pass at every risk level. -/
theorem vtabReadUsable_of_not_fromDdl {flags : Flags} {site : Site} (risk : VtabRisk)
    (h : site.fromDdl = false) : vtabReadUsable flags site risk = true :=
  Proofs.Machine.SQLite.ConnectionSecurity.vtabReadUsable_of_not_fromDdl risk h

/-- `SQLITE_VTAB_INNOCUOUS` tables pass both checks at every site. -/
theorem vtab_low_usable (flags : Flags) (site : Site) :
    vtabReadUsable flags site .low = true ∧ vtabWriteUsable flags site .low = true := by
  simp [vtabReadUsable, vtabWriteUsable, VtabRisk.level]

/-- The write check applies inside a TEMP trigger, unlike the read check. -/
theorem vtab_write_temp_trigger (flags : Flags) :
    vtabWriteUsable { flags with trustedSchema := false } ⟨.tempSchema, false, true⟩ .normal
      = false ∧
    vtabReadUsable { flags with trustedSchema := false } ⟨.tempSchema, false, true⟩ .normal
      = true := ⟨rfl, rfl⟩

/-! ### Extension loading: C API versus SQL function -/

/-- The SQL path needs the C-API bit as well as its own bit. -/
theorem loadExtension_sql_needs_c {build : Build} {flags : Flags}
    (h : loadExtensionPermitted build flags .sql = true) :
    loadExtensionPermitted build flags .c = true := by
  simp_all [loadExtensionPermitted]

/-- `SQLITE_DBCONFIG_ENABLE_LOAD_EXTENSION` never writes the SQL-function bit. -/
theorem dbConfig_loadExtension_keeps_sql (onoff : Int) (flags : Flags) :
    ((ClientOp.dbConfig .enableLoadExtension onoff).apply flags).loadExtensionSql =
      flags.loadExtensionSql := rfl

/-- Setting it to `0` disables both paths: the SQL bit may stay set, but the
SQL path also needs the cleared C-API bit. -/
theorem loadExtensionPermitted_dbConfig_zero (build : Build) (flags : Flags)
    (api : ExtensionApi) :
    loadExtensionPermitted build
      ((ClientOp.dbConfig .enableLoadExtension 0).apply flags) api = false :=
  Proofs.Machine.SQLite.ConnectionSecurity.loadExtensionPermitted_dbConfig_zero build flags api

/-- `sqlite3_enable_load_extension(db, 1)` enables both paths in a build that
has them. -/
theorem enableLoadExtension_both (build : Build) (flags : Flags) (api : ExtensionApi)
    (h : build.loadExtension = true) :
    loadExtensionPermitted build ((ClientOp.enableLoadExtension true).apply flags) api = true := by
  cases api <;> simp [loadExtensionPermitted, ClientOp.apply, h]

/-- With `SQLITE_OMIT_LOAD_EXTENSION` neither path exists. -/
theorem loadExtension_omitted (flags : Flags) (api : ExtensionApi) :
    loadExtensionPermitted Build.pinnedSmall flags api = false := by
  cases api <;> rfl

/-! ### ATTACH -/

/-- With `SQLITE_DBCONFIG_ENABLE_ATTACH_WRITE` off, `ATTACH` opens read-only
and cannot create, whatever the URI requested. -/
theorem attachOpenFlags_of_attachWrite_false {flags : Flags} (parsed : OpenFlags)
    (h : flags.attachWrite = false) : attachOpenFlags flags parsed = ⟨true, false, false⟩ :=
  Proofs.Machine.SQLite.ConnectionSecurity.attachOpenFlags_of_attachWrite_false parsed h

/-- With `SQLITE_DBCONFIG_ENABLE_ATTACH_CREATE` off, `ATTACH` cannot create. -/
theorem attachOpenFlags_create_of_attachCreate_false {flags : Flags} (parsed : OpenFlags)
    (h : flags.attachCreate = false) : (attachOpenFlags flags parsed).create = false :=
  Proofs.Machine.SQLite.ConnectionSecurity.attachOpenFlags_create_of_attachCreate_false parsed h

/-! ### Client sequences and the disabled profile -/

/-- Decisions compose along a client sequence. Every prefix of a run is the
run of the corresponding prefix. -/
theorem run_append (build : Build) (flags : Flags) (xs ys : List Item) :
    run build flags (xs ++ ys) = run build flags xs ++ run build (after flags xs) ys :=
  Proofs.Machine.SQLite.ConnectionSecurity.run_append build flags xs ys

/-- One decision under the disabled profile never attempts a forbidden effect. -/
theorem decideRequest_not_forbidden {build : Build} {flags : Flags} (hd : Disabled flags)
    {request : Request} {effect : Effect}
    (hr : decideRequest build flags request = some effect) : ¬ effect.Forbidden :=
  Proofs.Machine.SQLite.ConnectionSecurity.decideRequest_not_forbidden hd hr

/-- Disabled-profile exclusion for modeled effects. Take any finite sequence
of requests, with no validity or admission premise, interleaved with client
operations that keep the profile. Such a run attempts no forbidden effect:
no schema-originated DIRECTONLY or non-INNOCUOUS function, no
schema-originated non-INNOCUOUS virtual table, no extension load through
either API, no writable or creating `ATTACH`, and no write transaction. -/
theorem run_disabled {build : Build} {flags : Flags} (hd : Disabled flags) {items : List Item}
    (hkeep : ∀ item ∈ items, item.KeepsDisabled) {phase : Phase} {effect : Effect}
    (hmem : Event.attempted phase effect ∈ run build flags items) : ¬ effect.Forbidden :=
  Proofs.Machine.SQLite.ConnectionSecurity.run_disabled hd hkeep hmem

/-- The same exclusion for every finite prefix. -/
theorem run_take_disabled {build : Build} {flags : Flags} (hd : Disabled flags)
    {items : List Item} (hkeep : ∀ item ∈ items, item.KeepsDisabled) (n : Nat)
    {phase : Phase} {effect : Effect}
    (hmem : Event.attempted phase effect ∈ run build flags (items.take n)) :
    ¬ effect.Forbidden :=
  run_disabled hd (fun item hi => hkeep item (List.mem_of_mem_take hi)) hmem

end Silmaril.Machine.SQLite.ConnectionSecurity

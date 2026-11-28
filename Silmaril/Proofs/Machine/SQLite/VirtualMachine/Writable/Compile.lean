module

public import Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.Defs
public import Silmaril.Machine.SQLite.VirtualMachine.Writable.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.VirtualMachine.Writable.Compile

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine.Writable
open Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile

variable {F : Footprint} {cat : Catalog}

private theorem operand_nat (n : Nat) : Vdbe.operand? (n : Int) = some n := by
  simp [Vdbe.operand?]

private theorem register_nat {n : Nat} (h : 0 < n) : Vdbe.register? (n : Int) = some n := by
  simp [Vdbe.register?]; omega

private theorem within_toArray (l : List RawInstruction) :
    within F cat l.toArray = l.all (rawWithin F cat) := by
  simp [within]

private theorem rawWithin_init (t : Nat) : rawWithin F cat (Code.init t) = true := by
  simp [rawWithin, Code.init, Code.named, decode?, Vdbe.decode?, Vdbe.RawOpcode.name?,
    operand_nat, Instr.ofCore, Instr.touch?]

private theorem rawWithin_goto (t : Nat) : rawWithin F cat (Code.goto t) = true := by
  simp [rawWithin, Code.goto, Code.named, decode?, Vdbe.decode?, Vdbe.RawOpcode.name?,
    operand_nat, Instr.ofCore, Instr.touch?]

private theorem rawWithin_halt : rawWithin F cat Code.halt = true := rfl

private theorem rawWithin_rewind (c t : Nat) : rawWithin F cat (Code.rewind c t) = true := by
  simp [rawWithin, Code.rewind, Code.named, decode?, Vdbe.decode?, Vdbe.RawOpcode.name?,
    operand_nat, Instr.ofCore, Instr.touch?]

private theorem rawWithin_next (c t : Nat) : rawWithin F cat (Code.next c t) = true := by
  simp [rawWithin, Code.next, Code.named, decode?, Vdbe.decode?, Vdbe.RawOpcode.name?,
    operand_nat, Instr.ofCore, Instr.touch?]

private theorem rawWithin_column (c i d : Nat) (hd : 0 < d) :
    rawWithin F cat (Code.column c i d) = true := by
  simp [rawWithin, Code.column, Code.named, decode?, Vdbe.decode?, Vdbe.RawOpcode.name?,
    operand_nat, register_nat, Instr.ofCore, Instr.touch?, hd]

private theorem rawWithin_resultRow (f n : Nat) (hf : 0 < f) :
    rawWithin F cat (Code.resultRow f n) = true := by
  simp [rawWithin, Code.resultRow, Code.named, decode?, Vdbe.decode?, Vdbe.RawOpcode.name?,
    operand_nat, register_nat, Instr.ofCore, Instr.touch?, hf]

private theorem rawWithin_newRowid (c d : Nat) (hd : 0 < d) :
    rawWithin F cat (Code.newRowid c d) = true := by
  simp [rawWithin, Code.newRowid, Code.named, decode?, Vdbe.RawOpcode.name?, operand_nat, register_nat, Instr.touch?, hd]

private theorem rawWithin_makeRecord (f n d : Nat) (hf : 0 < f) (hd : 0 < d) :
    rawWithin F cat (Code.makeRecord f n d) = true := by
  simp [rawWithin, Code.makeRecord, Code.named, decode?, Vdbe.RawOpcode.name?, operand_nat, register_nat, Instr.touch?,
    hf, hd]

private theorem rawWithin_insert (c r k : Nat) (hr : 0 < r) (hk : 0 < k) :
    rawWithin F cat (Code.insert c r k) = true := by
  simp [rawWithin, Code.insert, Code.named, decode?, Vdbe.RawOpcode.name?, operand_nat, register_nat, Instr.touch?,
    hr, hk]

private theorem rawWithin_delete (c : Nat) : rawWithin F cat (Code.delete c) = true := by
  simp [rawWithin, Code.delete, Code.named, decode?, Vdbe.RawOpcode.name?, operand_nat, Instr.touch?]

private theorem rawWithin_seekRowid (c t k : Nat) (hk : 0 < k) :
    rawWithin F cat (Code.seekRowid c t k) = true := by
  simp [rawWithin, Code.seekRowid, Code.named, decode?, Vdbe.decode?, Vdbe.RawOpcode.name?,
    operand_nat, register_nat, Instr.ofCore, Instr.touch?, hk]

private theorem rawWithin_int64 (v : Int64) (d : Nat) (hd : 0 < d) :
    rawWithin F cat (Code.int64 v d) = true := by
  have h1 : ¬ v.toInt < -9223372036854775808 := by have := Int64.le_toInt v; omega
  have h2 : ¬ 9223372036854775808 ≤ v.toInt := by have := Int64.toInt_lt v; omega
  simp [rawWithin, Code.int64, Code.named, decode?, Vdbe.decode?, Vdbe.RawOpcode.name?,
    register_nat, Instr.ofCore, Instr.touch?, hd, h1, h2]

private theorem rawWithin_load (d : Nat) (hd : 0 < d) (value : Literal)
    (nulFree : ∀ text, value = .text text → text.contains '\x00' = false) :
    rawWithin F cat (Code.load d value) = true := by
  cases value with
  | integer v => exact rawWithin_int64 v d hd
  | text text =>
      have := nulFree text rfl
      simp [rawWithin, Code.load, Code.named, decode?, Vdbe.decode?, Vdbe.RawOpcode.name?,
        register_nat, Instr.ofCore, Instr.touch?, hd, this]
  | null =>
      simp [rawWithin, Code.load, Code.named, decode?, Vdbe.decode?, Vdbe.RawOpcode.name?,
        operand_nat, register_nat, Instr.ofCore, Instr.touch?, hd]

private theorem rawWithin_transaction {slot : Nat} {db : DbId} {mode : Mode}
    (hslot : cat.slot slot = some db) (hF : F.allows (.db db mode) = true) :
    rawWithin F cat (Code.transaction slot mode) = true := by
  cases mode <;>
    simp [rawWithin, Code.transaction, Code.named, decode?, Vdbe.RawOpcode.name?, operand_nat, Instr.touch?, hslot, hF]

private theorem rawWithin_openRead {location : Location} {table : TableId} (c : Nat)
    (h : Locates cat location table) (hF : F.allows (.table table .read) = true) :
    rawWithin F cat (Code.openRead c location) = true := by
  simp [rawWithin, Code.openRead, Code.named, decode?, Vdbe.decode?, Vdbe.RawOpcode.name?,
    operand_nat, register_nat h.1, Instr.ofCore, Instr.touch?, h.2, hF]

private theorem rawWithin_openWrite {location : Location} {table : TableId} (c : Nat)
    (h : Locates cat location table) (hF : F.allows (.table table .write) = true) :
    rawWithin F cat (Code.openWrite c location) = true := by
  simp [rawWithin, Code.openWrite, Code.named, decode?, Vdbe.RawOpcode.name?, operand_nat, register_nat h.1,
    Instr.touch?, h.2, hF]

private theorem ofList_allows {touches : List Touch} {touch : Touch} (h : touch ∈ touches) :
    (Footprint.ofList touches).allows touch = true := by
  simp [Footprint.ofList, h]

private theorem resolve_slot {slot root : Nat} {table : TableId}
    (h : cat.resolve slot root = some table) : cat.slot slot = some table.db := by
  unfold Catalog.resolve at h
  cases hs : cat.slot slot with
  | none => simp [hs] at h
  | some db =>
      cases hr : cat.root db root with
      | none => simp [hs, hr] at h
      | some key =>
          simp [hs, hr] at h
          subst h
          rfl

private theorem columns_within (c w first : Nat) (hf : 0 < first) :
    (Code.columns c w first).all (rawWithin F cat) = true := by
  simp only [Code.columns, List.all_map, List.all_eq_true]
  intro j _
  exact rawWithin_column _ _ _ (by omega)

private theorem loads_within :
    ∀ (first : Nat) (values : List Literal), 0 < first →
      (∀ text, Literal.text text ∈ values → text.contains '\x00' = false) →
      (Code.loads first values).all (rawWithin F cat) = true
  | _, [], _, _ => rfl
  | first, value :: rest, hf, nulFree => by
      simp only [Code.loads, List.all_cons, Bool.and_eq_true]
      refine ⟨rawWithin_load first hf value fun text h => nulFree text (h ▸ List.mem_cons_self), ?_⟩
      exact loads_within (first + 1) rest (by omega)
        fun text h => nulFree text (List.mem_cons_of_mem _ h)

/-- Each compiled program satisfies the bytecode restriction of its own source
footprint. The source footprint is computed from the statement only. -/
theorem compiles_within {stmt : Stmt} {code : RawProgram} (h : Compiles cat stmt code) :
    within (Footprint.ofList stmt.footprint) cat code = true := by
  cases h with
  | @scan table location width locates =>
      have hopen := rawWithin_openRead (F := Footprint.ofList (Stmt.scan table width).footprint)
        0 locates (ofList_allows (by simp [Stmt.footprint, readTouches]))
      have htx := rawWithin_transaction (F := Footprint.ofList (Stmt.scan table width).footprint)
        (mode := .read) (resolve_slot locates.2) (ofList_allows (by simp [Stmt.footprint, readTouches]))
      simp [Code.scan, within_toArray, hopen, htx, rawWithin_init, rawWithin_rewind,
        rawWithin_next, rawWithin_halt, rawWithin_goto, columns_within, rawWithin_resultRow]
  | @insert table location values locates nulFree =>
      have hopen := rawWithin_openWrite (F := Footprint.ofList (Stmt.insert table values).footprint)
        0 locates (ofList_allows (by simp [Stmt.footprint, writeTouches]))
      have htx := rawWithin_transaction (F := Footprint.ofList (Stmt.insert table values).footprint)
        (mode := .write) (resolve_slot locates.2) (ofList_allows (by simp [Stmt.footprint, writeTouches]))
      simp [Code.insertValues, within_toArray, hopen, htx, rawWithin_init, rawWithin_halt,
        rawWithin_goto, rawWithin_newRowid, rawWithin_makeRecord, rawWithin_insert,
        loads_within 2 values (by omega) nulFree]
  | @deleteRowid table location key locates =>
      have hopen := rawWithin_openWrite (F := Footprint.ofList (Stmt.deleteRowid table key).footprint)
        0 locates (ofList_allows (by simp [Stmt.footprint, writeTouches]))
      have htx := rawWithin_transaction (F := Footprint.ofList (Stmt.deleteRowid table key).footprint)
        (mode := .write) (resolve_slot locates.2) (ofList_allows (by simp [Stmt.footprint, writeTouches]))
      simp [Code.deleteRowid, within, hopen, htx, rawWithin_init, rawWithin_halt, rawWithin_goto,
        rawWithin_int64, rawWithin_seekRowid, rawWithin_delete]
  | @copy source target sourceAt targetAt width hs ht =>
      have hread := rawWithin_openRead (F := Footprint.ofList (Stmt.copy source target width).footprint)
        0 hs (ofList_allows (by simp [Stmt.footprint, readTouches]))
      have hwrite := rawWithin_openWrite (F := Footprint.ofList (Stmt.copy source target width).footprint)
        1 ht (ofList_allows (by simp [Stmt.footprint, writeTouches]))
      have htxr := rawWithin_transaction (F := Footprint.ofList (Stmt.copy source target width).footprint)
        (mode := .read) (resolve_slot hs.2) (ofList_allows (by simp [Stmt.footprint, readTouches]))
      have htxw := rawWithin_transaction (F := Footprint.ofList (Stmt.copy source target width).footprint)
        (mode := .write) (resolve_slot ht.2) (ofList_allows (by simp [Stmt.footprint, writeTouches]))
      simp [Code.copy, within_toArray, hread, hwrite, htxr, htxw, rawWithin_init, rawWithin_rewind,
        rawWithin_next, rawWithin_halt, rawWithin_goto, columns_within, rawWithin_newRowid,
        rawWithin_makeRecord 2 width (2 + width) (by omega) (by omega),
        rawWithin_insert 1 (2 + width) 1 (by omega) (by omega)]

theorem compiles_within_of {G : Footprint} {stmt : Stmt} {code : RawProgram}
    (h : Compiles cat stmt code) (hG : ∀ touch ∈ stmt.footprint, G.allows touch = true) :
    within G cat code = true :=
  within_mono (fun touch htouch => hG touch (by simpa [Footprint.ofList] using htouch))
    (compiles_within h)

/-- A program in the target restriction that no statement compiles to. -/
theorem not_compiles_halt (stmt : Stmt) : ¬ Compiles cat stmt #[Code.halt] := by
  intro h
  generalize hcode : #[Code.halt] = code at h
  have size := congrArg Array.size hcode
  cases h <;> simp [Code.scan, Code.insertValues, Code.deleteRowid, Code.copy] at size

theorem within_halt (G : Footprint) : within G cat #[Code.halt] = true := rfl

theorem target_iff (stmt : Stmt) (table : TableId) :
    Touch.table table .write ∈ stmt.footprint ↔ stmt.target? = some table := by
  cases stmt <;> simp [Stmt.footprint, Stmt.target?, readTouches, writeTouches, eq_comm]

theorem scriptFootprint_writes {stmts : List Stmt} {table : TableId} :
    (scriptFootprint stmts).Writes table ↔ ∃ stmt ∈ stmts, stmt.target? = some table := by
  simp [scriptFootprint, Footprint.Writes, Footprint.ofList, List.mem_flatMap, target_iff]

private theorem forall₂_mem {stmts : List Stmt} {codes : List RawProgram}
    (h : CompilesScript cat stmts codes) :
    ∀ code ∈ codes, ∃ stmt ∈ stmts, Compiles cat stmt code := by
  induction h with
  | nil => intro _ h; cases h
  | cons hc _ ih =>
      intro code hmem
      rcases List.mem_cons.mp hmem with rfl | h
      · exact ⟨_, List.mem_cons_self, hc⟩
      · obtain ⟨stmt, hs, hcs⟩ := ih code h
        exact ⟨stmt, List.mem_cons_of_mem _ hs, hcs⟩

theorem compiled_script_within {stmts : List Stmt} {codes : List RawProgram}
    (h : CompilesScript cat stmts codes) :
    ∀ code ∈ codes, within (scriptFootprint stmts) cat code = true := by
  intro code hmem
  obtain ⟨stmt, hs, hc⟩ := forall₂_mem h code hmem
  refine compiles_within_of hc fun touch htouch => ?_
  simp only [scriptFootprint, Footprint.ofList, List.contains_iff_mem, List.mem_flatMap]
  exact ⟨stmt, hs, htouch⟩

theorem compiled_script {stmts : List Stmt} {codes : List RawProgram}
    (h : CompilesScript cat stmts codes) (fuel : Nat) (store : Store) :
    runScript (scriptFootprint stmts) cat fuel codes store =
        runScript Footprint.top cat fuel codes store ∧
      (∀ event ∈ (runScript Footprint.top cat fuel codes store).1,
        event.Allowed (scriptFootprint stmts)) ∧
      Frame (fun table => ∃ stmt ∈ stmts, stmt.target? = some table)
        store (runScript Footprint.top cat fuel codes store).2 := by
  have heq := runScript_eq_top (fuel := fuel) (compiled_script_within h) store
  have allowed := (runScript_safe (scriptFootprint stmts) cat fuel codes store).1
  have frame := runScript_frame (scriptFootprint stmts) cat fuel codes store
  rw [heq] at allowed frame
  exact ⟨heq, allowed, fun table ht => frame table fun hw => ht (scriptFootprint_writes.mp hw)⟩

theorem provenance_targetRestricted {G : Footprint} {code : RawProgram}
    (h : CompilationProvenance G cat code) : TargetRestricted G cat code :=
  let ⟨_, hG, hc⟩ := h
  targetRestricted_of_within (compiles_within_of hc hG)

theorem callback_trace_safe {F : Footprint} {callbacks : Fallback}
    (h : CallbackProvenance F callbacks) {code : RawProgram} {store : Store} {c' : Config}
    {events : List Event} (htrace : Trace F cat callbacks code (Config.initial store) events c') :
    (∀ event ∈ events, event.Allowed F) ∧ Frame F.Writes store c'.committed :=
  ⟨(trace_safe h htrace).2.1, (trace_frame h htrace).2⟩

theorem transitive_script {causes : Stmt → List Stmt} {stmt : Stmt} {subs : List Stmt}
    {codes : List RawProgram} (htouch : TransitiveTouch causes stmt)
    (hreach : ∀ sub ∈ subs, Reaches causes stmt sub) (hcomp : CompilesScript cat (stmt :: subs) codes)
    (fuel : Nat) (store : Store) :
    runScript (Footprint.ofList stmt.footprint) cat fuel codes store =
        runScript Footprint.top cat fuel codes store ∧
      Frame (fun table => stmt.target? = some table) store
        (runScript Footprint.top cat fuel codes store).2 := by
  have hwithin : ∀ code ∈ codes, within (Footprint.ofList stmt.footprint) cat code = true := by
    intro code hmem
    obtain ⟨s, hs, hc⟩ := forall₂_mem hcomp code hmem
    refine compiles_within_of hc fun touch ht => ?_
    simp only [Footprint.ofList, List.contains_iff_mem]
    rcases List.mem_cons.mp hs with rfl | hsub
    · exact ht
    · exact htouch s (hreach s hsub) touch ht
  have heq := runScript_eq_top (fuel := fuel) hwithin store
  have frame := runScript_frame (Footprint.ofList stmt.footprint) cat fuel codes store
  rw [heq] at frame
  refine ⟨heq, fun table ht => frame table fun hw => ht ?_⟩
  have : Touch.table table .write ∈ stmt.footprint := by
    simpa [Footprint.Writes, Footprint.ofList] using hw
  exact (target_iff stmt table).mp this

end Silmaril.Proofs.Machine.SQLite.VirtualMachine.Writable.Compile

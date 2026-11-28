module

import Silmaril.Machine.SQLite.VirtualMachine.Writable.Thms

/-! Concrete runs of the writable VDBE fragment: committed and uncommitted
writes, deletes, reads that see earlier writes, refusals at the guard, an
aliased slot, unmodeled opcodes, and the same programs without the guard. -/

namespace Silmaril.Machine.SQLite.VirtualMachine.Writable.Checks

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine.Writable

private def mainDb : DbId := ⟨0⟩
private def otherDb : DbId := ⟨7⟩
private def users : TableId := ⟨mainDb, ⟨1⟩⟩
private def audit : TableId := ⟨mainDb, ⟨2⟩⟩
private def secrets : TableId := ⟨otherDb, ⟨1⟩⟩

/-- `main` at slot 0; one attached database reachable at slots 2 and 3. -/
private def cat : Catalog where
  slot slot := if slot = 0 then some mainDb else if slot = 2 ∨ slot = 3 then some otherDb else none
  root db root :=
    if db = mainDb ∧ root = 2 then some ⟨1⟩
    else if db = mainDb ∧ root = 3 then some ⟨2⟩
    else if db = otherDb ∧ root = 2 then some ⟨1⟩
    else none

private def store : Store := fun table =>
  if table = users then some [(1, [.text "alice"]), (2, [.text "bob"])]
  else if table = audit then some []
  else if table = secrets then some [(1, [.text "key"])]
  else none

/-- Configured: `main` only; read `users`, write `audit`. -/
private def policy : Footprint := Footprint.ofList
  [.db mainDb .read, .db mainDb .write, .table users .read, .table audit .write]

private def op (name : String) (p1 p2 p3 : Int := 0) (p4 : Vdbe.P4 := .none) : RawInstruction :=
  {opcode := .name name, p1 := p1, p2 := p2, p3 := p3, p4 := p4}

/-- `INSERT INTO audit VALUES (42)`, by hand, ending in `Halt code`. -/
private def insertAudit (code : Int) : RawProgram :=
  #[op "Transaction" 0 1, op "OpenWrite" 0 3 0, op "NewRowid" 0 1,
    op "Int64" 0 2 0 (.integer 42), op "MakeRecord" 2 1 3, op "Insert" 0 3 1, op "Halt" code]

/-- A real write, committed by `Halt 0`. -/
example :
    let out := run policy cat (insertAudit 0) 10 (Config.initial store)
    out.events = [.touch (.db mainDb .write), .touch (.table audit .write), .write audit, .commit] ∧
      out.config.committed audit = some [(1, [.integer 42])] ∧
      out.config.committed users = store users ∧ out.result = .halted := by
  decide

/-- An attempted write that is not committed: `Halt 1` publishes nothing. -/
example :
    let out := run policy cat (insertAudit 1) 10 (Config.initial store)
    Event.write audit ∈ out.events ∧ Event.commit ∉ out.events ∧
      out.config.working audit = some [(1, [.integer 42])] ∧ out.config.committed audit = some [] := by
  decide

/-- A write through one cursor is visible to a read cursor on the same table:
insert, then rewind a second cursor and emit the row. -/
private def insertThenRead : RawProgram :=
  #[op "Transaction" 0 1, op "OpenWrite" 0 3 0, op "Int64" 0 1 0 (.integer 7),
    op "Int64" 0 2 0 (.integer 43), op "MakeRecord" 2 1 3, op "Insert" 0 3 1,
    op "OpenRead" 1 3 0, op "Rewind" 1 10, op "Column" 1 0 4, op "ResultRow" 4 1, op "Halt"]

example :
    let out := run (Footprint.ofList [.db mainDb .write, .table audit .write, .table audit .read])
      cat insertThenRead 20 (Config.initial store)
    out.config.rows = [[.integer 43]] ∧ out.result = .halted := by
  decide +kernel

/-- Delete the row with rowid 1 from `audit`'s neighbour `users` is refused by
`policy`; with a footprint that writes `users` the row is removed. -/
private def deleteUser : RawProgram :=
  #[op "Transaction" 0 1, op "OpenWrite" 0 2 0, op "Int64" 0 1 0 (.integer 1),
    op "SeekRowid" 0 5 1, op "Delete" 0, op "Halt"]

example :
    (run policy cat deleteUser 10 (Config.initial store)).result =
      .fault (.denied (.table users .write)) := by
  decide

example :
    let out := run (Footprint.ofList [.db mainDb .write, .table users .write])
      cat deleteUser 10 (Config.initial store)
    out.config.committed users = some [(2, [.text "bob"])] ∧
      out.events = [.touch (.db mainDb .write), .touch (.table users .write), .write users,
        .commit] := by
  decide

/-- The attached database is not configured, whichever slot names it. -/
private def touchSecrets (slot : Int) : RawProgram :=
  #[op "Transaction" slot 1, op "OpenWrite" 0 2 slot, op "Int64" 0 1 0 (.integer 9),
    op "Int64" 0 2 0 (.integer 44), op "MakeRecord" 2 1 3, op "Insert" 0 3 1, op "Halt"]

example : (run policy cat (touchSecrets 2) 10 (Config.initial store)).result =
    .fault (.denied (.db otherDb .write)) := by decide
example : (run policy cat (touchSecrets 3) 10 (Config.initial store)).result =
    .fault (.denied (.db otherDb .write)) := by decide
example : (run policy cat (touchSecrets 3) 10 (Config.initial store)).events = [] := by decide

/-- Skipping the transaction does not help: the table touch is refused first. -/
example : (run policy cat ((touchSecrets 3).extract 1 7) 10 (Config.initial store)).result =
    .fault (.denied (.table secrets .write)) := by decide

/-- Without the guard the same bytecode does write and commit `secrets`, so the
refusals above are not vacuous. -/
example :
    let out := run Footprint.top cat (touchSecrets 3) 10 (Config.initial store)
    out.config.committed secrets = some [(1, [.text "key"]), (9, [.integer 44])] ∧
      policy.allows (.table secrets .write) = false := by
  decide

/-- A read cursor cannot be written through, even on a table the footprint
lets the program write. -/
example : (run policy cat
    #[op "Transaction" 0 1, op "OpenRead" 0 2 0, op "NewRowid" 0 1, op "Halt"] 10
      (Config.initial store)).result = .fault (.readOnlyCursor 0) := by decide

/-- `OpenWrite` needs a write transaction. -/
example : (run policy cat
    #[op "Transaction" 0 0, op "OpenWrite" 0 3 0, op "Halt"] 10 (Config.initial store)).result =
      .fault (.noTransaction mainDb .write) := by decide

/-- Unmodeled opcodes stop the runner. `Function` is the opcode through which
`ATTACH`'s callback runs (it is not an attach opcode; the callback is not
modeled), triggers run through `Program`, index maintenance uses `IdxInsert`. -/
example : (run policy cat #[op "Function" 0 1 2] 4 (Config.initial store)).result =
    .fault (.unmodeled (op "Function" 0 1 2)) := by decide
example : (run policy cat #[op "Program" 0 1 2] 4 (Config.initial store)).result =
    .fault (.unmodeled (op "Program" 0 1 2)) := by decide
example : (run policy cat #[op "IdxInsert" 0 1] 4 (Config.initial store)).result =
    .fault (.unmodeled (op "IdxInsert" 0 1)) := by decide

/-- Static footprint of the hand-written insert, and the guard transparency it
licenses. (`String8` checks its text with `String.contains`, which `decide`
does not unfold, so the runs in this file load integers.) -/
example : staticTouches cat (insertAudit 0) = [.db mainDb .write, .table audit .write] := by decide
example : within policy cat (insertAudit 0) = true := by decide
example : within policy cat (touchSecrets 3) = false := by decide
example : run policy cat (insertAudit 0) 10 (Config.initial store) =
    run Footprint.top cat (insertAudit 0) 10 (Config.initial store) :=
  run_eq_top (by decide) 10 _

/-- A fallback that skips unmodeled instructions without refusing them meets
the contract. -/
private def skipFallback : Fallback := fun _ c events c' => events = [] ∧ c' = c.advance

example (F : Footprint) : FallbackSafe F skipFallback := by
  rintro _ c events c' hinv ⟨rfl, rfl⟩
  exact ⟨⟨(fun _ h => by cases h), (fun _ _ => rfl), Or.inl rfl⟩, hinv.transactions, hinv.cursors⟩

/-- A fallback that writes a table outside the footprint does not. -/
private def leakyFallback : Fallback := fun _ c events c' =>
  events = [.write secrets] ∧ c' = {c with working := c.working.set secrets []}

example : ¬ FallbackSafe policy leakyFallback := by
  intro h
  have := (h (op "Function") (Config.initial store) _ _ (inv_initial policy store) ⟨rfl, rfl⟩).1.allowed
    (.write secrets) (List.mem_singleton_self _)
  exact (by decide : policy.allows (.table secrets .write) ≠ true) this

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Writable.trace_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Writable.trace_safe

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Writable.trace_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Writable.trace_frame

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Writable.run_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Writable.run_safe

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Writable.run_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Writable.run_eq_top

end Silmaril.Machine.SQLite.VirtualMachine.Writable.Checks

module

import Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.Thms

/-! A grounded demonstration of the compilation relation: a catalog with an
attached database under two aliases, three compiled statements run as an
autocommit script, and the theorems instantiated on it. -/

namespace Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.Checks

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine.Writable
open Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile

private def mainDb : DbId := ⟨0⟩
private def otherDb : DbId := ⟨7⟩
private def users : TableId := ⟨mainDb, ⟨1⟩⟩
private def audit : TableId := ⟨mainDb, ⟨2⟩⟩
private def secrets : TableId := ⟨otherDb, ⟨1⟩⟩

private def cat : Catalog where
  slot slot := if slot = 0 then some mainDb else if slot = 2 ∨ slot = 3 then some otherDb else none
  root db root :=
    if db = mainDb ∧ root = 2 then some ⟨1⟩
    else if db = mainDb ∧ root = 3 then some ⟨2⟩
    else if db = otherDb ∧ root = 2 then some ⟨1⟩
    else none

private def store : Store := fun table =>
  if table = users then some [(1, [.text "alice"]), (2, [.text "bob"])]
  else if table = audit then some [(5, [.integer 0])]
  else if table = secrets then some [(1, [.text "key"])]
  else none

private def usersAt : Location := ⟨0, 2⟩
private def auditAt : Location := ⟨0, 3⟩

/-- `INSERT INTO audit SELECT * FROM users; DELETE FROM users WHERE rowid = 1;
SELECT * FROM audit`, as source statements. -/
private def script : List Stmt :=
  [.copy users audit 1, .deleteRowid users 1, .scan audit 1]

private def codes : List RawProgram :=
  [Code.copy usersAt auditAt 1, Code.deleteRowid usersAt 1, Code.scan auditAt 1]

private theorem compiles : CompilesScript cat script codes :=
  .cons (.copy (by decide) (by decide)) (.cons (.deleteRowid (by decide))
    (.cons (.scan (by decide)) .nil))

/-- The source footprint is read off the statements. -/
example : (scriptFootprint script).allows (.table users .write) = true := by decide
example : (scriptFootprint script).allows (.db otherDb .read) = false := by decide

/-- The script really copies, deletes and commits: `audit` gains both user rows
after its existing rowid, `users` loses rowid 1, `secrets` is untouched. -/
example :
    let final := (runScript (scriptFootprint script) cat 40 codes store).2
    final audit = some [(5, [.integer 0]), (6, [.text "alice"]), (7, [.text "bob"])] ∧
      final users = some [(2, [.text "bob"])] ∧ final secrets = store secrets := by
  decide +kernel

/-- The final `scan` reads the committed result of the earlier statements. -/
example :
    let out := run (scriptFootprint script) cat (Code.scan auditAt 1) 20
      (Config.initial (runScript (scriptFootprint script) cat 40 (codes.take 2) store).2)
    out.config.rows = [[.integer 0], [.text "alice"], [.text "bob"]] ∧ out.result = .halted := by
  decide +kernel

/-- The theorems on this script, for every fuel and every initial store: the
guard is transparent, and `secrets`, which no statement writes, is unchanged. -/
example (fuel : Nat) (initial : Store) :
    runScript (scriptFootprint script) cat fuel codes initial =
        runScript Footprint.top cat fuel codes initial ∧
      (runScript Footprint.top cat fuel codes initial).2 secrets = initial secrets := by
  obtain ⟨heq, _, frame⟩ := compiled_script compiles fuel initial
  refine ⟨heq, frame secrets ?_⟩
  rintro ⟨stmt, hmem, htarget⟩
  simp only [script, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> simp [Stmt.target?, secrets, audit, users, mainDb, otherDb] at htarget

/-- Aliases are legitimate compilation targets: both slots that name the
attached database compile a scan of `secrets`, with the same footprint. -/
example : Compiles cat (.scan secrets 1) (Code.scan ⟨2, 2⟩ 1) := .scan (by decide)
example : Compiles cat (.scan secrets 1) (Code.scan ⟨3, 2⟩ 1) := .scan (by decide)
example : within (Footprint.ofList (Stmt.scan secrets 1).footprint) cat (Code.scan ⟨3, 2⟩ 1) = true :=
  compiles_within (.scan (by decide))

/-- The script's footprint does not contain that scan, and the guard refuses it
at the transaction on the attached database. -/
example : within (scriptFootprint script) cat (Code.scan ⟨3, 2⟩ 1) = false := by decide
example : (run (scriptFootprint script) cat (Code.scan ⟨3, 2⟩ 1) 20 (Config.initial store)).result =
    .fault (.denied (.db otherDb .read)) := by
  decide +kernel

/-- One-way inclusion, instantiated: the compiled copy is restricted to its
source footprint, and `Halt 0` is restricted but is not compiled from anything. -/
example : TargetRestricted (Footprint.ofList (Stmt.copy users audit 1).footprint) cat
    (Code.copy usersAt auditAt 1) :=
  image_targetRestricted ⟨_, fun _ h => by simpa [Footprint.ofList] using h,
    .copy (by decide) (by decide)⟩

example : ∀ stmt, ¬ Compiles cat stmt #[Code.halt] := (image_strict (cat := cat) Footprint.top).2

/-! Transitive table touch, as an obligation. A trigger-like cause that
deletes from `users` is not covered by an `INSERT INTO audit` footprint; an
audit insert caused by the copy is covered by the copy's footprint. -/

private def logInsert : Stmt := .insert audit [.integer 1]
private def copyUsers : Stmt := .copy users audit 1

private def causes (root sub : Stmt) : Stmt → List Stmt :=
  fun stmt => if stmt = root then [sub] else []

example : ¬ TransitiveTouch (causes logInsert (.deleteRowid users 1)) logInsert := by
  intro h
  have := h (.deleteRowid users 1) (.direct (by simp [causes])) (.table users .write)
    (by simp [Stmt.footprint, writeTouches])
  revert this
  decide

private theorem copy_covers : TransitiveTouch (causes copyUsers logInsert) copyUsers := by
  have only : ∀ sub, Reaches (causes copyUsers logInsert) copyUsers sub → sub = logInsert := by
    intro sub h
    induction h with
    | direct hmem => simpa [causes] using hmem
    | step _ hmem ih => subst ih; simp [causes, logInsert, copyUsers] at hmem
  intro sub h touch htouch
  rw [only sub h] at htouch
  simp only [logInsert, copyUsers, Stmt.footprint, readTouches, writeTouches, List.mem_cons,
    List.not_mem_nil, or_false] at htouch ⊢
  rcases htouch with rfl | rfl <;> simp

private theorem copy_then_log : CompilesScript cat [copyUsers, logInsert]
    [Code.copy usersAt auditAt 1, Code.insertValues auditAt [.integer 1]] :=
  .cons (.copy (by decide) (by decide)) (.cons (.insert (by decide) (by simp)) .nil)

/-- With the obligation assumed, the copy's footprint covers the caused insert,
and `users` (the copy's source, nobody's target) is unchanged for every store. -/
example (fuel : Nat) (initial : Store) :
    (runScript Footprint.top cat fuel
      [Code.copy usersAt auditAt 1, Code.insertValues auditAt [.integer 1]] initial).2 users =
      initial users := by
  have := (transitive_script (subs := [logInsert]) copy_covers
    (fun sub hs => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      exact .direct (by simp [causes]))
    copy_then_log fuel initial).2
  exact this users (by simp [copyUsers, Stmt.target?, users, audit])

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.image_targetRestricted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.image_targetRestricted

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.compiled_script' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.compiled_script

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.image_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.image_strict

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.transitive_script' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.transitive_script

end Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.Checks

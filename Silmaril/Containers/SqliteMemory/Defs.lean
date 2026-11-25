module

public import Silmaril.Containers.MemoryRefinement.Defs
public import Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.Bytes
public import Silmaril.Servers.State.Defs

/-! # Next SQLite contracts (statements only)

Inputs pin the library bytes. The caller must supply the process/driver that
actually performs the indicated calls, the SQL reference, and the admitted
workloads. These definitions do not construct any of those models.
-/

@[expose] public section

namespace Silmaril.Containers.SqliteMemory

open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So (F)
open Silmaril.Servers.State

/-- Values as seen by a `sqlite3_exec` callback: nullable text columns, in row order. -/
abbrev Rows := List (List (Option String))

inductive Call where
  | openDb (path : String) | exec (sql : String) | close

inductive Reply where
  | opened | rows (result : Rows) | closed | error (code : Int)

inductive Work where
  | openExecClose (path sql : String)
  | serialized (perThread : List (List Call))

abbrev Driver (Prog : Type) := Runtime (X86.Link.Blob × Work) Prog (Servers.State.Ev Call Reply)

def pathHistory (path sql : String) (rows : Rows) : Hist Call Reply :=
  [.call 0 (.openDb path), .ret 0 .opened, .call 1 (.exec sql), .ret 1 (.rows rows), .call 2 .close, .ret 2 .closed]

/-- A refused launch cannot discharge a path-safety goal. Safety by itself is not termination. -/
def Task.openExecClose {Prog} (driver : Driver Prog) (admitted : String → String → Prop) : Prop :=
  ∀ path sql, admitted path sql → let image := (F, Work.openExecClose path sql)
    (∃ prog, driver.load image = .ok prog) ∧ (∃ run, driver.beh image run) ∧
      (MemoryRefinement.ofRuns driver.beh).wp (fun _ => True) image

/-- On the successful fragment of a reference SQL evaluator, *all* runs complete the same API path. -/
def Task.queryResults {Prog DB} (driver : Driver Prog) (initial : String → DB)
    (evalSQL : DB → String → Option Rows) : Prop :=
  ∀ path sql rows, evalSQL (initial path) sql = some rows → let image := (F, Work.openExecClose path sql)
    (∃ run, driver.beh image run) ∧ (MemoryRefinement.ofRuns driver.beh).wp
      (Spec.totalCorrect fun history code => code = 0 ∧ history = pathHistory path sql rows) image

/-- One shared serialized connection. Check every finite prefix, including prefixes of infinite runs. -/
def Task.serialized {Prog DB} (driver : Driver Prog) (api : Atomic DB Call Reply) (initial : DB)
    (admitted : List (List Call) → Prop) : Prop :=
  ∀ calls, admitted calls → let image := (F, Work.serialized calls)
    (∃ prog, driver.load image = .ok prog) ∧ (∃ run, driver.beh image run) ∧ (MemoryRefinement.ofRuns driver.beh).wp
      (Spec.safe fun history => WellFormed history ∧ Linearizable api initial history) image

end Silmaril.Containers.SqliteMemory

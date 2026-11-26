module

import Silmaril.Languages.Python.Core.Closure.Executor.Thms

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Executor

private abbrev callerLayout : Layout := ⟨1, 1, 0⟩
private abbrev ownerLayout : Layout := ⟨0, 1, 1⟩
private abbrev forwardingLayout : Layout := ⟨0, 0, 1⟩
private def captured : CellId := ⟨0⟩
private def heap : Heap := ⟨1, fun _ => some (.int 7)⟩
private def owner (key : Nat) : Value := .function ⟨⟨key, ownerLayout⟩, #v[captured], []⟩
private def forwarding : Value := .function ⟨⟨2, forwardingLayout⟩, #v[captured], []⟩
private def aliasSlot : Slot callerLayout := .local 0
private def frame : Frame callerLayout := ⟨fun _ => some (owner 1), fun _ => captured, Fin.elim0⟩

private def entry (layout : Layout) (cellvars : Option (List String)) : Dispatch.Entry Body :=
  ⟨layout,
    { parameters := ⟨[], by simp⟩
      body := .ret (.literal .none)
      freevars := some ["forwarded"]
      cellvars := cellvars }⟩

private def table : CodeTable
  | 1 => some (entry ownerLayout (some ["owned"]))
  | 2 => some (entry forwardingLayout (some []))
  | 3 => some (entry ownerLayout none)
  | _ => none

private def next : Body callerLayout := .ret (.read aliasSlot)
private def points (name : String) : List UInt32 := name.toList.map Char.val
private def aliasTest (name : String) : CellvarsTest callerLayout := ⟨.slot aliasSlot, points name⟩
private def currentTest (name : String) : CellvarsTest callerLayout := ⟨.global "current", points name⟩
private def atCurrent (value : Value) : GlobalLookup
  | "current" => some value
  | _ => none

example : readCellvars table (owner 1) = .ok ["owned"] := rfl
example : readFreevars table (owner 1) = .ok ["forwarded"] := rfl
example : readCellvars table forwarding = .ok [] := rfl
example : readFreevars table forwarding = .ok ["forwarded"] := rfl
example : readCellvars table (owner 3) = .error (.unprofiled ⟨3, ownerLayout⟩) := rfl

-- The alias still selects the owning function after the current binding points elsewhere.
example : StepIn table (atCurrent forwarding) (.running heap frame (.assertCellvars (aliasTest "forwarded") next) [])
    none (.running heap frame next []) := .assertCellvarsTrue rfl
example : StepIn table (atCurrent forwarding) (.running heap frame (.assertCellvars (aliasTest "owned") next) [])
    none (.delivering heap [] (.error .assertionError)) := .assertCellvarsFalse rfl
example :
    advanceIn table (atCurrent forwarding) (.running heap frame (.assertCellvars (currentTest "owned") next) []) =
      some (none, .running heap frame next []) := rfl

example : (CellvarsTest.mk (.slot aliasSlot) (points "owned" ++ [0xD800])).evalIn
    table emptyGlobals heap frame = .ok true := rfl

private def readCurrent : State := .running heap frame (.assertCellvars (currentTest "owned") next) []
example : advanceIn table (atCurrent (owner 3)) readCurrent =
    some (some (.fault (.unprofiledCellvars ⟨3, ownerLayout⟩)),
      .faulted heap [] (.unprofiledCellvars ⟨3, ownerLayout⟩)) := rfl
example : advanceIn table (atCurrent .none) readCurrent =
    some (some (.fault .unsupportedCellvarsReceiver), .faulted heap [] .unsupportedCellvarsReceiver) := rfl
example : advance table readCurrent =
    some (none, .delivering heap [] (.error (.nameError "current"))) := rfl
example : advanceIn table (atCurrent (owner 4)) readCurrent =
    some (some (.fault (.missingCode 4)), .faulted heap [] (.missingCode 4)) := rfl
example : advanceIn table (atCurrent (.function ⟨⟨1, forwardingLayout⟩, #v[captured], []⟩)) readCurrent =
    some (some (.fault (.layoutMismatch forwardingLayout ownerLayout)),
      .faulted heap [] (.layoutMismatch forwardingLayout ownerLayout)) := rfl

private def dangling : CellvarsTest callerLayout := ⟨.slot (.owned 0), points "owned"⟩
example : advance table (.running Heap.empty frame (.assertCellvars dangling next) []) =
    some (some (.fault (.danglingCell captured)), .faulted Heap.empty [] (.danglingCell captured)) := rfl

#print axioms readCellvars_iff
#print axioms stepIn_iff

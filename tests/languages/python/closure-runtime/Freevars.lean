module

import Silmaril.Languages.Python.Core.Closure.Executor.Thms

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Executor

private abbrev callerLayout : Layout := ⟨1, 1, 0⟩
private abbrev codeLayout : Layout := ⟨0, 0, 1⟩
private abbrev emptyLayout : Layout := ⟨0, 0, 0⟩
private def captured : CellId := ⟨0⟩
private def heap : Heap := ⟨1, fun _ => some (.int 7)⟩
private def closure (key : Nat) : Value := .function ⟨⟨key, codeLayout⟩, #v[captured], []⟩
private def emptyClosure : Value := .function ⟨⟨2, emptyLayout⟩, #v[], []⟩
private def aliasSlot : Slot callerLayout := .local 0
private def frame : Frame callerLayout := ⟨fun _ => some (closure 1), fun _ => captured, Fin.elim0⟩

private def entry (layout : Layout) (metadata : Option (List String)) : Dispatch.Entry Body :=
  ⟨layout, { parameters := ⟨[], by simp⟩, body := .ret (.literal .none), freevars := metadata }⟩

private def table : CodeTable
  | 1 => some (entry codeLayout (some ["alpha"]))
  | 2 => some (entry emptyLayout (some []))
  | 3 => some (entry codeLayout none)
  | _ => none

private def next : Body callerLayout := .ret (.read aliasSlot)
private def alpha : List UInt32 := [97, 108, 112, 104, 97]
private def member : FreevarsTest callerLayout := ⟨.slot aliasSlot, alpha, true⟩
private def absent : FreevarsTest callerLayout := ⟨.global "current", alpha, false⟩
private def globals (current : Value) : GlobalLookup
  | "current" => some current
  | _ => none

example : readFreevars table (closure 1) = .ok ["alpha"] := rfl
example : readFreevars table emptyClosure = .ok [] := rfl
example : readFreevars table (closure 3) = .error (.unprofiled ⟨3, codeLayout⟩) := rfl

-- The retained function alias still sees its own code after the other binding changes.
example : StepIn table (globals emptyClosure) (.running heap frame (.assertFreevars member next) [])
    none (.running heap frame next []) := .assertFreevarsTrue rfl
example :
    advanceIn table (globals emptyClosure) (.running heap frame (.assertFreevars absent next) []) =
      some (none, .running heap frame next []) := rfl
example :
    advanceIn table (globals (closure 1)) (.running heap frame (.assertFreevars absent next) []) =
      some (none, .delivering heap [] (.error .assertionError)) := rfl

example : ({ member with needle := alpha ++ [0] } : FreevarsTest callerLayout).evalIn
    table emptyGlobals heap frame = .ok false := rfl

example :
    advanceIn table (globals (closure 3)) (.running heap frame (.assertFreevars absent next) []) =
      some (some (.fault (.unprofiledFreevars ⟨3, codeLayout⟩)),
        .faulted heap [] (.unprofiledFreevars ⟨3, codeLayout⟩)) := rfl

example :
    advanceIn table (globals (.int 3)) (.running heap frame (.assertFreevars absent next) []) =
      some (some (.fault .unsupportedFreevarsReceiver), .faulted heap [] .unsupportedFreevarsReceiver) := rfl

example :
    advanceIn table (globals (closure 4)) (.running heap frame (.assertFreevars absent next) []) =
      some (some (.fault (.missingCode 4)), .faulted heap [] (.missingCode 4)) := rfl

private def mismatched : Value := .function ⟨⟨1, emptyLayout⟩, #v[], []⟩
example :
    advanceIn table (globals mismatched) (.running heap frame (.assertFreevars absent next) []) =
      some (some (.fault (.layoutMismatch emptyLayout codeLayout)),
        .faulted heap [] (.layoutMismatch emptyLayout codeLayout)) := rfl

example :
    advance table (.running heap frame (.assertFreevars absent next) []) =
      some (none, .delivering heap [] (.error (.nameError "current"))) := rfl

private def dangling : FreevarsTest callerLayout := ⟨.slot (.owned 0), alpha, true⟩
example :
    advance table (.running Heap.empty frame (.assertFreevars dangling next) []) =
      some (some (.fault (.danglingCell captured)), .faulted Heap.empty [] (.danglingCell captured)) := rfl

#print axioms readFreevars_iff
#print axioms stepIn_iff

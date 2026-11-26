module

import Silmaril.Languages.Python.Core.Closure.Executor.Thms

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Executor

private abbrev callerLayout : Layout := ⟨1, 1, 0⟩
private abbrev receiverLayout : Layout := ⟨0, 0, 1⟩
private def captured : CellId := ⟨0⟩
private def originalHeap : Heap := ⟨1, fun _ => some (.int 3)⟩
private def heap : Heap := (originalHeap.write captured (.int 7)).getD originalHeap
private def receiver (key : Nat) : Value := .function ⟨⟨key, receiverLayout⟩, #v[captured], []⟩
private def aliasSlot : Slot callerLayout := .local 0
private def frame : Frame callerLayout := ⟨fun _ => some (receiver 1), fun _ => captured, Fin.elim0⟩

private def row (codeNames : Option Dispatch.ProfiledCodeNames) : Dispatch.Entry Body :=
  ⟨receiverLayout,
    { parameters := ⟨[], by simp⟩
      body := .ret (.literal .none)
      freevars := some ["captured"]
      cellvars := some []
      codeNames := codeNames }⟩

private def table : CodeTable
  | 1 => some (row (some ⟨.cpython3135ExecOptimize0, ["café"]⟩))
  | 2 => some (row (some ⟨.cpython3135ExecOptimize0, ["live"]⟩))
  | 3 => some (row (some ⟨.cpython3135ExecOptimize0, []⟩))
  | 4 => some (row none)
  | 5 => some (row (some ⟨.cpython373ExecOptimize0, ["café", "AssertionError"]⟩))
  | _ => none

private def next : Body callerLayout := .ret (.read aliasSlot)
private def needle : List UInt32 := [0x63, 0x61, 0x66, 0xE9]
private def aliasTest : CodeNamesTest callerLayout := ⟨.slot aliasSlot, needle⟩
private def currentTest : CodeNamesTest callerLayout := ⟨.global "current", needle⟩
private def atCurrent (value : Value) : GlobalLookup
  | "current" => some value
  | _ => none

private def saved : Call.Saved Continuation := ⟨callerLayout, frame, some (.discard, next)⟩
private def readCurrent : State := .running heap frame (.assertCodeNames currentTest next) [saved]

-- A prior write updates the alias's captured cell. The metadata check reads
-- the alias's code even when the current global function has different names.
example : runPrefixIn table (atCurrent (receiver 2)) 2
    (.running originalHeap frame
      (.store (.owned 0) (.literal (.int 7)) (.assertCodeNames aliasTest next)) [saved]) =
    ([], .running heap frame next [saved]) := rfl
example : frame.read heap aliasSlot = .ok (receiver 1) := rfl
example : heap.lookup captured = some (some (.int 7)) := rfl
example : StepIn table (atCurrent (receiver 2)) readCurrent none
    (.delivering heap [saved] (.error .assertionError)) := .assertCodeNamesFalse rfl

-- Membership uses the exact code points, including needles outside Char.
example : (CodeNamesTest.mk (.slot aliasSlot) [0x63, 0x61, 0x66, 0x65, 0x301]).evalIn
    table emptyGlobals heap frame = .ok false := rfl
example : (CodeNamesTest.mk (.slot aliasSlot) (needle ++ [0xD800])).evalIn
    table emptyGlobals heap frame = .ok false := rfl

example : readCodeNames table (receiver 3) = .ok [] := rfl
example : StepIn table (atCurrent (receiver 3)) readCurrent none
    (.delivering heap [saved] (.error .assertionError)) := .assertCodeNamesFalse rfl
example : advanceIn table (atCurrent (receiver 4)) readCurrent =
    some (some (.fault (.unprofiledCodeNames ⟨4, receiverLayout⟩)),
      .faulted heap [saved] (.unprofiledCodeNames ⟨4, receiverLayout⟩)) := rfl
example : advanceIn table (atCurrent (receiver 5)) readCurrent =
    some (some (.fault (.wrongCodeNamesProfile ⟨5, receiverLayout⟩ .cpython373ExecOptimize0)),
      .faulted heap [saved] (.wrongCodeNamesProfile ⟨5, receiverLayout⟩ .cpython373ExecOptimize0)) := rfl
example : advanceIn table (atCurrent (.int 1)) readCurrent =
    some (some (.fault .unsupportedCodeNamesReceiver), .faulted heap [saved] .unsupportedCodeNamesReceiver) := rfl

example : advance table readCurrent =
    some (none, .delivering heap [saved] (.error (.nameError "current"))) := rfl
example : advanceIn table (atCurrent (receiver 6)) readCurrent =
    some (some (.fault (.missingCode 6)), .faulted heap [saved] (.missingCode 6)) := rfl
example : advanceIn table (atCurrent (.function ⟨⟨1, callerLayout⟩, #v[], []⟩)) readCurrent =
    some (some (.fault (.layoutMismatch callerLayout receiverLayout)),
      .faulted heap [saved] (.layoutMismatch callerLayout receiverLayout)) := rfl
example : advance table (.running Heap.empty frame
    (.assertCodeNames ⟨.slot (.owned 0), needle⟩ next) [saved]) =
    some (some (.fault (.danglingCell captured)), .faulted Heap.empty [saved] (.danglingCell captured)) := rfl

#print axioms readCodeNames_iff
#print axioms stepIn_iff

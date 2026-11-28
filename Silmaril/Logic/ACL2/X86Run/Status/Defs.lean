module

public import Silmaril.Logic.ACL2.Standard.Objects.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status

open Standard

/-- The remaining logical functions, observed using ACL2's non-NIL truth convention.
The domains include malformed records and arbitrary keys. -/
structure RecordPrimitives where
  /-- X86ISA::X86REC-P1, the ordered and typed entry-list recognizer. -/
  entriesP : Object → Bool
  /-- ACL2::<<, the strict order used by lookup. -/
  keyBefore : Object → Object → Bool

/-- X86REC-P. A record wraps a nonempty valid entry list around a non-record tail. -/
def recordP (p : RecordPrimitives) : Object → Bool
  | .cons entries tail => p.entriesP entries && decide (entries ≠ .nil) && !recordP p tail
  | _ => false

/-- X86REC-TO-MTR preserves an existing record and otherwise wraps the value as a bad tail. -/
def toRecord (p : RecordPrimitives) (state : Object) : Object :=
  if recordP p state then state else .cons .nil state

/-- The X86$AP recognizer compares the record's bad part with NIL. -/
def logicalStateP (p : RecordPrimitives) (state : Object) : Bool :=
  decide ((toRecord p state).cdr = Object.nil)

/-- X86REC-GET1 for a fixed key and its default. ENDP tests for any atom, and
CAR and CDR remain total even on malformed entries. -/
def readEntries (p : RecordPrimitives) (key fallback : Object) : Object → Object
  | .cons entry rest =>
    if p.keyBefore key entry.car then fallback
    else if key = entry.car then entry.cdr
    else readEntries p key fallback rest
  | _ => fallback

/-- A scalar XR call supplies a keyword paired with the NIL index. The concrete
foundation uses a separate zero-based slot in its logical list. -/
structure Accessor where
  field : Object
  fallback : Object
  slot : Nat

def Accessor.key (a : Accessor) : Object := .cons a.field .nil

def Accessor.read (a : Accessor) (p : RecordPrimitives) (state : Object) : Object :=
  readEntries p a.key a.fallback (toRecord p state).car

/-- The total ACL2 NTH equations on a quoted natural index. -/
def nthSlot : Nat → Object → Object
  | 0, state => state.car
  | n + 1, state => nthSlot n state.cdr

def Accessor.readFoundation (a : Accessor) (state : Object) : Object :=
  nthSlot a.slot state

structure Observation where
  label : String
  state : Object
  valid : Bool
  ms : Object
  fault : Object

end Silmaril.Logic.ACL2.X86Run.Status

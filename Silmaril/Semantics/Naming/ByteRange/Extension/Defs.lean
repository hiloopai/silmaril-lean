module

public import Silmaril.Semantics.Naming.ByteRange.Defs

@[expose] public section

namespace Silmaril.Semantics.Naming.ByteRange

/-- A closed observation. A range is exact and in bounds (including an empty
range at EOF). Only `whole` and `eof` assert a length. -/
inductive Fact where
  | range (offset : Nat) (fragment : Bytes)
  | whole (bytes : Bytes)
  | eof (length : Nat)

def Fact.bound : Fact → Nat
  | .range offset fragment => offset + fragment.length
  | .whole bytes => bytes.length
  | .eof length => length

def Fact.end? : Fact → Option Nat
  | .range .. => none
  | .whole bytes => some bytes.length
  | .eof length => some length

def Fact.reads (fact : Fact) (pos : Nat) (byte : UInt8) : Prop :=
  match fact with
  | .range offset fragment => ∃ index, offset + index = pos ∧ fragment[index]? = some byte
  | .whole bytes => bytes[pos]? = some byte
  | .eof _ => False

def Fact.Holds (fact : Fact) (bytes : Bytes) : Prop :=
  fact.bound ≤ bytes.length ∧ (∀ length, fact.end? = some length → bytes.length = length) ∧
    ∀ pos byte, fact.reads pos byte → bytes[pos]? = some byte

abbrev Observations (Name : Type) := Name → Fact → Prop

namespace Observations

variable {Name : Type}

def Queried (seen : Observations Name) (name : Name) : Prop := ∃ fact, seen name fact

def Fits (seen : Observations Name) (name : Name) (bytes : Bytes) : Prop :=
  ∀ fact, seen name fact → fact.Holds bytes

def ByteAt (seen : Observations Name) (name : Name) (pos : Nat) (byte : UInt8) : Prop :=
  ∃ fact, seen name fact ∧ fact.reads pos byte

def Agrees (seen : Observations Name) (name : Name) : Prop :=
  ∀ pos left right, seen.ByteAt name pos left → seen.ByteAt name pos right → left = right

/-- A finite bound per name, not a bound on the number of observations. -/
def Bounded (seen : Observations Name) (name : Name) : Prop :=
  ∃ bound, ∀ fact, seen name fact → fact.bound ≤ bound

/-- Every explicit length must accommodate every fact. Since an end also
contributes its length as a bound, this forces all explicit ends to agree. -/
def RespectsEnds (seen : Observations Name) (name : Name) : Prop :=
  ∀ ending fact length, seen name ending → seen name fact → ending.end? = some length →
    fact.bound ≤ length

def Compatible (seen : Observations Name) (name : Name) : Prop :=
  seen.Agrees name ∧ seen.Bounded name ∧ seen.RespectsEnds name

/-- One binding per queried name. Retain all old bindings and add no unqueried ones. -/
def Model (seen : Observations Name) (base rel : Relation Name Bytes) : Prop :=
  Binding rel ∧ Subset base rel ∧
    (∀ ⦃name bytes⦄, rel name bytes → base name bytes ∨ seen.Queried name) ∧
    ∀ name, seen.Queried name → ∃ bytes, rel name bytes ∧ seen.Fits name bytes

/-- Choose distinct compatible representatives for distinct new names, avoiding all base payloads. -/
def FreshAssignment (seen : Observations Name) (base : Relation Name Bytes)
    (pick : Name → Bytes) : Prop :=
  let fresh := fun name => seen.Queried name ∧ ¬ ∃ bytes, base name bytes
  (∀ name, fresh name → seen.Fits name (pick name)) ∧
    (∀ name, fresh name → ∀ old, ¬ base old (pick name)) ∧
    ∀ left right, fresh left → fresh right → pick left = pick right → left = right

end Observations
end Silmaril.Semantics.Naming.ByteRange

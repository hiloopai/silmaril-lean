module

public import Init.Data.ByteArray
public import Mathlib.Basic.Rel
public import Mathlib.Data.List.Forall2

/-! # Cursor success graphs

Inclusion is the refinement order on exact successes, not a choice between
diagnostics or parses. Byte positions are offsets into a representation;
semantic context is independent of the cursor and its upper bound.
-/

@[expose] public section

namespace Silmaril.Parse.DecodeGraph

open scoped SetRel

/-- The active half-open window is `[pos, stop)`. -/
structure Input (Context Buffer : Type*) where
  context : Context
  bytes : Buffer
  stop : Nat
  pos : Nat

variable {Context Buffer Source Target : Type*}

def Input.atPos (input : Input Context Buffer) (pos : Nat) : Input Context Buffer :=
  { input with pos }

/-- A success names a value and its absolute end cursor. The half-open span
is `[input.pos, endPos)`; bounds and progress are separate contracts. -/
abbrev Graph (Context Buffer Value : Type*) := SetRel (Input Context Buffer) (Value × Nat)

abbrev Reference (Context Value : Type*) := Graph Context (List UInt8) Value

/-- A semantic context can be added without changing a context-free graph. -/
def ignoreContext (graph : Graph Unit Buffer Source) : Graph Context Buffer Source :=
  {(input, result) | (⟨(), input.bytes, input.stop, input.pos⟩, result) ∈ graph}

def Deterministic (graph : Graph Context Buffer Source) : Prop :=
  Relator.RightUnique (fun input result => input ~[graph] result)

def Positive (graph : Graph Context Buffer Source) : Prop :=
  ∀ ⦃input value endPos⦄, (input, (value, endPos)) ∈ graph → input.pos < endPos

/-- A specification view, not a requirement to materialize a list at runtime. -/
structure ByteView (Buffer : Type*) where
  toList : Buffer → List UInt8
  Valid : Buffer → Prop

def ByteView.byteArray : ByteView ByteArray where
  toList bytes := bytes.data.toList
  Valid _ := True

def ValidWindow (view : ByteView Buffer) (input : Input Context Buffer) : Prop :=
  view.Valid input.bytes ∧ input.pos ≤ input.stop ∧ input.stop ≤ (view.toList input.bytes).length

/-- Import reference successes to a representation, preserving both cursors. -/
def overView (view : ByteView Buffer) (reference : Reference Context Source) : Graph Context Buffer Source :=
  {(input, result) | view.Valid input.bytes ∧
    (⟨input.context, view.toList input.bytes, input.stop, input.pos⟩, result) ∈ reference}

/-- Interpret an exact-consumption byte-list grammar at a cursor. -/
def ofGrammar (grammar : Context → List UInt8 → Source → Prop) :
    Reference Context Source :=
  Set.ofPred fun (input, result) =>
    input.pos ≤ result.2 ∧ result.2 ≤ input.stop ∧ input.stop ≤ input.bytes.length ∧
      grammar input.context (input.bytes.extract input.pos result.2) result.1

/-- Compare all successes on valid inputs, without first filtering their ends. -/
def SoundFor (view : ByteView Buffer) (graph : Graph Context Buffer Source)
    (reference : Reference Context Source) : Prop :=
  ∀ ⦃input result⦄, ValidWindow view input → (input, result) ∈ graph → (input, result) ∈ overView view reference

/-- Coverage of every specified success on valid inputs. With a deterministic
implementation this requires that the specification be unambiguous there. -/
def CompleteFor (view : ByteView Buffer) (graph : Graph Context Buffer Source)
    (reference : Reference Context Source) : Prop :=
  ∀ ⦃input result⦄, ValidWindow view input → (input, result) ∈ overView view reference → (input, result) ∈ graph

/-- Relate values without changing the end cursor (hence the consumed span). -/
def onSpan (rel : SetRel Source Target) : SetRel (Source × Nat) (Target × Nat) :=
  {(source, target) | source.1 ~[rel] target.1 ∧ source.2 = target.2}

/-- For lists, `rel` can relate entire lists of different lengths. -/
def transport (rel : SetRel Source Target) (graph : Graph Context Buffer Source) : Graph Context Buffer Target :=
  graph ○ onSpan rel

def map (f : Source → Target) (graph : Graph Context Buffer Source) : Graph Context Buffer Target :=
  transport (Function.graph f) graph

/-- The aligned, equal-length special case of a relation on whole lists. -/
def pointwise (rel : SetRel Source Target) : SetRel (List Source) (List Target) :=
  {(source, target) | List.Forall₂ (fun left right => left ~[rel] right) source target}

end Silmaril.Parse.DecodeGraph

module

public import Silmaril.Data.Layout.Defs

/-!
# Record layouts: ABI-resolved and observed

Three objects describe one C record, and this slice keeps them apart:

1. **Source description** (`Silmaril.Data.Layout.Decl`, from `Silmaril.Data.Layout.Source`):
   member names and C types, no numbers.
2. **ABI-resolved layout** (`RecordLayout`, here): what a target data model (`DataModel`:
   scalar sizes and alignments) and the psABI placement rule (`declLayout`: each member at the
   next multiple of its alignment, union members at zero, size rounded up to the alignment)
   assign. Units are bytes. `resolveEnv` computes it for a whole source.
3. **Observed layout** (`ObservedRecord`, here): what a compiler *reports*. Units are bits,
   as in Clang's `-fdump-record-layouts-simple` (`Size`, `DataSize`, `Alignment`,
   `FieldOffsets`). Observations arrive as JSON (`Silmaril.Data.Layout.Interchange`) and are
   compared with `RecordLayout.observe`, which says what the model predicts the compiler
   reports; `Agrees` is equality of the two, record by record and in order.

`RecordLayout` carries no C types: an entry is a named, aligned byte range of a record of a
given size and alignment, the vocabulary FFI layers and compiled-layout dumps share. It is
the intended place for later non-C producers (for instance a compiled C++ record seen through
a C-compatible ABI), which would add entry kinds of their own; nothing here models C++, and
`dataSize` (Clang's size without tail padding) is predicted equal to `size`, which holds for
the C records this slice accepts and is exactly what such an extension would have to revisit.

`Target` bundles a data model with its well-formedness proof and the Clang target triple an
observation of that data model must name.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Record

open Silmaril.Data.Layout

/-! ## ABI-resolved layouts -/

/-- A member as a byte range: offset from the start of the record, size and alignment. -/
structure Entry where
  name : String
  offset : Nat
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

/-- An ABI-resolved record layout, in bytes, without source types. -/
structure RecordLayout where
  kind : Kind
  name : String
  size : Nat
  align : Nat
  entries : List Entry
  deriving DecidableEq, Repr

/-- Forget the C types of a computed declaration layout. -/
def ofDeclLayout (L : DeclLayout) : RecordLayout where
  kind := L.kind
  name := L.tag
  size := L.shape.size
  align := L.shape.align
  entries := L.fields.map fun f =>
    { name := f.name, offset := f.off, size := f.size, align := f.align }

/-- Well-formedness, as `DeclLayout.WF`: power-of-two alignments, the record's alignment
divides its size, members in bounds and aligned, struct members in order and disjoint, union
members at offset zero. -/
structure RecordLayout.WF (R : RecordLayout) : Prop where
  pow2 : Pow2 R.align
  alignDvd : R.align ∣ R.size
  inBounds : ∀ e ∈ R.entries, e.offset + e.size ≤ R.size
  aligned : ∀ e ∈ R.entries, e.align ∣ e.offset
  entryAlignDvd : ∀ e ∈ R.entries, e.align ∣ R.align
  entryPow2 : ∀ e ∈ R.entries, Pow2 e.align
  disjoint : R.kind = .struct → R.entries.Pairwise fun e f => e.offset + e.size ≤ f.offset
  unionZero : R.kind = .union → ∀ e ∈ R.entries, e.offset = 0

/-- Layouts of every record of a source, in order, under data model `dm`. -/
def resolveEnv (dm : DataModel) (env : Env) : Except String (List RecordLayout) :=
  traverse (fun d => match declLayout dm env d with
    | .ok L => .ok (ofDeclLayout L)
    | .error e => .error s!"{d.tag}: {e}") env

/-- What a source declaration and a layout share: kind, name and member names. -/
def declNames (d : Decl) : Kind × String × List String := (d.kind, d.tag, d.fields.map (·.name))

def layoutNames (R : RecordLayout) : Kind × String × List String :=
  (R.kind, R.name, R.entries.map (·.name))

/-! ## Observed layouts -/

/-- A member as a compiler reports it: name and offset in bits. -/
structure ObservedField where
  name : String
  offset : Nat
  deriving DecidableEq, Repr

/-- A record as a compiler reports it, in bits: `size`, `dataSize` (size without tail
padding) and `align` as in Clang's `ASTRecordLayout`, and the member offsets in declaration
order. -/
structure ObservedRecord where
  kind : Kind
  name : String
  size : Nat
  dataSize : Nat
  align : Nat
  fields : List ObservedField
  deriving DecidableEq, Repr

/-- What the model predicts a compiler reports for a record. -/
def RecordLayout.observe (R : RecordLayout) : ObservedRecord where
  kind := R.kind
  name := R.name
  size := 8 * R.size
  dataSize := 8 * R.size
  align := 8 * R.align
  fields := R.entries.map fun e => { name := e.name, offset := 8 * e.offset }

/-- An observation agrees with computed layouts: the same records, in order, with the
predicted sizes, alignments and member offsets. -/
def Agrees (Ls : List RecordLayout) (obs : List ObservedRecord) : Prop :=
  obs = Ls.map RecordLayout.observe

instance (Ls : List RecordLayout) (obs : List ObservedRecord) : Decidable (Agrees Ls obs) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Targets -/

/-- A target: a well-formed data model and the Clang triple whose layouts it predicts. -/
structure Target where
  /-- Short name, used for generated declarations (`x86_64`). -/
  name : String
  model : DataModel
  wf : model.WF
  /-- The `-triple` an observation must name (`x86_64-unknown-linux-gnu`). -/
  triple : String

end Silmaril.Data.Layout.Record

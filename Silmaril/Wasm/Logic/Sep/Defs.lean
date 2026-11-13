module

public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# Separation logic over the Core 3.0 store: definitions

A **heap** is a partial map from store locations (`Loc`: a GC structure field, a
GC array element, a byte of a linear memory, a global) to their contents
(`Cell`). Locations are the store's own addresses: `field a i` is field `i` of
the structure at address `a` of `Store.structs`, `byte m i` is byte `i` of the
memory at address `m` of `Store.mems` (so multiple memories are distinct
address spaces). A store **satisfies** a heap (`Heap.Sat`) if it holds every
cell of the heap. Assertions (`Assn`) are predicates on heaps, with the
separating conjunction `Assn.sep` (`∗`) of disjoint heaps and the points-to
assertion `pointsTo l c`.

`STriple Pre code Post` is the every-run triple with the **frame baked in**: for
every frame heap `hF` disjoint from the precondition's heap, if the store
satisfies both, every run of `code` (`Silmaril.Wasm.Logic.Hoare.HWP`) exits with a
heap for the postcondition that is still disjoint from `hF`, and the final store
satisfies both. The frame rule (`STriple.frame`) is then a theorem about heaps
alone; each instruction rule has to show that the instruction keeps every cell
outside its footprint (`Silmaril.Proofs.Wasm.Logic.Sep.GC` for the GC structure
instructions).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Sep

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP)

variable {H : Type}

/-- A location in the store. -/
inductive Loc where
  /-- Field `i` of the GC structure at address `a`. -/
  | field (a i : Nat)
  /-- Element `i` of the GC array at address `a`. -/
  | elem (a i : Nat)
  /-- Byte `i` of the linear memory at address `m`. -/
  | byte (m i : Nat)
  /-- The global at address `a`. -/
  | global (a : Nat)
  deriving DecidableEq

/-- The contents of a location. -/
inductive Cell where
  | fv (v : FieldVal)
  | byte (b : UInt8)
  | val (v : Val)

/-- What the store holds at a location. -/
def cellOf (s : Store H) : Loc → Option Cell
  | .field a i => (s.structs[a]?.bind fun si => si.fields[i]?).map .fv
  | .elem a i => (s.arrays[a]?.bind fun ai => ai.fields[i]?).map .fv
  | .byte m i => (s.mems[m]?.bind fun mi => mi.bytes[i]?).map .byte
  | .global a => s.globals[a]?.map fun g => .val g.value

/-- A heap: some cells of the store. -/
abbrev Heap := Loc → Option Cell

/-- The store holds every cell of the heap. -/
def Heap.Sat (s : Store H) (h : Heap) : Prop := ∀ l c, h l = some c → cellOf s l = some c

/-- Disjoint heaps. -/
def Heap.Disj (h₁ h₂ : Heap) : Prop := ∀ l, h₁ l = none ∨ h₂ l = none

/-- The union of heaps (left-biased; disjoint in every use). -/
def Heap.union (h₁ h₂ : Heap) : Heap := fun l =>
  match h₁ l with
  | some c => some c
  | none => h₂ l

/-- The empty heap. -/
def Heap.empty : Heap := fun _ => none

/-- The heap of one cell. -/
def Heap.single (l : Loc) (c : Cell) : Heap := fun l' => if l' = l then some c else none

/-- The fields of the structure at `a`. -/
def Heap.struct (a : Nat) (fs : List FieldVal) : Heap := fun l =>
  match l with
  | .field a' i => if a' = a then fs[i]?.map .fv else none
  | _ => none

/-- The elements of the array at `a`. -/
def Heap.array (a : Nat) (fs : List FieldVal) : Heap := fun l =>
  match l with
  | .elem a' i => if a' = a then fs[i]?.map .fv else none
  | _ => none

/-- Assertions on heaps. -/
abbrev Assn := Heap → Prop

/-- The separating conjunction. -/
def Assn.sep (A B : Assn) : Assn := fun h =>
  ∃ h₁ h₂, Heap.Disj h₁ h₂ ∧ h = h₁.union h₂ ∧ A h₁ ∧ B h₂

@[inherit_doc] infixr:35 " ∗ " => Assn.sep

/-- The empty heap. -/
def emp : Assn := fun h => h = Heap.empty

/-- `l ↦ c`. -/
def pointsTo (l : Loc) (c : Cell) : Assn := fun h => h = Heap.single l c

/-- The structure at `a` has exactly the fields `fs`. -/
def structPts (a : Nat) (fs : List FieldVal) : Assn := fun h => h = Heap.struct a fs

/-- The array at `a` has exactly the elements `fs`. -/
def arrayPts (a : Nat) (fs : List FieldVal) : Assn := fun h => h = Heap.array a fs

/-- **The separation-logic triple** with the frame baked in. -/
def STriple (P : Profile) (host : HostSemantics H) (Pre : Frame → Assn) (code : List Admin)
    (Post : Frame → Outcome → Assn) : Prop :=
  ∀ (s : Store H) (f : Frame) (hP hF : Heap), Heap.Disj hP hF → Heap.Sat s (hP.union hF) →
    Pre f hP → HWP P host s f code fun s' f' o =>
      ∃ hQ, Heap.Disj hQ hF ∧ Heap.Sat s' (hQ.union hF) ∧ Post f' o hQ

end Silmaril.Wasm.Logic.Sep

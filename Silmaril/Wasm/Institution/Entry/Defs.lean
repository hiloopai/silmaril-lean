module

public import Silmaril.Wasm.Institution.Generic.Defs
public import Silmaril.Wasm.Binaryen.Behaviour
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

/-!
# Single-invocation (entry-point) logics

The observational semantics behind silmaril's *fixed-environment, single-invocation* notions
`Equiv.ModuleRefines E R` and `Equiv.ModuleEquiv E R` (`Silmaril.Wasm.Equiv.Module`), for any
invocation boundary `E : Equiv.EntryPoints S A V` (programs or stores `S`, entry names `A`,
values `V`). For Wasm modules, `E` is `Binaryen.moduleEntryPoints P host Env` (instantiate in an
environment allowed by `Env`, run the start function, invoke one export); for Binaryen IR it is
`Binaryen.entryPoints P host Env`, its pullback along lowering.

* **Interfaces**: sets of entry names `X : Set A`, under inclusion.
* **Semantic objects** (`Obj A V X`): for each entry in `X` and argument list, a well-formedness
  premise and a set of behaviours. The reduct hides entries outside `X`.
* **Operators**: closures `close R` of behaviour sets under a behaviour relation.
* **Refinement** `Refines R a b`: every behaviour of every well-formed invocation of `a` is
  `R`-related to one of `b` (the demonic lifting `Behaviours.Refines R`), entry by entry.
  `Equiv R a b := Refines R a b ∧ Refines Rᵒᵖ b a`.

Unlike the session logics (`Silmaril.Wasm.Institution.Session`), invocations do not share a store:
this is the closed-program, per-export notion. No translation between the two families is
claimed here.
-/

namespace Silmaril.Wasm.Institution.Entry

open CategoryTheory Silmaril.Wasm

variable (A V : Type)

/-- A semantic object of the entry interface `X`. -/
structure Obj (X : Set A) where
  /-- Well-formedness of an invocation (`EntryPoints.Ok`). -/
  ok : X → List V → Prop
  /-- Behaviours of an invocation (`EntryPoints.beh`). -/
  beh : X → List V → Set (Behaviour V)

variable {A V}

/-- Hiding entries outside `X`. -/
def Obj.restrict {X Y : Set A} (f : X ⟶ Y) (a : Obj A V Y) : Obj A V X :=
  ⟨fun x vs => a.ok ⟨x.1, f.le x.2⟩ vs, fun x vs => a.beh ⟨x.1, f.le x.2⟩ vs⟩

/-- Closure of behaviour sets under a behaviour relation. -/
def close (R : Behaviour V → Behaviour V → Prop) {X : Set A} (a : Obj A V X) : Obj A V X :=
  ⟨a.ok, fun x vs => {b | ∃ b' ∈ a.beh x vs, R b b'}⟩

/-- Entry-wise demonic refinement. -/
def Refines (R : Behaviour V → Behaviour V → Prop) {X : Set A} (a b : Obj A V X) : Prop :=
  ∀ x vs, a.ok x vs → Behaviours.Refines R (a.beh x vs) (b.beh x vs)

/-- Entry-wise equivalence, in the shape of `Equiv.ModuleEquiv`. -/
def Equiv (R : Behaviour V → Behaviour V → Prop) {X : Set A} (a b : Obj A V X) : Prop :=
  Refines R a b ∧ Refines (fun x y => R y x) b a

variable {S : Type}

/-- The denotation of a program (or store) `s` at interface `X`. -/
def den (E : Equiv.EntryPoints S A V) (X : Set A) (s : S) : Obj A V X :=
  ⟨fun x vs => E.Ok s x.1 vs, fun x vs => E.beh s x.1 vs⟩

/-- The entry-point semantics of `E` with refinement `Le`. -/
def mk (E : Equiv.EntryPoints S A V) (Le : ∀ X : Set A, Obj A V X → Obj A V X → Prop) :
    ObsSemantics (Set A) where
  Sem := Obj A V
  restrict := Obj.restrict
  restrict_id _ := rfl
  restrict_comp _ _ _ := rfl
  Prog := S
  den := den E
  Op := Behaviour V → Behaviour V → Prop
  op _ R a := close R a
  Le := Le

/-- The refinement logic of `E` under `R`: the logic of `Equiv.ModuleRefines E R`. -/
abbrev entryRef (E : Equiv.EntryPoints S A V) (R : Behaviour V → Behaviour V → Prop) :
    ObsSemantics (Set A) :=
  mk E (fun _ => Refines R)

/-- The equivalence logic of `E` under `R`: the logic of `Equiv.ModuleEquiv E R`. -/
abbrev entryEquiv (E : Equiv.EntryPoints S A V) (R : Behaviour V → Behaviour V → Prop) :
    ObsSemantics (Set A) :=
  mk E (fun _ => Equiv R)

end Silmaril.Wasm.Institution.Entry

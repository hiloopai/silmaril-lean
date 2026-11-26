module

public import Silmaril.X86.Link.Env.Defs
public import Silmaril.X86.Sep.Alloc.Defs
public import Silmaril.X86.Link.FnSpec.Defs

/-! # Linking any allocator with a client proved against the interface

A client is proved once, `∀ A : Sep.Alloc.Iface`; an allocator unit exports `malloc`/`free`/…
with the specs of *its own* abstraction `A p σ` (which may depend on its placement, i.e. its
globals, and on the link valuation). `link_any_allocator` (`AllocLink/Thms.lean`) instantiates
the client at the allocator's abstraction at the link point and closes the client's allocator
imports with the allocator's exports.

* `nMalloc`, `nFree`, `nCalloc`, `nRealloc` and `allocNames`: the C names, as `NameBytes`.
* `allocSpecOf A nm`: the interface spec of the allocator entry point `nm` (`mallocSpec A`,
  `freeSpec A`, `callocSpec A`, `reallocSpec A`; `unverified` for any other name, never used).
* `ClientFamily Tag`: one object file, and a unit `tu A` for every allocator abstraction; its
  imports named in `allocNames` carry `allocSpecOf A` (`imports_alloc`).
* `ClientFamily.fam C M pA`: the client as a `UnitFam`, at the abstraction of the allocator
  unit `M` placed at `pA` (its specs depend on the link valuation only through `M.A pA σ`).
* `AllocUnit Tag`: a unit family `fam` and its abstraction `A p σ`; for every name in
  `provides`, `fam.tu p σ` exports it with `allocSpecOf (A p σ)` (`exports_alloc`).
* `ResolvedIn L units ext i`: the import `i` is served by an export of some unit (or an
  external entry) with a refining spec: one clause of `Contract.ImportsClosed`.
-/

@[expose] public section

namespace Silmaril.X86.Link.AllocLink

universe u

open Silmaril.Formats.ELF
open Silmaril.X86.Sep (FnSpec)
open Silmaril.X86.Sep.Alloc
open Silmaril.X86.Link.Unit
open Silmaril.X86.Link.Contract
open Silmaril.X86.Link.Env

/-- `malloc`. -/
def nMalloc : NameBytes := [0x6d, 0x61, 0x6c, 0x6c, 0x6f, 0x63]
/-- `free`. -/
def nFree : NameBytes := [0x66, 0x72, 0x65, 0x65]
/-- `calloc`. -/
def nCalloc : NameBytes := [0x63, 0x61, 0x6c, 0x6c, 0x6f, 0x63]
/-- `realloc`. -/
def nRealloc : NameBytes := [0x72, 0x65, 0x61, 0x6c, 0x6c, 0x6f, 0x63]

/-- The allocator entry points a client may import. -/
def allocNames : List NameBytes := [nMalloc, nFree, nCalloc, nRealloc]

/-- The interface spec of an allocator entry point (`unverified` off `allocNames`). -/
def allocSpecOf (A : Iface) (nm : NameBytes) : FnSpec :=
  if nm = nMalloc then mallocSpec A
  else if nm = nFree then freeSpec A
  else if nm = nCalloc then callocSpec A
  else if nm = nRealloc then reallocSpec A
  else Silmaril.X86.Link.FnSpec.unverified

/-- **A client unit family**: one object file, and a unit for every allocator abstraction,
whose allocator imports carry that abstraction's interface specs. -/
structure ClientFamily (Tag : Type) where
  tu : Iface → TU Tag FnSpec
  object_const : ∀ A B, (tu A).object = (tu B).object
  imports_alloc : ∀ A, ∀ i ∈ (tu A).imports, i.name ∈ allocNames → i.spec = allocSpecOf A i.name

/-- **An allocator unit**: a unit family whose specs may depend on its placement and the
link valuation, its abstraction `A p σ`, and the entry points it provides with exactly the
interface specs of `A p σ`. -/
structure AllocUnit (Tag : Type) where
  fam : UnitFam Tag FnSpec
  A : Placement → Valuation → Iface
  provides : List NameBytes
  exports_alloc : ∀ p σ, ∀ nm ∈ provides,
    ∃ e ∈ (fam.tu p σ).exports, e.name = nm ∧ e.spec = allocSpecOf (A p σ) nm

/-- The client as a unit family, at the abstraction of the allocator unit `M` placed at
`pA`. -/
def ClientFamily.fam {Tag : Type} (C : ClientFamily Tag) (M : AllocUnit Tag) (pA : Placement) :
    UnitFam Tag FnSpec :=
  ⟨fun _ σ => C.tu (M.A pA σ), fun _ _ _ _ => C.object_const _ _⟩

/-- The import `i` is served by an export of some unit, or by an external entry, with a
refining spec (one clause of `Contract.ImportsClosed`). -/
def ResolvedIn {Tag : Type} {Spec : Type u} (L : Logic Spec) (units : List (TU Tag Spec))
    (ext : List (Entry Tag Spec)) (i : Entry Tag Spec) : Prop :=
  (∃ (slot : Nat) (v : TU Tag Spec), units[slot]? = some v ∧
      ∃ e ∈ v.exports, e.name = i.name ∧ L.Sub e.spec i.spec) ∨
    (∃ x ∈ ext, x.name = i.name ∧ L.Sub x.spec i.spec)

end Silmaril.X86.Link.AllocLink

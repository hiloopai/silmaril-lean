module

public import Silmaril.X86.Link.AllocLink.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Defs

/-! # Linking any mutex at the object level

`link_any_allocator` (`Link/AllocLink`) generalised from `Sep.Alloc.Iface` and
`FnSpec` to **any abstraction type** `Ab` and **any link logic** `L : Logic Spec`, then
instantiated at the CIR `Mutex.Iface`. The proofs (`Silmaril.Proofs.X86.Concurrency.Cir.Mutex
.Link`) are AllocLink's, copied with the types generalised, and go through `Link/Env`'s
`link_compose_env`.

* `IfaceClient Tag Ab Spec names specOf`: one object file and a unit `tu A` for every
  abstraction `A : Ab`; its imports named in `names` carry `specOf A` (`imports_iface`).
* `IfaceUnit Tag Ab Spec names specOf`: a unit family and its abstraction `A p σ` (which may
  depend on its placement and the link valuation); for every name in `provides`, `fam.tu p σ`
  exports it with `specOf (A p σ)` (`exports_iface`).
* `IfaceClient.fam C M pA`: the client as a `UnitFam`, at `M`'s abstraction placed at `pA`.

For the mutex:

* `nLock`, `nUnlock`, `mutexNames`: `mutex_lock`, `mutex_unlock` as `NameBytes`;
* `Render Spec`: how a link logic's specs render the interface's two operations (`lock M`,
  `unlock M`; `other` off the two names). `mutexSpecOf ρ M nm` is the spec of entry `nm`.
* `MutexClient`, `MutexUnit`: the two structures at `Ab := Mutex.Iface`.

No `Render` into x86 `FnSpec` is given: that needs the CIR specs (the `Safe` over CIR code)
restated over x86 calls, i.e. call-level translation validation, which the checker does not do
(calls fail it). The CIR-level linking theorem is `Mutex.link_any_mutex` (`Mutex/Thms.lean`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Mutex.Link

universe u

open Silmaril.Formats.ELF
open Silmaril.X86.Link.Unit
open Silmaril.X86.Link.Contract
open Silmaril.X86.Link.Env

/-- **A client of an interface**: one object file, and a unit for every abstraction `A`, whose
imports named in `names` carry `specOf A`. -/
structure IfaceClient (Tag : Type) (Ab : Type) (Spec : Type u) (names : List NameBytes)
    (specOf : Ab → NameBytes → Spec) where
  tu : Ab → TU Tag Spec
  object_const : ∀ A B, (tu A).object = (tu B).object
  imports_iface : ∀ A, ∀ i ∈ (tu A).imports, i.name ∈ names → i.spec = specOf A i.name

/-- **A provider of an interface**: a unit family, its abstraction at each placement and
valuation, and the entry points it provides with exactly the interface's specs. -/
structure IfaceUnit (Tag : Type) (Ab : Type) (Spec : Type u) (names : List NameBytes)
    (specOf : Ab → NameBytes → Spec) where
  fam : UnitFam Tag Spec
  A : Placement → Valuation → Ab
  provides : List NameBytes
  exports_iface : ∀ p σ, ∀ nm ∈ provides,
    ∃ e ∈ (fam.tu p σ).exports, e.name = nm ∧ e.spec = specOf (A p σ) nm

variable {Tag Ab : Type} {Spec : Type u} {names : List NameBytes}
  {specOf : Ab → NameBytes → Spec}

/-- The client as a unit family, at the abstraction of the provider `M` placed at `pA`. -/
def IfaceClient.fam (C : IfaceClient Tag Ab Spec names specOf)
    (M : IfaceUnit Tag Ab Spec names specOf) (pA : Placement) : UnitFam Tag Spec :=
  ⟨fun _ σ => C.tu (M.A pA σ), fun _ _ _ _ => C.object_const _ _⟩

/-! ## The mutex instance -/

/-- `mutex_lock`. -/
def nLock : NameBytes := [0x6d, 0x75, 0x74, 0x65, 0x78, 0x5f, 0x6c, 0x6f, 0x63, 0x6b]
/-- `mutex_unlock`. -/
def nUnlock : NameBytes := [0x6d, 0x75, 0x74, 0x65, 0x78, 0x5f, 0x75, 0x6e, 0x6c, 0x6f, 0x63, 0x6b]

/-- The mutex entry points a client may import. -/
def mutexNames : List NameBytes := [nLock, nUnlock]

/-- How a link logic's specs render the mutex interface. -/
structure Render (Spec : Type u) where
  lock : Iface → Spec
  unlock : Iface → Spec
  other : Spec

/-- The spec of the mutex entry point `nm` at `M`. -/
def mutexSpecOf (ρ : Render Spec) (M : Iface) (nm : NameBytes) : Spec :=
  if nm = nLock then ρ.lock M else if nm = nUnlock then ρ.unlock M else ρ.other

/-- A client of the mutex interface. -/
abbrev MutexClient (Tag : Type) (Spec : Type u) (ρ : Render Spec) :=
  IfaceClient Tag Iface Spec mutexNames (mutexSpecOf ρ)

/-- A mutex unit. -/
abbrev MutexUnit (Tag : Type) (Spec : Type u) (ρ : Render Spec) :=
  IfaceUnit Tag Iface Spec mutexNames (mutexSpecOf ρ)

end Silmaril.X86.Concurrency.Cir.Mutex.Link

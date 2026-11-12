module

public import Silmaril.Libc.X86Alloc.Spec.Defs
public import Silmaril.X86.Sep.AllocS.Thms
import Silmaril.Raw.Libc.X86Alloc.Spec

/-!
# Allocator specification layers: refinements

* `mallocSpecL_subH`, `freeSpecL_subH`: a live allocator is a loose one (`⊑ₕ`: the abstract
  state is chosen from the fragment).
* `mallocSpecF_sub`: a functional allocator is live for its own capacity model `R.toCap`.
* `mallocSpecF_subH_along`, `freeSpecL_subH_along`: along a simulation `R.Sim C α Inv`, a functional
  allocator is live for the capacity model `C`.
* `mallocSpecL_post_avail`: under `C.avail s n` the postcondition has no failure branch.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc

open Silmaril.X86 (Word)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc

theorem mallocSpecL_subH {C : CapModel} (B : IfaceL C) :
    (mallocSpecL B).SubH (mallocSpec B.toIface) :=
  Silmaril.Raw.Libc.X86Alloc.Spec.mallocSpecL_subH B

theorem freeSpecL_subH {C : CapModel} (B : IfaceL C) :
    (freeSpecL B).SubH (freeSpec B.toIface) :=
  Silmaril.Raw.Libc.X86Alloc.Spec.freeSpecL_subH B

theorem mallocSpecF_sub {R : RefModel} (B : IfaceL R.toCap) :
    (mallocSpecF B).Sub (mallocSpecL B) :=
  Silmaril.Raw.Libc.X86Alloc.Spec.mallocSpecF_sub B

theorem mallocSpecF_subH_along {R : RefModel} {C : CapModel} {α : R.St → C.St}
    {Inv : R.St → Prop} (hsim : R.Sim C α Inv) (B : IfaceL R.toCap) :
    (mallocSpecF B).SubH (mallocSpecL (B.along α Inv)) :=
  Silmaril.Raw.Libc.X86Alloc.Spec.mallocSpecF_subH_along hsim B

theorem freeSpecL_subH_along {R : RefModel} {C : CapModel} {α : R.St → C.St}
    {Inv : R.St → Prop} (hsim : R.Sim C α Inv) (B : IfaceL R.toCap) :
    (freeSpecL B).SubH (freeSpecL (B.along α Inv)) :=
  Silmaril.Raw.Libc.X86Alloc.Spec.freeSpecL_subH_along hsim B

/-- **An available request is served**: the postcondition is a fresh block and the next state. -/
theorem mallocSpecL_post_avail {C : CapModel} (B : IfaceL C) {s : C.St} {n v : Word}
    (h : C.avail s n.toNat) :
    (mallocSpecL B).post (s, n) v ⊢ₛ
      (B.toIface.Fresh v n.toNat ∗ B.mmS (C.alloc s n.toNat v)) :=
  sor_elim (spure_sep_elim fun ⟨_, hna⟩ => absurd h hna) (entails_refl _)

/-- The identity simulation: a reference model simulates its own capacity model. -/
theorem RefModel.sim_self (R : RefModel) : R.Sim R.toCap id (fun _ => True) :=
  ⟨fun _ _ _ h => h, fun _ _ _ _ => ⟨trivial, rfl⟩, fun _ _ _ _ _ => ⟨trivial, rfl⟩⟩

end Silmaril.Libc.X86Alloc

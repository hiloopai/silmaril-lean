module

public import Silmaril.X86.Sep.AllocS.Defs
public import Silmaril.X86.Sep.Alloc.Thms
import Silmaril.Proofs.X86.Sep.AllocS

/-!
# The availability layer: laws

* **Heap-dependent refinement.** `FnSpec.Sub.subH`, `FnSpec.SubH.trans` and
  `FnSpec.SubH.satWith`/`FnSpec.SubH.sat`: a function meeting `S` meets every `T` with
  `S ⊑ₕ T`.
* **`IfaceS` refines `Iface`.** `mallocSpecS_subH : mallocSpecS B ⊑ₕ mallocSpec B.toIface`,
  hence `mallocSpecS_sat_toIface`: a `malloc` with availability is a `malloc` of the loose
  interface. `freeSpec`, `callocSpec`, `reallocSpec`, `usableSpec` of `B.toIface` are the
  loose ones unchanged.
* **Using availability.** `mallocS_post_avail`: when `B.avail s n` held at the call, the
  postcondition gives the state and a `Fresh` block, with no `NULL` case;
  `mallocS_post_null_false`: under `avail`, the postcondition at `NULL` is unsatisfiable.
* **Looseness.** `toIface_toS`, `mallocSpec_sub_toS`: every loose allocator is a strong one
  that promises nothing (`avail := False`), so the layer adds no obligation.
-/

@[expose] public section

namespace Silmaril.X86.Sep

open Silmaril.X86 (Word)
open Silmaril.X86.SegVC (Isa)

variable {σ : Type} {I : Isa σ}

theorem FnSpec.Sub.subH {S T : FnSpec} (h : S.Sub T) : S.SubH T :=
  Silmaril.Proofs.X86.SepAllocS.sub_subH h

theorem FnSpec.SubH.trans {S T U : FnSpec} (h₁ : S.SubH T) (h₂ : T.SubH U) : S.SubH U :=
  Silmaril.Proofs.X86.SepAllocS.subH_trans h₁ h₂

/-- **Refinement with a hidden choice**: a function meeting `S` meets every `T` with
`S ⊑ₕ T`. -/
theorem FnSpec.SubH.satWith {A : Word → Prop} {S T : FnSpec} {C : SProp} {entry : Word}
    (hsub : S.SubH T) (hS : S.SatWith I A C entry) : T.SatWith I A C entry :=
  Silmaril.Proofs.X86.SepAllocS.subH_satWith hS hsub

theorem FnSpec.SubH.sat {S T : FnSpec} {C : SProp} {entry : Word}
    (hsub : S.SubH T) (hS : S.Sat I C entry) : T.Sat I C entry :=
  hsub.satWith hS

end Silmaril.X86.Sep

namespace Silmaril.X86.Sep.Alloc

open Silmaril.X86 (Word)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep

variable {σ : Type} {I : Isa σ}

/-- **`mallocSpecS B ⊑ₕ mallocSpec B.toIface`.** -/
theorem mallocSpecS_subH (B : IfaceS) : (mallocSpecS B).SubH (mallocSpec B.toIface) :=
  Silmaril.Proofs.X86.SepAllocS.mallocSpecS_subH B

/-- **A `malloc` with availability is a `malloc` of the loose interface.** -/
theorem mallocSpecS_sat_toIface {A : Word → Prop} {B : IfaceS} {C : SProp} {entry : Word}
    (h : (mallocSpecS B).SatWith I A C entry) : (mallocSpec B.toIface).SatWith I A C entry :=
  (mallocSpecS_subH B).satWith h

/-- When the request was available, `malloc` returned a fresh block. -/
theorem mallocS_post_avail (B : IfaceS) {s : B.St} {n v : Word} (ha : B.avail s n.toNat) :
    (mallocSpecS B).post (s, n) v ⊢ₛ (B.toIface.mm ∗ B.toIface.Fresh v n.toNat) :=
  Silmaril.Proofs.X86.SepAllocS.mallocS_post_avail B ha

/-- Under `avail`, no fragment satisfies the postcondition with result `NULL`. -/
theorem mallocS_post_null_false (B : IfaceS) {s : B.St} {n : Word} (ha : B.avail s n.toNat) :
    ∀ h, ¬ (mallocSpecS B).post (s, n) 0 h :=
  Silmaril.Proofs.X86.SepAllocS.mallocS_post_null_false B ha

theorem toIface_toS (A : Iface) : A.toS.toIface = A :=
  Silmaril.Proofs.X86.SepAllocS.toIface_toS A

/-- Every loose `malloc` is a strong one that promises nothing. -/
theorem mallocSpec_sub_toS (A : Iface) : (mallocSpec A).Sub (mallocSpecS A.toS) :=
  Silmaril.Proofs.X86.SepAllocS.mallocSpec_sub_toS A

end Silmaril.X86.Sep.Alloc

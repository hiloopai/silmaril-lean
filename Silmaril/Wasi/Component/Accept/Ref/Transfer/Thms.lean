module

public import Silmaril.Wasi.Component.Accept.Ref.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Transfer.Defs
import Silmaril.Proofs.Wasi.Component.Accept.RefTransfer

/-! # Acceptance across engines with the same static part

For a store simulation `S : E.StoreSim I`:

* `accepted_of_withStore`: a byte string accepted on REF over `E.withStore I` is accepted on REF
  over `E`, given related dispatchers (`DispatchRel S`) and related linked instantiation
  programs `acceptLinkedProg c` (`ProgRel S`). The proof is the machine simulation
  `Machine.Transfer.steps_sim`, applied to the instantiation run and to the environment's run.
* `dispatchRel_dispatch`, `progRel_acceptLinkedProg`: both hypotheses hold. REF programs reach
  the core store only through the core operations of `Canon.Op`, so `dispatch` and
  `acceptLinkedProg c` over `E.withStore I` are the same terms as over `E` up to unfolding, and
  related by `ProgRel.refl`. The kernel checks that the terms agree (`prog_rel_refl`).
* `accepted_of_storeSim`: so acceptance over `E.withStore I` is acceptance over `E`, with no
  further hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Machine.Transfer

variable {E : CoreEngine} {I : E.StoreImpl}

/-- **Acceptance over `E.withStore I` is acceptance over `E`**, given related dispatchers and
related instantiation programs. -/
theorem accepted_of_withStore [∀ a b, Decidable (E.ExternSub a b)] (S : E.StoreSim I)
    {prof : ProfileKind} {c : Syntax.Component E.Module} {w : List UInt8}
    (hd : DispatchRel S (dispatch (E := E.withStore I)) (dispatch (E := E)))
    (hp : ProgRel S (acceptLinkedProg (E := E.withStore I) c) (acceptLinkedProg (E := E) c))
    (h : Accepted (E := E.withStore I) prof c w) : Accepted (E := E) prof c w :=
  Silmaril.Proofs.Wasi.Component.Accept.RefTransfer.accepted_of_withStore S hd hp h

/-- The acceptor's dispatchers over `E.withStore I` and over `E` are related. -/
theorem dispatchRel_dispatch [∀ a b, Decidable (E.ExternSub a b)] (S : E.StoreSim I) :
    DispatchRel S (dispatch (E := E.withStore I)) (dispatch (E := E)) :=
  Silmaril.Proofs.Wasi.Component.Accept.RefTransfer.dispatchRel S

/-- The linked instantiation programs over `E.withStore I` and over `E` are related. -/
theorem progRel_acceptLinkedProg [∀ a b, Decidable (E.ExternSub a b)] (S : E.StoreSim I)
    (c : Syntax.Component E.Module) :
    ProgRel S (acceptLinkedProg (E := E.withStore I) c) (acceptLinkedProg (E := E) c) :=
  Silmaril.Proofs.Wasi.Component.Accept.RefTransfer.progRel_acceptLinkedProg S c

/-- **Acceptance over `E.withStore I` is acceptance over `E`**, for every store simulation. -/
theorem accepted_of_storeSim [∀ a b, Decidable (E.ExternSub a b)] (S : E.StoreSim I)
    {prof : ProfileKind} {c : Syntax.Component E.Module} {w : List UInt8}
    (h : Accepted (E := E.withStore I) prof c w) : Accepted (E := E) prof c w :=
  accepted_of_withStore S (dispatchRel_dispatch S) (progRel_acceptLinkedProg S c) h

end Silmaril.Wasi.Accept.Ref

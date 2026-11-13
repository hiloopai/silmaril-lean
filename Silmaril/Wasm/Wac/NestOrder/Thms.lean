module

public import Silmaril.Wasm.Wac.NestOrder.Defs
public import Silmaril.Wasm.Component.Passes.Flatten.Thms
public import Silmaril.Proofs.Wasm.Wac.Nest.Order

/-!
# WAC: nesting = inlining with first-occurrence import order

`nest_inline` (`Silmaril.Wasm.Wac.NestInline.Thms`) is stated over sorted imports
(`Graph.toCompSorted`). This module removes that restriction, under the same `NestOk`:

* `nest_inline_toComp`: with `Graph.toComp`'s first-occurrence import order, the nested
  composition means the inlined one **with its imports renumbered**: the handler of
  `importPerm I₁ I₂` (each import of the inlined side forwarded to the import of the same
  name of the nested side) composed below the inlined composition;
* `nest_inline_toComp_of_iface_eq`: when the two sides list their imports in the same
  order, the meanings are equal;
* `NestOrderExample.nest_inline_toComp_not_eq`: they need not: an instance satisfying
  `NestOk` whose two flat components have their imports in different orders, so the flat
  components differ. The equality of the flat components with first-occurrence import
  order (the unsorted form of `flatten_nest_inline`) is **false**; the renumbering
  in `nest_inline_toComp` cannot be dropped.

Proofs in `Silmaril.Proofs.Wasm.Wac.Nest.Order`: changing the order of the imports of a
composition graph is a specialisation by `importPerm` (`flatten_buildWith_perm`, a
consequence of the run over valuations `flatten_mkNodes`), and the nested and inlined
graphs have imports with the same lookups (`lookup_iface_inline`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

/-- **Nesting = inlining, first-occurrence import order**: under `NestOk`, the
composition `g₂` whose package `k0` is the composition `g₁` means the inlined composition
with its imports renumbered by `importPerm`. -/
theorem nest_inline_toComp {M : Type} [CoreModule M] (C : CoreSem M) (P : Nat → Comp M)
    (k0 : Nat) (g₁ g₂ : Graph) (ok : NestOk P k0 g₁ g₂) :
    (g₂.toComp (nestPkgs P k0 g₁)).denU C =
      (Silmaril.Games.Strategy.ofHandler (implsH (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)).length
          (importPerm (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k))
            ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).iface fun k => sigOf (P k))))).comp
        (((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).toComp P).denU C) := by
  have hl : ∀ x, (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)).lookup x =
      ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).iface fun k => sigOf (P k)).lookup x :=
    fun x => (NestProof.lookup_iface_inline P ok x).symm
  rw [← denU_flatten' C, NestProof.flatten_nest_inline_perm P ok,
    denU_specialise' C _ (NestProof.scoped_importPerm hl) _ (NestProof.length_importPerm _ _)]

/-- When the nested and the inlined composition list their imports in the same order,
they have the same meaning. -/
theorem nest_inline_toComp_of_iface_eq {M : Type} [CoreModule M] (C : CoreSem M)
    (P : Nat → Comp M) (k0 : Nat) (g₁ g₂ : Graph) (ok : NestOk P k0 g₁ g₂)
    (h : (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)) =
      (Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).iface fun k => sigOf (P k)) :
    (g₂.toComp (nestPkgs P k0 g₁)).denU C =
      ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).toComp P).denU C := by
  rw [← denU_flatten' C, ← denU_flatten' C ((Graph.inline _ k0 g₁ g₂).toComp P)]
  show (flatten (g₂.buildWith _ _ _)).denU C = (flatten ((Graph.inline _ k0 g₁ g₂).buildWith _ _ _)).denU C
  rw [h, NestProof.flatten_nest_inline_with P ok]

end Silmaril.Wasm.Wac

module

public import Silmaril.Wasm.Wac.Nest.Defs
public import Silmaril.Wasm.Component.Passes.Flatten.Thms
public import Silmaril.Proofs.Wasm.Wac.Nest.Main

/-!
# WAC: nesting = inlining

A composition `g₁` (over packages `P`) used as package `k0` of a composition `g₂`
(`nestPkgs`) means the same as `g₂` with every instance of `k0` replaced by the instances
of `g₁` (`Graph.inline S k0 g₁ g₂`), both built over sorted imports
(`Graph.toCompSorted`), under the conditions `NestOk` (`Silmaril.Wasm.Wac.Nest.Defs`).

* `NestProof.flatten_nest_inline`: the two flat (linked) components are **equal**;
* `nest_inline`: so the two components have the same meaning, for every core semantics.

## The proof

Proofs in `Silmaril.Proofs.Wasm.Wac.Nest`:

* `flatten_buildWith` (`Nest.Run`): flattening a composition graph is a run `gRun` over
  *valuations* (`Src → Impl`, the flat wiring of every reference), with no index
  arithmetic left;
* `sim_inner` (`Nest.Sim`): the run of `g₁`'s instances inside the nested instance,
  over the valuation built from the instance's arguments, and the run of the inlined
  instances at the top level agree, under the shift `innerSrc` of references;
* `sim_outer` (`Nest.Outer`, `Nest.Inline`): the runs of `g₂` over `nestPkgs P k0 g₁` and
  of the inlined graph over `P` produce the same flat nodes; their valuations are
  related by the renaming `Graph.inline` builds, which changes at every inlined node
  (`SimV`, `RenOk`);
* `sortIface_iface_inline` (`Nest.Iface`, `Nest.IfaceFold`, `Nest.Sort`): both graphs
  use the same imports at the same types, so their sorted imports are equal.

The frozen target , `Task.nest_inline`, wrote the inlined side as
`g₂.inline S k0 g₁`. By dot notation that is `Graph.inline S k0 g₂ g₁`: `g₁` with the
instances of `k0` replaced by `g₂`, the reverse of the intended composition. Under
`NestOk.noSelf`, `g₁` has no instance of `k0`, so that side is `g₁` with its references renamed, and the claim
would equate `g₂[k0 := g₁]` with `g₁`. The target is therefore restated here with the
arguments in the intended order, `Graph.inline S k0 g₁ g₂`. The literal frozen statement
is neither proved nor refuted, and the frozen `def` is removed.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

/-- **Nesting = inlining**: under `NestOk`, the composition `g₂` whose package `k0` is
the composition `g₁` has the meaning of `g₂` with `g₁` inlined, both with their imports
in the canonical order. -/
theorem nest_inline {M : Type} [CoreModule M] (C : CoreSem M) (P : Nat → Comp M) (k0 : Nat)
    (g₁ g₂ : Graph) (ok : NestOk P k0 g₁ g₂) :
    (g₂.toCompSorted (nestPkgs P k0 g₁)).denU C =
      ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).toCompSorted P).denU C := by
  rw [← denU_flatten' C, ← denU_flatten' C ((Graph.inline _ k0 g₁ g₂).toCompSorted P),
    NestProof.flatten_nest_inline P ok]

end Silmaril.Wasm.Wac

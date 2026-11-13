module

public import Silmaril.Wasm.Wac.Nest.Defs
public import Silmaril.Wasm.Component.Passes.Flatten.Thms
public import Silmaril.Proofs.Wasm.Wac.Nest.Main

/-!
# WAC: nesting = inlining with no condition on the imports

`Wac.nest_inline` (`Silmaril.Wasm.Wac.NestInline.Thms`) asks `NestOk`, whose field `used` says
that every import of the nested composition `g₁` is used by one of its instances: inlining
loses an unused import, so the nested and the inlined composition do not have the same
imports. Here both sides are built over **the same** import list, and the only conditions
are the run conditions `NestRunOk` (both graphs well formed, exports of instances):

* `nest_inline_with`: for every import list `I`, `g₂` over the packages `nestPkgs P k0 g₁`
  and the inlined graph over `P`, both built over `I`, have the same meaning;
* **`nest_inline_any`**: the nested composition `g₂.toComp (nestPkgs P k0 g₁)` (its imports in
  first-occurrence order, unused imports of `g₁` included) means the inlined graph built over
  those same imports. No `used`, `declared`, `typed` or `noSelf` hypothesis, and no reordering
  of the imports.

The inlined graph built over a list that contains imports it does not use is, by
`Wac.buildWith_sub_equiv` (`Silmaril.Wasm.Wac.Unused.Thms`), the algebra's promotion `reimport`
of the inlined graph over the imports it uses.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- **Nesting = inlining over any import list**, under the run conditions only. -/
theorem nest_inline_with (C : CoreSem M) (P : Nat → Comp M) (k0 : Nat) (g₁ g₂ : Graph)
    (ok : NestRunOk P k0 g₁ g₂) (I : Iface) :
    (g₂.buildWith (fun k => sigOf (nestPkgs P k0 g₁ k)) (nestPkgs P k0 g₁) I).denU C =
      ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).buildWith (fun k => sigOf (P k)) P I).denU C := by
  rw [← denU_flatten' C, ← denU_flatten' C ((Graph.inline _ k0 g₁ g₂).buildWith _ P I),
    NestProof.flatten_nest_inline_run P ok I]

/-- **Nesting = inlining, no condition on the imports**: the nested composition means the
inlined graph built over the nested composition's own imports (first-occurrence order,
unused imports of `g₁` included). -/
theorem nest_inline_any (C : CoreSem M) (P : Nat → Comp M) (k0 : Nat) (g₁ g₂ : Graph)
    (ok : NestRunOk P k0 g₁ g₂) :
    (g₂.toComp (nestPkgs P k0 g₁)).denU C =
      ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).buildWith (fun k => sigOf (P k)) P
        (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k))).denU C :=
  nest_inline_with C P k0 g₁ g₂ ok _

/-- The same with the imports in the canonical (sorted) order of `Graph.toCompSorted`. -/
theorem nest_inline_sorted (C : CoreSem M) (P : Nat → Comp M) (k0 : Nat) (g₁ g₂ : Graph)
    (ok : NestRunOk P k0 g₁ g₂) :
    (g₂.toCompSorted (nestPkgs P k0 g₁)).denU C =
      ((Graph.inline (fun k => sigOf (P k)) k0 g₁ g₂).buildWith (fun k => sigOf (P k)) P
        (sortIface (g₂.iface fun k => sigOf (nestPkgs P k0 g₁ k)))).denU C :=
  nest_inline_with C P k0 g₁ g₂ ok _

end Silmaril.Wasm.Wac

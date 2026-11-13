module

public import Silmaril.Wasm.Wac.Graph.Defs
public import Silmaril.Wasm.Component.Passes.Flatten.Thms
public import Silmaril.Proofs.Wasm.Wac.Graph

/-!
# WAC composition graphs: theorems

Proofs in `Silmaril.Proofs.Wasm.Wac.Graph`, corollaries here.

## Promotion and merging of imports

* `toComp_explicate`: filling in every unsatisfied import `q` of an instance with the
  explicit argument `imp q` (as `wac` writes compositions in WAT) does not change the
  composed component;
* `nodup_imports_toComp`: the imports of the composition have distinct names
  (duplicates merged); `mem_iface_of_uses`, `mem_iface_of_declared`: every used and
  every declared import is an import of the composition;
* `resolve_promoted`: an unsatisfied import `q` is wired to the import `q` of the
  composition, the same for every instance that leaves `q` unsatisfied.

## Compositionality

* `denU_toComp`: the meaning of the composition is `Graph.sem` of the meanings of the
  packages (`Graph.sem` only uses the package interfaces and meanings);
* `toComp_mono`: replacing packages by refinements with the same interfaces refines the
  composition; `toComp_congr`: by equivalent packages, gives an equivalent composition;
* `denU_flatten_toComp`: the flat (linked) IR of the composition, the `linked` node of
  `Silmaril.Wasm.Institution.CompGraph.compGraph`, has the same meaning.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component Silmaril.Games

variable {M : Type}

theorem length_exports_sigOf (c : Comp M) : (sigOf c).exports.length = c.exports.length := by
  simp [sigOf]

/-- **Explicit promotion does not change the composed component.** -/
theorem toComp_explicate (P : Nat → Comp M) (g : Graph) :
    (g.explicate fun k => sigOf (P k)).toComp P = g.toComp P :=
  build_explicate _ P g

/-- The imports of a composition have distinct names. -/
theorem nodup_imports_toComp (P : Nat → Comp M) (g : Graph) :
    (names (g.toComp P).imports).Nodup :=
  nodup_iface _ g

variable [CoreModule M]

/-- **Compositionality**: the meaning of a composition is a function of the meanings
of its packages. -/
theorem denU_toComp (C : CoreSem M) (P : Nat → Comp M) (g : Graph) :
    (g.toComp P).denU C = g.sem (fun k => sigOf (P k)) (fun k => (P k).denU C) :=
  denU_build C _ P (fun k => (length_exports_sigOf (P k)).symm) g

/-- **Refining packages refines the composition** (same interfaces). -/
theorem toComp_mono {C C' : CoreSem M} {P P' : Nat → Comp M}
    (hs : ∀ k, sigOf (P k) = sigOf (P' k)) (hle : ∀ k, (P k).denU C ≤ (P' k).denU C')
    (g : Graph) : (g.toComp P).denU C ≤ (g.toComp P').denU C' := by
  have hS : (fun k => sigOf (P k)) = fun k => sigOf (P' k) := funext hs
  rw [denU_toComp, denU_toComp, hS]
  exact sem_mono _ g hle

/-- **Equivalent packages give equivalent compositions** (same interfaces). -/
theorem toComp_congr {C C' : CoreSem M} {P P' : Nat → Comp M}
    (hs : ∀ k, sigOf (P k) = sigOf (P' k)) (heq : ∀ k, (P k).denU C = (P' k).denU C')
    (g : Graph) : (g.toComp P).denU C = (g.toComp P').denU C' :=
  le_antisymm (toComp_mono hs (fun k => (heq k).le) g)
    (toComp_mono (fun k => (hs k).symm) (fun k => (heq k).ge) g)

/-- The flattening of a composition (the flat IR) has the meaning of the composition. -/
theorem denU_flatten_toComp (C : CoreSem M) (P : Nat → Comp M) (g : Graph) :
    (flatten (g.toComp P)).denU C = g.sem (fun k => sigOf (P k)) (fun k => (P k).denU C) := by
  rw [denU_flatten', denU_toComp]

end Silmaril.Wasm.Wac

module

public import Silmaril.Wasm.Wac.Unused.Defs
public import Silmaril.Proofs.Wasm.Wac.Unused.Main
public import Silmaril.Wasm.Component.Algebra.Plug.Defs
public import Silmaril.Wasm.Component.Algebra.Ops.Thms

/-!
# WAC: unused imports are promotion (theorems)

* **`buildWith_sub_equiv`**: a composition graph built over the imports `I` is equivalent, for
  every core semantics, to the same graph built over any `J` that contains every import the
  graph refers to (`Graph.RefsIn`) with the same types as in `I`, re-imported into `I` by name:
  `reimport I (byName I J) (g.buildWith S P J)`. The imports of `I` outside `J` are promoted
  and unused;
* **`toComp_unused`**: the same for `Graph.toComp`, whose imports are `g.iface`, declared
  unused imports included.

So a WAC composition that declares imports it does not use is the algebra term
`reimport I (byName I J) t`, where `t` is the term of the composition over the imports it uses.
Proof: `Silmaril.Proofs.Wasm.Wac.Unused.Main` (`flatten_buildWith_sub`: the flat components are
equal up to the specialisation by `importPerm I J`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra UnusedProof

variable {M : Type}

theorem importPerm_eq_byName (I J : Iface) : importPerm I J = (byName I J).map Impl.fwd := by
  simp [importPerm, byName, names, Function.comp_def]

variable [CoreModule M]

/-- **Unused imports are promotion**: a graph built over `I` is the graph built over the
imports `J` it refers to, re-imported into `I` by name. -/
theorem buildWith_sub_equiv (C : CoreSem M) (P : Nat → Comp M) (g : Graph) {I J : Iface}
    (hl : ∀ x ∈ names J, I.lookup x = J.lookup x)
    (hr : g.RefsIn (fun k => sigOf (P k)) (names J)) :
    CompEquiv C (g.buildWith (fun k => sigOf (P k)) P I)
      (reimport I (byName I J) (g.buildWith (fun k => sigOf (P k)) P J)) := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp [Graph.buildWith, reimport, wrap, length_reexport, Graph.mkExports]
  · rw [← denU_flatten' C, flatten_buildWith_sub P g hl hr,
      denU_specialise' C I (scoped_importPerm hl) _
        (by simp [Graph.buildWith, length_importPerm]),
      denU_reimport, importPerm_eq_byName]

/-- **Unused imports of a composition are promotion**: `Graph.toComp` (imports `g.iface`,
declared unused imports included) is the composition over the imports `J` it refers to,
re-imported by name. -/
theorem toComp_unused (C : CoreSem M) (P : Nat → Comp M) (g : Graph) {J : Iface}
    (hl : ∀ x ∈ names J, (g.iface fun k => sigOf (P k)).lookup x = J.lookup x)
    (hr : g.RefsIn (fun k => sigOf (P k)) (names J)) :
    CompEquiv C (g.toComp P)
      (reimport (g.iface fun k => sigOf (P k))
        (byName (g.iface fun k => sigOf (P k)) J) (g.buildWith (fun k => sigOf (P k)) P J)) :=
  buildWith_sub_equiv C P g hl hr

end Silmaril.Wasm.Wac

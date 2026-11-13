module

public import Silmaril.Wasm.Component.BinaryP3.World.Defs

/-!
# Component Model subtyping on closed types

`CSub a b` (`a` is usable where `b` is expected) is the subtyping relation of the Component
Model explainer (`design/mvp/Explainer.md`, "Type checking", at `d095e2f`): type equality,
relaxed for instance and component types only:

> Currently, subtyping is only relaxed for `module`, `instance` and `component` types […].
> Module, component and instance subtyping allows a subtype to export more and import less than
> is declared by the supertype, ignoring the exact order of imports and exports and considering
> only names.

On `World.CType`:

* `refl`: every type is a subtype of itself (type equality; value, function, resource and type
  export types are compared this way, as in the explainer);
* `inst`: `a` exports every name `b` exports, at a subtype (**width and depth**);
* `comp`: every import of `a` is imported by `b` at a subtype (contravariant: `b`'s import is
  usable where `a`'s is expected), and every export of `b` is exported by `a` at a subtype.

Core module types are opaque in `CType` (`coreModule`), so their subtyping (also relaxed in the
explainer) is not visible here: two core module types are related only by `refl`.

`Silmaril.Wasm.Component.BinaryP3.WorldSub.Thms` proves `World.sub`, `World.provides` and
`World.targets` sound for `CSub`, `CSub` reflexive and transitive, and `World.sub` incomplete
(it has no depth subtyping).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3.World

/-- **Component Model subtyping** on closed types (see the module documentation). The premises
of `inst` and `comp` say "every name of the one is a name of the other" and "at a subtype"
separately, so that `CSub` occurs only strictly positively. -/
inductive CSub : CType → CType → Prop
  | refl (a : CType) : CSub a a
  | inst {as bs : CFields} :
      (∀ n tb, (n, tb) ∈ bs.toList → (as.toList.lookup n).isSome) →
      (∀ n tb ta, (n, tb) ∈ bs.toList → as.toList.lookup n = some ta → CSub ta tb) →
      CSub (.inst as) (.inst bs)
  | comp {ai ae bi be : CFields} :
      (∀ n ta, (n, ta) ∈ ai.toList → (bi.toList.lookup n).isSome) →
      (∀ n ta tb, (n, ta) ∈ ai.toList → bi.toList.lookup n = some tb → CSub tb ta) →
      (∀ n tb, (n, tb) ∈ be.toList → (ae.toList.lookup n).isSome) →
      (∀ n tb ta, (n, tb) ∈ be.toList → ae.toList.lookup n = some ta → CSub ta tb) →
      CSub (.comp ai ae) (.comp bi be)

/-- Every entry of `need` is provided by `have_` at a subtype (`CSub`). -/
def Provides (have_ need : Table) : Prop :=
  ∀ n t, (n, t) ∈ need → ∃ t', have_.lookup n = some t' ∧ CSub t' t

end Silmaril.Wasm.Component.BinaryP3.World

end

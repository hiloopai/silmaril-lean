module

public import Silmaril.Wasm.Component.Semantics.Defs

/-!
# The component algebra: equivalence and refinement of components

Three notions of sameness of two components `c c' : Comp M`, all relative to a semantics
of core modules `C : CoreSem M` (the meaning of a core module is a parameter of the
component semantics, see `Silmaril.Wasm.Component.Semantics`):

* `SameSizes c c'`: the same number of imports and of exports;
* `CompEquiv C c c'` (*denotational equivalence*): same sizes, and the same strategy
  `Comp.denU` over the unbounded signature `sigU`;
* `IfaceEquiv C c c'` (*behavioural equivalence at the interface*): same sizes, and the
  same strategy at the interface, `atSizes n k (Comp.denU C ·)` for the shared sizes
  `n`, `k` (this is `Comp.den` up to the identification of `c.imports.sig` with
  `sigN c.imports.length`).

`CompRefines` and `IfaceRefines` are the refinement (play inclusion) versions. The
theorems (`Silmaril.Wasm.Component.Algebra.Equiv.Thms`) prove that the interface notions
and the denotational notions coincide (`ifaceEquiv_iff`, `ifaceRefines_iff`): a component
traps on every call outside its interface, so its behaviour at the interface determines
its strategy over `sigU`. Contextual equivalence is defined over terms of the algebra in
`Silmaril.Wasm.Component.Algebra.Term`.

`ParEquiv c c'` (*parametric equivalence*) is `CompEquiv C c c'` for every `C`: the
equivalence of two components that holds whatever their core modules compute.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component

variable {M : Type}

/-- The same number of imports and of exports. -/
def SameSizes (c c' : Comp M) : Prop :=
  c.imports.length = c'.imports.length ∧ c.exports.length = c'.exports.length

variable [CoreModule M]

/-- **Denotational equivalence** of components: same sizes, same strategy. -/
def CompEquiv (C : CoreSem M) (c c' : Comp M) : Prop :=
  SameSizes c c' ∧ c.denU C = c'.denU C

/-- **Refinement** of components: same sizes, every play of `c` is a play of `c'`. -/
def CompRefines (C : CoreSem M) (c c' : Comp M) : Prop :=
  SameSizes c c' ∧ c.denU C ≤ c'.denU C

/-- The strategy of a component at given interface sizes. -/
def atIface (C : CoreSem M) (n k : Nat) (c : Comp M) : Strategy (sigN n) (sigN k) :=
  atSizes n k (c.denU C)

/-- **Behavioural equivalence at the interface**: same sizes, and the same strategy
between the `n` imports and the `k` exports. -/
def IfaceEquiv (C : CoreSem M) (c c' : Comp M) : Prop :=
  SameSizes c c' ∧ atIface C c.imports.length c.exports.length c =
    atIface C c.imports.length c.exports.length c'

/-- Refinement at the interface. -/
def IfaceRefines (C : CoreSem M) (c c' : Comp M) : Prop :=
  SameSizes c c' ∧ atIface C c.imports.length c.exports.length c ≤
    atIface C c.imports.length c.exports.length c'

/-- **Parametric equivalence**: equivalence for every semantics of core modules. -/
def ParEquiv (c c' : Comp M) : Prop := ∀ C : CoreSem M, CompEquiv C c c'

end Silmaril.Wasm.Component.Algebra

module

public import Silmaril.Wasm.Component.Algebra.Ops.Defs

/-!
# Contextual equivalence through closed contexts: definitions

A **closed context** is a term `Tm.mk [] ns xs` of the component algebra: a whole program with
no imports, whose holes (variables) are instances of the component under test. Plugging `c`
into a closed context gives a closed component, observed at its exports only
(`atIface C 0 k`: the lower interface `sigN 0` has no operation).

* `Tm.Closed t`: `t` is a closed context.
* `ClosedCtxEquiv C c c'`: no closed context distinguishes `c` from `c'` at its exports;
  `ClosedCtxRefines` is the refinement version.
* `closeTm k`: the closed context `Tm.mk [] [.inst (.var 0) []] …` that instantiates its hole
  with every import trapping and re-exports its `k` exports.

Theorems in `Silmaril.Wasm.Component.Algebra.Closed.Thms`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Wasm.Component

variable {M : Type}

/-- A term with no imports: a context in which the result is a whole program. -/
def Tm.Closed : Tm M → Prop
  | .var _ => False
  | .mk I _ _ => I = []

/-- An export forwarding to nothing yet (`reexport` sets its implementation). -/
def blankExport : Export := ⟨"", ⟨[], []⟩, Impl.trap⟩

/-- The closing context: one instance of the hole, all of its imports trapping, its `k`
exports re-exported. -/
def closeTm (k : Nat) : Tm M := .mk [] [.inst (.var 0) []] (reexport 0 (List.replicate k blankExport))

variable [CoreModule M]

/-- **Closed-context equivalence**: no closed context distinguishes `c` from `c'`. -/
def ClosedCtxEquiv (C : CoreSem M) (c c' : Comp M) : Prop :=
  ∀ t : Tm M, t.Closed → IfaceEquiv C (t.eval fun _ => c) (t.eval fun _ => c')

/-- **Closed-context refinement.** -/
def ClosedCtxRefines (C : CoreSem M) (c c' : Comp M) : Prop :=
  ∀ t : Tm M, t.Closed → IfaceRefines C (t.eval fun _ => c) (t.eval fun _ => c')

end Silmaril.Wasm.Component.Algebra

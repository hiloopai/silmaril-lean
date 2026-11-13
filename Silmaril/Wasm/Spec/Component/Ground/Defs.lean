module

public import Silmaril.Wasm.Spec.Component.IR.Defs
public import Silmaril.Wasm.Spec.Component.Ref.Defs
public import Silmaril.Wasm.Spec.Component.Logic.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs

@[expose] public section

/-!
# Grounding component specifications in the reference semantics: definitions

For *simple* components (`Reference.Simple`: one instance of an import-free numeric Core 3.0
module, exports `canon lift`ed at scalar/record/variant types; the fragment of the IR soundness
link in `Silmaril.Wasm.Component.Reference.Sound`), the three readings of an export call:

* the IR program `Simple.irProg c` (the component `c.toComp`, at its interface
  `cface c.toComp`), in `irSem (modSem P)`;
* the canonical-ABI specification `exportSpec P c x vs` (Core 3.0 `Steps P` of the core export
  between `checkLower` and `liftArgs`);
* the reference program `Simple.refProg P c` (the reference component `c.toRef` over
  `core3P P`), in `refSem prof (refHost P) ()`.

`Terminates b`: the outcome is observable by the IR (a returned value list or a trap).
`Simple.RefSound P prof c`: the reference-machine half of the IR soundness proof for `c` (every
reference behaviour of a well-typed call is a specification outcome). It holds for every
component within the flat arities (`Simple.refSound_of_arity`, from the proved
`Reference.refToSpec_of_arity`). Theorems in
`Silmaril.Wasm.Spec.Component.Ground.Thms`.
-/

namespace Silmaril.Wasm.Spec.Component

open Silmaril.Wasm.Component (ValTy)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-- A reference outcome that the IR can observe: a returned value list or a trap. -/
def Terminates : Outcome → Prop
  | .returns (some _) => True
  | .traps => True
  | _ => False

namespace Simple

/-- The IR program of a simple component. -/
def irProg (c : Simple) : IRProg NumModule (cface c.toComp) := IRProg.ofComp c.toComp

/-- The export of the interface of `c.toComp` for export `j` of `c`. -/
def expIdx (c : Simple) (j : Fin c.exports.length) : (cface c.toComp).Exp :=
  ⟨j, by simp [cface, Simple.toComp]⟩

/-- The reference program of a simple component over `core3P P`. -/
noncomputable def refProg (P : Profile) (c : Simple) : RefProg (core3P P) (cface c.toComp) where
  comp := c.toRef
  args := []
  names j := (c.exports[j.1]'(by simpa [cface, Simple.toComp] using j.2)).name

/-- The reference-machine half of IR soundness for one component: every reference behaviour of
a well-typed export call is an outcome of the canonical-ABI specification. -/
def RefSound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) : Prop :=
  ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
    exportBehaviours prof (refHost P) () c.toRef [] x.name (vs.map toRefVal) ⊆ exportSpec P c x vs

/-- The precondition of the reference contract: the arguments are reference images of IR values
of the parameter types satisfying `pre`. -/
def refPre (c : Simple) (j : Fin c.exports.length) (pre : List RVal → Prop) (a : List RVal) :
    Prop :=
  ∃ vs, a = vs.map toRefVal ∧ ValTy.checkList c.exports[j].ty.params vs = true ∧ pre a

end Simple

end Silmaril.Wasm.Spec.Component

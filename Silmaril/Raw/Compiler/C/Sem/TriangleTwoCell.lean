module

public import Silmaril.Compiler.C.Sem.Triangle.Defs
public import Silmaril.Compiler.Category.TwoCell.Defs
@[expose] public section

/-!
# The Ail → Core → Mir triangle as 2-cells

The triangle `Core.cAC_comp_cCM` (`cAC S ≫ cCM cfg ctl = cAM S cfg ctl`) as a pair of 2-cells
of `Silmaril.Compile.Category.TwoCell`, and the factorization of `Silmaril.Compile.C.Sem.Triangle`
restated in the 2-cell API:

* `triangle : cAM ⟹ cAC ≫ cCM` and `triangleInv : cAC ≫ cCM ⟹ cAM`;
* `factorsVia`: if an elaboration preserves `S` on `F`, every valid direct lowering Ail → Mir
  factors through it (`factor'` is `C.Sem.factor`, re-derived);
* `valid_iff'`: `C.Sem.valid_iff` from `Factors.valid_iff` and the two 2-cells;
* `coreRoute`: a pass Ail → Core and a pass Core → Mir give a pass Ail → Mir at `cAM`, the one
  2-cell `triangleInv` being the whole cost of the route;
* `cAM_rigid`: every read-back convention with a 2-cell into `cAM` is `cAM` (read-back
  rigidity), so the triangle is the only 2-cell between read-back routes.
-/

namespace Silmaril.Compile.C.Sem

open Silmaril.Compile.Category Silmaril.Compile.Core
open CategoryTheory

variable (S : Semantics) (cfg : Mir.Config) (ctl : Nat)

/-- The triangle, from the direct convention to the Core route. -/
def triangle : cAM S cfg ctl ⟹ cAC S ≫ cCM cfg ctl := TwoCell.ofEq (cAC_comp_cCM S cfg ctl).symm

/-- The triangle, from the Core route to the direct convention. -/
def triangleInv : cAC S ≫ cCM cfg ctl ⟹ cAM S cfg ctl := TwoCell.ofEq (cAC_comp_cCM S cfg ctl)

variable {S}

/-- If the elaboration preserves `S` on `F`, the Core route captures every valid direct
lowering of a program of `F`. -/
theorem factorsVia {F : Set Silmaril.Cerberus.Ail.TypedProgram}
    {elaborate : Silmaril.Cerberus.Ail.TypedProgram → Silmaril.Cerberus.Core.Dynamics.Program}
    (h : ∀ p ∈ F, Core.beh (elaborate p) = S p) :
    FactorsVia (cAM S cfg ctl) (cAC S) (cCM cfg ctl) F elaborate :=
  (realises_of_beh h).factorsVia (triangle S cfg ctl)

/-- `C.Sem.factor`, re-derived from the 2-cell API. -/
theorem factor' {F : Set Silmaril.Cerberus.Ail.TypedProgram}
    {elaborate : Silmaril.Cerberus.Ail.TypedProgram → Silmaril.Cerberus.Core.Dynamics.Program}
    (h : ∀ p ∈ F, Core.beh (elaborate p) = S p) {p : Silmaril.Cerberus.Ail.TypedProgram}
    (hp : p ∈ F) {m : Array Mir.Unit} (hv : Valid (cAM S cfg ctl) p m) :
    Valid (cAC S) p (elaborate p) ∧ Valid (cCM cfg ctl) (elaborate p) m :=
  factorsVia cfg ctl h p hp m hv

/-- `C.Sem.valid_iff`, re-derived from the 2-cell API. -/
theorem valid_iff' {F : Set Silmaril.Cerberus.Ail.TypedProgram}
    {elaborate : Silmaril.Cerberus.Ail.TypedProgram → Silmaril.Cerberus.Core.Dynamics.Program}
    (h : ∀ p ∈ F, Core.beh (elaborate p) = S p) {p : Silmaril.Cerberus.Ail.TypedProgram}
    (hp : p ∈ F) (m : Array Mir.Unit) :
    Relation.Comp (Valid (cAC S)) (Valid (cCM cfg ctl)) p m ↔ Valid (cAM S cfg ctl) p m :=
  (factorsVia cfg ctl h).factors.valid_iff (triangleInv S cfg ctl) hp m

/-- **The Core route as a direct pass.** An elaboration pass Ail → Core and a lowering pass
Core → Mir, each with its own local soundness, give a pass at the direct convention `cAM`. -/
def coreRoute (P : Pass (cAC S)) (Q : Pass (cCM cfg ctl)) : Pass (cAM S cfg ctl) :=
  P.route Q (triangleInv S cfg ctl)

/-- Read-back rigidity at `cAM`: a read-back convention with a 2-cell into `cAM` is `cAM`. -/
theorem cAM_rigid {a : cSyntax.lang S ⟶ Mir.lang cfg} (ha : Convention.ReadBack a)
    (α : a ⟹ cAM S cfg ctl) : a = cAM S cfg ctl :=
  ha.eq_of_twoCell (cAM_readBack S cfg ctl) α

/-- The Core route is a read-back route: its composite reads back like `cAM`. -/
def coreRoute_readBack : Convention.ReadBack (cAC S ≫ cCM cfg ctl) :=
  (cAC_readBack S).comp (cCM_readBack cfg ctl)

end Silmaril.Compile.C.Sem

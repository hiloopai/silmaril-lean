module

public import Silmaril.Wasm.Game.Linking.Defs
public import Silmaril.Wasm.Game.DivAdequacy.Defs
public import Silmaril.Games.Category.Defs
public import Silmaril.Games.DivComp.Thms
public import Mathlib.CategoryTheory.PathCategory.Basic

@[expose] public section

/-!
# The semantic functor of scalar instances into the category of games

Scalar instances form a quiver `WObj`: objects are scalar function interfaces, an arrow
`ts ⟶ ts'` is an instance importing `ts` and exporting `ts'` (its export addresses and its
store). Its free category `Paths WObj` has *formal* composites: a path `a₁ ≫ a₂` is the
instance `a₁` supplying the imports of `a₂`.

* `sem P : Paths WObj ⥤ Sig.{0}`, the **semantic functor** into `Silmaril.Games`' category of
  signatures and strategies, sends an instance to its strategy `I.σ P` (relational, every
  profile `P`) and a path to the composite of the strategies.
* `dsem P : Paths WObj ⥤ DSig.{0}`, its divergence-observing version (`I.dstrategy P I.store`
  into the category of divergence-observing strategies).
* The arrows of a static link (`Silmaril.Wasm.Game.Linking.Setup`, silmaril-lean's `link?` on the
  `Recipe.Assembly` fragment): the provider `provArrow S`, the consumer `consArrow S` (its
  imports bound to stubs of the provider's exports) and the linked module `linkArrow S`.

`Silmaril.Wasm.Category.Linking.Thms` proves that `sem P` identifies the formal composite
`provArrow S ≫ consArrow S` with the linked module (M3), and that forgetting divergence maps
`dsem P` to `sem P`.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

/-- Objects of the instance quiver: scalar function interfaces. -/
structure WObj where of ::
  /-- The function types of the interface. -/
  ts : List FnType

/-- An arrow `X ⟶ Y` of the instance quiver: an instance importing `X` and exporting `Y`. -/
structure WArrow (X Y : WObj) where
  /-- The export addresses. -/
  addrs : List Nat
  /-- The store after instantiation. -/
  store : Store Nat

/-- The instance of an arrow. -/
def WArrow.inst {X Y : WObj} (a : WArrow X Y) : ScalarInstance := ⟨X.ts, Y.ts, a.addrs, a.store⟩

instance : Quiver WObj := ⟨WArrow⟩

/-- An arrow as a morphism (a path of length one) of the free category. -/
def WArrow.path {X Y : WObj} (a : WArrow X Y) :
    (Paths.of WObj).obj X ⟶ (Paths.of WObj).obj Y :=
  (Paths.of WObj).map a

/-- An arrow from an instance. -/
def WArrow.ofInst (I : ScalarInstance) : WArrow (.of I.imports) (.of I.exports) :=
  ⟨I.addrs, I.store⟩

theorem WArrow.ofInst_inst (I : ScalarInstance) : (WArrow.ofInst I).inst = I := rfl

/-- The semantic prefunctor: an instance denotes its strategy. -/
noncomputable def semPre (P : Profile) : WObj ⥤q Sig.{0} where
  obj X := ifaceSig X.ts
  map a := a.inst.σ P

/-- **The semantic functor** from the free category on instances into the category of games. -/
noncomputable def sem (P : Profile) : Paths WObj ⥤ Sig.{0} := Paths.lift (semPre P)

/-- The divergence-observing semantic prefunctor. -/
noncomputable def dsemPre (P : Profile) : WObj ⥤q DSig.{0} where
  obj X := ifaceSig X.ts
  map a := a.inst.dstrategy P a.inst.store

/-- **The divergence-observing semantic functor.** -/
noncomputable def dsem (P : Profile) : Paths WObj ⥤ DSig.{0} := Paths.lift (dsemPre P)

/-- Forgetting divergence, as a functor `DSig ⥤ Sig`. -/
def forgetDiv : DSig.{0} ⥤ Sig.{0} where
  obj E := E
  map δ := DStrategy.forget δ
  map_id _ := rfl
  map_comp σ τ := DStrategy.forget_comp σ τ

namespace Linking.Setup

variable (S : Linking.Setup)

/-- The provider of a static link, as an arrow. -/
def provArrow : WArrow (.of []) (.of S.stubTypes) := WArrow.ofInst S.providerI

/-- The consumer of a static link, as an arrow. -/
def consArrow : WArrow (.of S.stubTypes) (.of S.exportTypes) := WArrow.ofInst S.consumerI

/-- The linked module, as an arrow. -/
def linkArrow : WArrow (.of []) (.of S.exportTypes) := WArrow.ofInst S.linkedI

end Linking.Setup

end Silmaril.Wasm.Category

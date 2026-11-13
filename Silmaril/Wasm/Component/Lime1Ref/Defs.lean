module

public import Silmaril.Wasm.Component.Lime1G.Defs
public import Silmaril.Wasm.Models.Lime1Core.Defs

/-!
# The reference-machine half for the Lime1 engine: statements

`RefToSpec lime1G` (`docs/projects/spectec/README.md` §S.3) asks that every behaviour of the reference
component machine over the Lime1 engine `Silmaril.Wasm.Component.Engine.Lime1.lime1` be an
outcome of the Core 3.0 canonical-ABI specification `exportSpec P`. This module states it
precisely and splits it into two halves.

**The statement needs two corrections.**

* *A domain.* The Lime1 engine runs the Lime1 decoding `ofCoreL m` of a Core module `m`, which
  is the empty Lime1 module when `m` is not Lime1 syntax (`Lime1G.lime1Emb`). A simple component
  in the fragment of `RefToSpec` whose Core module uses a feature outside Lime1 (for example a
  tail call) has a Core 3.0 instance and so a non-empty specification, while over `lime1` its
  core instance has no exports and the reference machine traps during instantiation. The same
  holds for a Lime1 module that the Lime1 validator rejects. So the statement is over
  `Lime1Dom`: the Core module decodes to a valid Lime1 module. (This counterexample is not
  formalised here; see `docs/projects/wasm-components.md`, "Port: lime1ref".)
* *A profile.* Lime1 execution may return any NaN payload of the specification's result sets
  and may fail any `memory.grow`. The Lime1 → Core simulation is therefore stated at
  `Profile.spec`, and so is the target. At a deterministic profile the target is expected to be
  false (a Lime1 run can observe a non-canonical NaN through `i32.reinterpret_f32`, or a grow
  failure the oracle does not pick); this is not formalised either.

**The split.** `RefToSpecOn E ofCore P D` is `RefToSpec E ofCore P` on the components
satisfying `D`. It follows from

* `RefToSpecEOn E ofCore emb D`: the reference-machine half against the engine's *own*
  specification `exportSpecE E emb` (a statement about the component machine over `E` only);
* `SpecSubOn E emb P D`: the engine's specification is contained in the Core 3.0 specification
  `exportSpec P` (a statement about core runs only: no component machine).

For Lime1 the targets are the frozen statements

* `RefToSpecLime1`: `RefToSpecOn lime1 ofCoreL Profile.spec Lime1Dom` (the corrected
  `RefToSpec lime1G`);
* `RefToSpecELime1`: its machine half `RefToSpecEOn lime1 ofCoreL lime1G.emb Lime1Dom`.

The engine-run half `SpecSubOn lime1 lime1G.emb Profile.spec Lime1Dom` is proved in
`Silmaril.Wasm.Component.Lime1Bridge` (`specSub_of_instBridgeE`, from the store-level bridge
`Lime1Bridge.InstBridgeE`), and `refToSpecOn_of_specE` (`Thms`) combines the two halves.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)

/-- The Lime1 module of a Core 3.0 module: its canonical decoding, and the empty Lime1 module
off the decoder's domain. `Lime1G.lime1G.emb m` is `ofCoreL m.mod`. -/
def ofCoreL (m : Silmaril.Wasm.Module) : Silmaril.Wasm.Lime1.Module :=
  (Silmaril.Wasm.Lime1.Module.ofCore? m).getD Lime1G.emptyL

/-- **The Lime1 domain**: the Core module of `c` decodes to a Lime1 module that the Lime1
validator accepts. -/
def Lime1Dom (c : Simple) : Prop :=
  ∃ l, Silmaril.Wasm.Lime1.Module.ofCore? c.mod.mod = some l ∧
    Silmaril.Wasm.Lime1.Validation.ModuleValid l

/-- The Lime1 host without host functions. -/
def noHostL {H : Type} : Silmaril.Wasm.Models.V10.LHost H := fun _ _ _ _ => False

section Generic

variable (E : Engine) [∀ a b, Decidable (E.ExternSub a b)]
  (ofCore : Silmaril.Wasm.Module → E.Module) (emb : NumModule → E.Module) (P : Profile)
  (D : Simple → Prop)

/-- **The reference-machine half on a domain** `D`: `RefToSpec E ofCore P` for the components
satisfying `D`. -/
def RefToSpecOn : Prop :=
  ∀ (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple), D c → c.Good → c.FloatFree →
    c.Inst → c.Arity → ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      exportBehaviours prof (refHostE E) () (c.toRef.map ofCore) [] x.name (vs.map toRefVal) ⊆
        exportSpec P c x vs

/-- The reference-machine half against the engine's own specification (`RefToSpecE`), on a
domain `D`. -/
def RefToSpecEOn : Prop :=
  ∀ (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple), D c → c.Good → c.FloatFree →
    c.Inst → c.Arity → ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      exportBehaviours prof (refHostE E) () (c.toRef.map ofCore) [] x.name (vs.map toRefVal) ⊆
        exportSpecE E emb c x vs

/-- **The engine-run half**: on the domain `D`, the canonical-ABI specification over the engine
is contained in the Core 3.0 specification at profile `P`. -/
def SpecSubOn : Prop :=
  ∀ c : Simple, D c → c.Good → c.Inst → ∀ x ∈ c.exports, ∀ vs,
    exportSpecE E emb c x vs ⊆ exportSpec P c x vs

end Generic

/-! ## The Lime1 targets -/

/-- **`RefToSpec lime1G`, corrected** (proved: `Lime1Eng.refToSpec_lime1`): on the Lime1 domain, every behaviour of the
reference machine over the Lime1 engine is an outcome of the Core 3.0 specification at
`Profile.spec`. -/
def RefToSpecLime1 : Prop :=
  RefToSpecOn lime1 ofCoreL Profile.spec Lime1Dom

/-- **The machine half for Lime1** (proved: `Lime1Eng.refToSpecE_lime1`): on the Lime1 domain, every behaviour of the
reference machine over the Lime1 engine is an outcome of the Lime1 engine's own specification. -/
def RefToSpecELime1 : Prop :=
  RefToSpecEOn lime1 ofCoreL Lime1G.lime1G.emb Lime1Dom

end Silmaril.Wasm.Component.Lime1Ref

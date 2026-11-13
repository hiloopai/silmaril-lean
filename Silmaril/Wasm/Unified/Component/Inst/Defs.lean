module

public import Silmaril.Wasm.Unified.Component.Core.Thms
public import Silmaril.Wasm.Unified.Component.Feat.Defs

/-!
# The unified component institution and the comorphism from the core

The unified core institution (`Silmaril.Wasm.Unified.inst`) lifted to the Component Model.

* **Signatures** `CSig := FSig × CMSig`: a core feature signature (the opcodes core modules may
  use) and a Component Model feature signature (adapter kinds and resource types,
  `Silmaril.Wasm.Unified.Component.Feat`). Morphisms are pairs: an opcode renaming and an inclusion
  of CM feature sets (the product category).
* **Models** of `(S, K)`: unified models of `S` with payload inputs and answer observations
  (`PModel S`), i.e. interpretations of the opcodes of `S`; a model of the component layer
  *is* an interpretation of the core, and components get their meaning from it through
  `coreSem` and `Silmaril.Wasm.Component`'s denotation (`Comp.denU`). Reducts are the core reducts
  along the opcode renaming; the CM features add no model structure.
* **Sentences** `CSen (S, K)`:
  * `beh φ`: an Atlas behaviour sentence (`BSen`: `always`, `may`, `and`, `top`) over calls
    `(x, j, p)` of a program `x` (a core module or a component over `S`-modules using only
    adapters in `K`), export `j` and payload `p`, observing answers (`obs`);
  * `res x d r`: the strategy of `x`, read as handle events of a resource type `d` declared in
    `K` (`resEv d`), follows the handle protocol in role `r`
    (`Silmaril.Wasm.Resource.handleProto`): every play is accepted;
  * conjunctions.
  Translation renames the opcodes of the programs and includes the CM features.
* `sat_map_iff`: **the satisfaction condition** (from `obs_reduct` and `den_reduct`).
* `cinstitution : CSig ⥤ Room`, `cinst : Inst`.

## The comorphism from the core

`toComp : Inst.CoHom (Unified.inst Payload (Option Payload)) cinst`: a signature `S` goes to
`(S, coreOnly)`; a core sentence about the call `(c, p)` goes to the same sentence about the
call of export `0` of the one-export module `UMod.single c`; a component model goes back to
itself. Its satisfaction condition is `obs_single` (a core module answers exactly with the
observations of the model). Core sentences are about the unified institution at the flat ABI
(payload inputs, answer observations); the Wasm models (`model30` and the `Versions` models,
inputs `List Val`, observations `Behaviour Val`) enter through `Model.abi`
(`Silmaril.Wasm.Unified.Component.Abi30`).
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm.Atlas Silmaril.Wasm.Resource
open Silmaril.Wasm.Component Silmaril.Wasm.Unified

/-- Signatures of the component layer: core opcodes and Component Model features. -/
abbrev CSig : Type := FSig × CMSig

/-- Programs of a signature: over its opcodes, using only its adapters. -/
abbrev CProgIn (T : CSig) : Type := {x : CProg T.1 // x.Uses T.2}

/-- Calls of a signature: a program, an export index and a payload. -/
abbrev CCall (T : CSig) : Type := CProgIn T × Nat × Payload

/-- Translate a program along a signature morphism. -/
def CProgIn.map {T T' : CSig} (f : T ⟶ T') (x : CProgIn T) : CProgIn T' :=
  ⟨x.1.map f.1, (x.2.map f.1).mono (leOfHom f.2)⟩

/-- Translate a call along a signature morphism. -/
def CCall.map {T T' : CSig} (f : T ⟶ T') (x : CCall T) : CCall T' := (x.1.map f, x.2)

/-- Sentences of the component layer. -/
inductive CSen (T : CSig) : Type where
  /-- A behaviour sentence about calls. -/
  | beh (φ : BSen (CCall T) (Option Payload))
  /-- The program follows the handle protocol of a declared resource type, in role `r`. -/
  | res (x : CProgIn T) (d : ResDecl) (hd : CMFeature.resource d ∈ T.2) (r : Role)
  /-- Conjunction. -/
  | and (φ ψ : CSen T)

/-- Sentence translation. -/
def CSen.map {T T' : CSig} (f : T ⟶ T') : CSen T → CSen T'
  | .beh φ => .beh (φ.rename (CCall.map f))
  | .res x d hd r => .res (x.map f) d (leOfHom f.2 hd) r
  | .and φ ψ => .and (CSen.map f φ) (CSen.map f ψ)

/-- **Satisfaction.** -/
def CSat {T : CSig} (M : PModel T.1) : CSen T → Prop
  | .beh φ => φ.Sat fun x => obs M (x.1.1, x.2)
  | .res x d _ r => ∀ s ∈ den M x.1, (handleProto Flat r).Accepts (s.map (resEv d))
  | .and φ ψ => CSat M φ ∧ CSat M ψ

theorem CProgIn.map_id {T : CSig} (x : CProgIn T) : x.map (𝟙 T) = x :=
  Subtype.ext (CProg.map_id x.1)

theorem CProgIn.map_comp {T T' T'' : CSig} (f : T ⟶ T') (g : T' ⟶ T'') (x : CProgIn T) :
    x.map (f ≫ g) = (x.map f).map g :=
  Subtype.ext (CProg.map_comp f.1 g.1 x.1)

theorem CSen.map_id {T : CSig} (φ : CSen T) : φ.map (𝟙 T) = φ := by
  induction φ with
  | beh φ =>
    have h : CCall.map (𝟙 T) = id := funext fun x => Prod.ext (CProgIn.map_id x.1) rfl
    rw [CSen.map, h, BSen.rename_id]
  | res x d hd r => rw [CSen.map, CProgIn.map_id]
  | and φ ψ ih₁ ih₂ => rw [CSen.map, ih₁, ih₂]

theorem CSen.map_comp {T T' T'' : CSig} (f : T ⟶ T') (g : T' ⟶ T'') (φ : CSen T) :
    φ.map (f ≫ g) = (φ.map f).map g := by
  induction φ with
  | beh φ =>
    have h : CCall.map (f ≫ g) = fun x => CCall.map g (CCall.map f x) :=
      funext fun x => Prod.ext (CProgIn.map_comp f g x.1) rfl
    rw [CSen.map, CSen.map, CSen.map, BSen.rename_rename, h]
  | res x d hd r => rw [CSen.map, CSen.map, CSen.map, CProgIn.map_comp]
  | and φ ψ ih₁ ih₂ => rw [CSen.map, CSen.map, CSen.map, ih₁, ih₂]

/-- **The satisfaction condition** of the component institution. -/
theorem sat_map_iff {T T' : CSig} (f : T ⟶ T') (M : PModel T'.1) (φ : CSen T) :
    CSat M (φ.map f) ↔ CSat (M.reduct f.1) φ := by
  induction φ with
  | beh φ =>
    have h : ∀ x : CCall T, obs M ((CCall.map f x).1.1, (CCall.map f x).2) =
        obs (M.reduct f.1) (x.1.1, x.2) := fun x => (obs_reduct f.1 M x.1.1 x.2.1 x.2.2).symm
    exact (BSen.sat_rename _ _ φ).trans (BSen.sat_congr h φ)
  | res x d hd r =>
    show (∀ s ∈ den M (x.1.map f.1), _) ↔ ∀ s ∈ den (M.reduct f.1) x.1, _
    rw [den_reduct]
  | and φ ψ ih₁ ih₂ => exact and_congr ih₁ ih₂

/-- The room of a signature. -/
def croom (T : CSig) : Room.{0, 0, 1} := ⟨CSen T, Cat.of (PModel T.1), CSat⟩

/-- The corridor of a signature morphism. -/
def ccorridor {T T' : CSig} (f : T ⟶ T') : croom T ⟶ croom T' :=
  ⟨CSen.map f, reductF f.1, fun M φ => sat_map_iff f M φ⟩

/-- **The unified component institution**, as a functor into rooms. -/
def cinstitution : CSig ⥤ Room.{0, 0, 1} where
  obj := croom
  map := ccorridor
  map_id _ := Room.hom_ext (funext fun φ => CSen.map_id φ)
    (CategoryTheory.Functor.ext (fun M => Model.reduct_id M) (fun _ _ _ => rfl))
  map_comp f g := Room.hom_ext (funext fun φ => CSen.map_comp f g φ)
    (CategoryTheory.Functor.ext (fun M => Model.reduct_comp f.1 g.1 M) (fun _ _ _ => rfl))

/-- The unified component institution, bundled. -/
def cinst : Inst.{0, 0, 0, 0, 1} := ⟨CSig, cinstitution⟩

/-! ## The comorphism from the unified core institution -/

/-- Core signatures as component signatures with no CM features. -/
def coreToCSig : FSig ⥤ CSig where
  obj S := (S, coreOnly)
  map σ := (σ, 𝟙 coreOnly)

/-- A core call as a call of export `0` of the one-export module. -/
def coreCall {S : FSig} (x : Call Payload S) : CCall (coreToCSig.obj S) :=
  (⟨.core (UMod.single x.1), CProg.uses_core _ _⟩, 0, x.2)

/-- Core sentences as component sentences. -/
def coreSen {S : FSig} (φ : Sen Payload (Option Payload) S) : CSen (coreToCSig.obj S) :=
  .beh (φ.rename coreCall)

theorem coreSen_sat {S : FSig} (M : PModel S) (φ : Sen Payload (Option Payload) S) :
    CSat (T := coreToCSig.obj S) M (coreSen φ) ↔ Sat M φ :=
  (BSen.sat_rename _ _ φ).trans
    (BSen.sat_congr (obs := fun c => obs M ((coreCall c).1.1, (coreCall c).2)) (obs' := M.obs)
      (fun x => obs_single M x.1 x.2) φ)

/-- The corridor of the comorphism at a signature. -/
def toCompCorridor (S : FSig) :
    (institution Payload (Option Payload)).obj S ⟶ cinstitution.obj (coreToCSig.obj S) :=
  ⟨coreSen, 𝟭 _, fun M φ => coreSen_sat M φ⟩

theorem coreSen_map {S S' : FSig} (σ : S ⟶ S') (φ : Sen Payload (Option Payload) S) :
    coreSen (φ.map σ) = (coreSen φ).map (coreToCSig.map σ) := by
  rw [coreSen, coreSen, CSen.map, Sen.map, BSen.rename_rename, BSen.rename_rename]
  rfl

/-- **The comorphism from the unified core institution into the component institution.** -/
def toComp : Inst.CoHom (inst Payload (Option Payload)) cinst where
  Φ := coreToCSig
  ρ :=
    { app := toCompCorridor
      naturality := fun {_ _} σ => Room.hom_ext (funext fun φ => coreSen_map σ φ)
        (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)) }

end Silmaril.Wasm.Unified.Component

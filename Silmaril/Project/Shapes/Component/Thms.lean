module

public import Silmaril.Project.Shapes.Component.Defs
public import Silmaril.Project.Core.Thms
public import Silmaril.Wasi.Host.Thms
public import Silmaril.Wasi.World.Thms
public import Silmaril.Games.Composition.Thms

/-! # Standard problem shapes: WebAssembly components (transfer lemmas)

* `WasiSat.everyHost`: the sentence with uninterpreted imports, for the client's view
  (`onExp G`), gives the guarantee over every host of the theory (`link_satP`).
* `WasiSat.of_refines`, `WasiEveryHost.of_refines`: both are inherited by refinements;
  `Refines.of_wasiSat`: a model of `agP T G` refines the loosest one, `agSpec T G`.
* `Refines.refl`, `Refines.trans`.
* `UpgradeCompatible.refl` (along the identity), `.trans` (along a composite fitting),
  `.of_refines` (a refinement at one world), `.wasiSat`: an assume–guarantee sentence of the
  earlier release holds of the later one used at the earlier world.
* `BehaviourEq.iff_refines` (refinement both ways), `.wasiSat_iff`.
* `DigestBehaviourEq.of_bytes_eq`: one format and one digest (the same bytes) give the same
  behaviour, under every denotation, once one side decodes; `.symm`, `.trans`, `.parses`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Component

open CategoryTheory Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)

variable {W W₁ W₂ W₃ : World} {S S' : Type} {T : Protocol S WEv} {G : Protocol S' WEv}

/-! ## WASI theories -/

/-- **From uninterpreted imports to every host**: a guarantee on the export events. -/
theorem WasiSat.everyHost {σ : W.Model} (h : WasiSat σ T (onExp G)) : WasiEveryHost σ T G :=
  fun _ _ hη => link_satP h hη

/-- A refinement of a model of `agP T G` is one. -/
theorem WasiSat.of_refines {σ τ : W.Model} (hle : Refines τ σ) (h : WasiSat σ T G) :
    WasiSat τ T G :=
  ag_mono hle h

/-- A refinement of a component correct over every host is correct over every host. -/
theorem WasiEveryHost.of_refines {σ τ : W.Model} (hle : Refines τ σ) (h : WasiEveryHost σ T G) :
    WasiEveryHost τ T G :=
  fun Y η hη p hp => h Y η hη p (Strategy.comp_mono_right η hle hp)

/-! ## Refinement -/

theorem Refines.refl (σ : W.Model) : Refines σ σ := le_refl σ

theorem Refines.trans {σ τ υ : W.Model} (h₁ : Refines σ τ) (h₂ : Refines τ υ) : Refines σ υ :=
  le_trans h₁ h₂

/-- **A model of the contract refines the loosest model of it.** -/
theorem Refines.of_wasiSat {σ : W.Model} (h : WasiSat σ T G) : Refines σ (agSpec T G) :=
  fun s hs => Strategy.subset_generate (h s hs) (σ.legal hs)

/-! ## Upgrades -/

/-- Every release is an upgrade of itself. -/
theorem UpgradeCompatible.refl (v : W.Model) : UpgradeCompatible (𝟙 W) v v := by
  unfold UpgradeCompatible
  rw [World.toGame.map_id]
  exact le_of_eq (Game.reduct_id (World.toGame.obj W) v)

/-- A refinement at one world is an upgrade along the identity. -/
theorem UpgradeCompatible.of_refines {v₁ v₂ : W.Model} (h : Refines v₂ v₁) :
    UpgradeCompatible (𝟙 W) v₂ v₁ := by
  unfold UpgradeCompatible
  rw [World.toGame.map_id]
  exact le_of_eq_of_le (Game.reduct_id (World.toGame.obj W) v₂) h

/-- **Upgrades compose** along the composite fitting. -/
theorem UpgradeCompatible.trans {f : W₁ ⟶ W₂} {g : W₂ ⟶ W₃} {v₁ : W₁.Model} {v₂ : W₂.Model}
    {v₃ : W₃.Model} (h₁₂ : UpgradeCompatible f v₂ v₁) (h₂₃ : UpgradeCompatible g v₃ v₂) :
    UpgradeCompatible (f ≫ g) v₃ v₁ := by
  unfold UpgradeCompatible at *
  rw [World.toGame.map_comp]
  exact le_of_eq_of_le (Game.reduct_comp (World.toGame.map f) (World.toGame.map g) v₃)
    (le_trans (Game.reduct_mono _ h₂₃) h₁₂)

/-- **Clients of the earlier release keep their guarantees**: an assume–guarantee sentence of
`v₁` holds of `v₂` used at `v₁`'s world. -/
theorem UpgradeCompatible.wasiSat {f : W₁ ⟶ W₂} {v₁ : W₁.Model} {v₂ : W₂.Model}
    (h : UpgradeCompatible f v₂ v₁) (h₁ : WasiSat v₁ T G) :
    WasiSat (Game.reduct (World.toGame.map f) v₂) T G :=
  WasiSat.of_refines h h₁

/-! ## Behavioural equality -/

theorem BehaviourEq.iff_refines {σ τ : W.Model} : BehaviourEq σ τ ↔ Refines σ τ ∧ Refines τ σ :=
  ⟨fun h => h ▸ ⟨le_refl σ, le_refl σ⟩, fun h => le_antisymm h.1 h.2⟩

theorem BehaviourEq.wasiSat_iff {σ τ : W.Model} (h : BehaviourEq σ τ) :
    WasiSat σ T G ↔ WasiSat τ T G := by
  unfold BehaviourEq at h
  rw [h]

/-- **One format, one digest**: two releases with the same bytes behave the same under every
denotation, once one of them decodes. -/
theorem DigestBehaviourEq.of_bytes_eq {V : Type} {den : V → W.Model} {X Y : Value V}
    (hf : X.format = Y.format) (hb : X.bytes = Y.bytes) (hp : X.Parses) :
    DigestBehaviourEq den X Y := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hp
  have hY : Y.parse = some v := by
    rw [← hv]
    simp only [Silmaril.Project.Value.parse, hf, hb]
  exact ⟨v, v, hv, hY, rfl⟩

/-- Two releases decoding to components with one behaviour. -/
theorem DigestBehaviourEq.of_parse {V : Type} {den : V → W.Model} {X Y : Value V} {a b : V}
    (ha : X.parse = some a) (hb : Y.parse = some b) (h : BehaviourEq (den a) (den b)) :
    DigestBehaviourEq den X Y :=
  ⟨a, b, ha, hb, h⟩

theorem DigestBehaviourEq.symm {V : Type} {den : V → W.Model} {X Y : Value V}
    (h : DigestBehaviourEq den X Y) : DigestBehaviourEq den Y X := by
  obtain ⟨a, b, ha, hb, he⟩ := h
  exact ⟨b, a, hb, ha, he.symm⟩

theorem DigestBehaviourEq.trans {V : Type} {den : V → W.Model} {X Y Z : Value V}
    (h₁ : DigestBehaviourEq den X Y) (h₂ : DigestBehaviourEq den Y Z) :
    DigestBehaviourEq den X Z := by
  obtain ⟨a, b, ha, hb, he⟩ := h₁
  obtain ⟨b', c, hb', hc, he'⟩ := h₂
  have hbb : b = b' := Option.some.inj (hb.symm.trans hb')
  subst hbb
  exact ⟨a, c, ha, hc, he.trans he'⟩

/-- A release in a behavioural equality decodes. -/
theorem DigestBehaviourEq.parses {V : Type} {den : V → W.Model} {X Y : Value V}
    (h : DigestBehaviourEq den X Y) : X.Parses ∧ Y.Parses := by
  obtain ⟨a, b, ha, hb, -⟩ := h
  exact ⟨by simp [Silmaril.Project.Value.Parses, ha], by simp [Silmaril.Project.Value.Parses, hb]⟩

end Silmaril.Project.Shapes.Component

end

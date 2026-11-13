module

public import Silmaril.Wasm.Spec.Joint.Base.Defs

@[expose] public section

/-!
# Change of base: proofs

Observation commutes with the translation of events along a change of base: reading a translated
trace through a mapped interface morphism is translating the reading (`back_mapP`), hence
`reduct_evImage`. Summary in `Silmaril.Wasm.Spec.Joint.Base.Thms`.
-/

namespace Silmaril.Wasm.Spec

open CategoryTheory

variable {Ty Ty' A A' R R' : Type}

/-- Preimages along a map conjugated by index casts. -/
theorem preimage?_cast {n m n' m' : ℕ} (f : Fin n → Fin m)
    (hn : n = n') (hm : m = m') (j : Fin m) :
    preimage? (fun i => Fin.cast hm (f (Fin.cast hn.symm i))) (Fin.cast hm j) =
      (preimage? f j).map (Fin.cast hn) := by
  subst hn hm
  show preimage? f j = (preimage? f j).map (Fin.cast rfl)
  cases preimage? f j <;> rfl

/-- Reading a translated side event through a conjugated map. -/
theorem SideEv.back_mapP_cast {n m n' m' : ℕ} (f : Fin n → Fin m)
    (hn : n = n') (hm : m = m') (α : A → A') (β : R → R') (e : SideEv A R m) :
    (SideEv.mapP (Fin.cast hm) α β e).back (fun i => Fin.cast hm (f (Fin.cast hn.symm i))) =
      (e.back f).map (SideEv.mapP (Fin.cast hn) α β) := by
  cases e with
  | ask j a =>
    simp only [SideEv.mapP, SideEv.back, preimage?_cast f hn hm, Option.map_map]
    rfl
  | ans j r =>
    simp only [SideEv.mapP, SideEv.back, preimage?_cast f hn hm, Option.map_map]
    rfl

/-- The import side of `back_mapP`. -/
theorem back_mapP_inl (τ : Ty → Ty') (α : A → A') (β : R → R') {Z X : Iface Ty} (f : Z ⟶ X)
    (e : SideEv A R X.imports.length) (t : List (Event A R X))
    (ih : back (Iface.mapHom τ f) (t.map (Event.mapP τ α β)) =
      (back f t).map (List.map (Event.mapP τ α β))) :
    back (Iface.mapHom τ f) ((Sum.inl e :: t).map (Event.mapP τ α β)) =
      (back f (.inl e :: t)).map (List.map (Event.mapP τ α β)) := by
  have he : (SideEv.mapP (Iface.impTo τ X) α β e).back (Iface.mapHom τ f).imp =
      (e.back f.imp).map (SideEv.mapP (Iface.impTo τ Z) α β) :=
    SideEv.back_mapP_cast f.imp (List.length_map τ).symm (List.length_map τ).symm α β e
  cases h : e.back f.imp with
  | none =>
    have hn : (SideEv.mapP (Iface.impTo τ X) α β e).back (Iface.mapHom τ f).imp = none := by
      rw [he, h]; rfl
    rw [back_inl_none f h, ← ih]
    exact back_inl_none (Iface.mapHom τ f) hn _
  | some e' =>
    have hs : (SideEv.mapP (Iface.impTo τ X) α β e).back (Iface.mapHom τ f).imp =
        some (SideEv.mapP (Iface.impTo τ Z) α β e') := by
      rw [he, h]; rfl
    rw [back_inl_some f h, List.map_cons]
    refine (back_inl_some (Iface.mapHom τ f) hs _).trans ?_
    rw [ih, Option.map_map, Option.map_map]
    rfl

/-- The export side of `back_mapP`. -/
theorem back_mapP_inr (τ : Ty → Ty') (α : A → A') (β : R → R') {Z X : Iface Ty} (f : Z ⟶ X)
    (e : SideEv A R X.exports.length) (t : List (Event A R X))
    (ih : back (Iface.mapHom τ f) (t.map (Event.mapP τ α β)) =
      (back f t).map (List.map (Event.mapP τ α β))) :
    back (Iface.mapHom τ f) ((Sum.inr e :: t).map (Event.mapP τ α β)) =
      (back f (.inr e :: t)).map (List.map (Event.mapP τ α β)) := by
  have he : (SideEv.mapP (Iface.expTo τ X) α β e).back (Iface.mapHom τ f).exp =
      (e.back f.exp).map (SideEv.mapP (Iface.expTo τ Z) α β) :=
    SideEv.back_mapP_cast f.exp (List.length_map τ).symm (List.length_map τ).symm α β e
  cases h : e.back f.exp with
  | none =>
    have hn : (SideEv.mapP (Iface.expTo τ X) α β e).back (Iface.mapHom τ f).exp = none := by
      rw [he, h]; rfl
    rw [back_inr_none f h]
    exact back_inr_none (Iface.mapHom τ f) hn _
  | some e' =>
    have hs : (SideEv.mapP (Iface.expTo τ X) α β e).back (Iface.mapHom τ f).exp =
        some (SideEv.mapP (Iface.expTo τ Z) α β e') := by
      rw [he, h]; rfl
    rw [back_inr_some f h, List.map_cons]
    refine (back_inr_some (Iface.mapHom τ f) hs _).trans ?_
    rw [ih, Option.map_map, Option.map_map]
    rfl

/-- **Observation commutes with change of base.** -/
theorem back_mapP (τ : Ty → Ty') (α : A → A') (β : R → R') {Z X : Iface Ty} (f : Z ⟶ X) :
    ∀ t : List (Event A R X), back (Iface.mapHom τ f) (t.map (Event.mapP τ α β)) =
      (back f t).map (List.map (Event.mapP τ α β))
  | [] => rfl
  | .inl e :: t => back_mapP_inl τ α β f e t (back_mapP τ α β f t)
  | .inr e :: t => back_mapP_inr τ α β f e t (back_mapP τ α β f t)

/-- Observed translated traces are translated observed traces. -/
theorem reduct_evImage (τ : Ty → Ty') (α : A → A') (β : R → R') {Z X : Iface Ty} (f : Z ⟶ X)
    (T : Set (List (Event A R X))) :
    reduct (Iface.mapHom τ f) (evImage τ α β T) = evImage τ α β (reduct f T) := by
  ext t
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, hb⟩
    rw [back_mapP, Option.map_eq_some_iff] at hb
    obtain ⟨v, hv, rfl⟩ := hb
    exact ⟨v, ⟨u, hu, hv⟩, rfl⟩
  · rintro ⟨v, ⟨u, hu, hv⟩, rfl⟩
    exact ⟨u.map (Event.mapP τ α β), ⟨u, hu, rfl⟩, by rw [back_mapP, hv]; rfl⟩

/-- Translation of trace sets is monotone. -/
theorem evImage_mono (τ : Ty → Ty') (α : A → A') (β : R → R') {X : Iface Ty}
    {T T' : Set (List (Event A R X))} (h : T ⊆ T') : evImage τ α β T ⊆ evImage τ α β T' :=
  Set.image_mono h

/-- Membership of a translated trace. -/
theorem map_mem_evImage (τ : Ty → Ty') (α : A → A') (β : R → R') {X : Iface Ty}
    {T : Set (List (Event A R X))} {t : List (Event A R X)} (ht : t ∈ T) :
    t.map (Event.mapP τ α β) ∈ evImage τ α β T :=
  ⟨t, ht, rfl⟩

end Silmaril.Wasm.Spec

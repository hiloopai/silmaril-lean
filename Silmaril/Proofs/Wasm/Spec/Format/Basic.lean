module

public import Silmaril.Wasm.Spec.Format.Defs

@[expose] public section

/-!
# The trace-institution format: proofs

Preimages along injective maps, observation of traces along interface morphisms (`back`), its
strict functoriality, prefix closure of observed trace sets, and the reading of satisfaction
through the observed traces of a model. Summary in `Silmaril.Wasm.Spec.Format.Thms`.
-/

namespace Silmaril.Wasm.Spec

open CategoryTheory

/-! ## Preimages -/

section Preimage

variable {n m k : ℕ}

/-- `preimage?` finds the preimage under an injective map. -/
theorem preimage?_eq_some_iff {f : Fin n → Fin m} (hf : Function.Injective f) {j : Fin m}
    {i : Fin n} : preimage? f j = some i ↔ f i = j := by
  unfold preimage?
  constructor
  · intro h
    simpa using List.find?_some h
  · intro h
    cases hp : (List.finRange n).find? (fun i => decide (f i = j)) with
    | none =>
      have hno := List.find?_eq_none.1 hp i (List.mem_finRange i)
      exact absurd h (by simpa using hno)
    | some i' =>
      have h' : f i' = j := by simpa using List.find?_some hp
      exact congrArg some (hf (h'.trans h.symm))

/-- The preimage of an image point. -/
theorem preimage?_apply {f : Fin n → Fin m} (hf : Function.Injective f) (i : Fin n) :
    preimage? f (f i) = some i :=
  (preimage?_eq_some_iff hf).2 rfl

/-- Preimages under the identity. -/
theorem preimage?_id (j : Fin n) : preimage? id j = some j :=
  preimage?_apply Function.injective_id j

/-- Preimages under a composite. -/
theorem preimage?_comp {f : Fin n → Fin m} {g : Fin m → Fin k} (hf : Function.Injective f)
    (hg : Function.Injective g) (l : Fin k) :
    preimage? (g ∘ f) l = (preimage? g l).bind (preimage? f) := by
  refine Option.ext fun i => ?_
  rw [preimage?_eq_some_iff (hg.comp hf), Option.bind_eq_some_iff]
  constructor
  · intro h
    exact ⟨f i, (preimage?_eq_some_iff hg).2 h, preimage?_apply hf i⟩
  · rintro ⟨j, hj, hi⟩
    have hj' : g j = l := (preimage?_eq_some_iff hg).1 hj
    have hi' : f i = j := (preimage?_eq_some_iff hf).1 hi
    show g (f i) = l
    rw [hi', hj']

end Preimage

/-! ## Observation of side events -/

namespace SideEv

variable {A R : Type} {n m k : ℕ}

/-- Reading through the identity keeps the event. -/
theorem back_id (e : SideEv A R n) : e.back id = some e := by
  cases e <;> simp [back, preimage?_id]

/-- Reading through a composite reads through each map in turn. -/
theorem back_comp {f : Fin n → Fin m} {g : Fin m → Fin k} (hf : Function.Injective f)
    (hg : Function.Injective g) (e : SideEv A R k) :
    e.back (g ∘ f) = (e.back g).bind (SideEv.back f) := by
  cases e with
  | ask j a =>
    simp only [back, preimage?_comp hf hg]
    cases preimage? g j <;> rfl
  | ans j r =>
    simp only [back, preimage?_comp hf hg]
    cases preimage? g j <;> rfl

end SideEv

/-! ## Observation of traces -/

variable {Ty A R : Type}

section Back

variable {Z X : Iface Ty} (f : Z ⟶ X)

theorem back_nil : back f ([] : List (Event A R X)) = some [] := rfl

theorem back_inl_some {e : SideEv A R X.imports.length} {e' : SideEv A R Z.imports.length}
    (h : e.back f.imp = some e') (t : List (Event A R X)) :
    back f (.inl e :: t) = (back f t).map (.inl e' :: ·) := by
  simp only [back, h]

theorem back_inl_none {e : SideEv A R X.imports.length} (h : e.back f.imp = none)
    (t : List (Event A R X)) : back f (.inl e :: t) = back f t := by
  simp only [back, h]

theorem back_inr_some {e : SideEv A R X.exports.length} {e' : SideEv A R Z.exports.length}
    (h : e.back f.exp = some e') (t : List (Event A R X)) :
    back f (.inr e :: t) = (back f t).map (.inr e' :: ·) := by
  simp only [back, h]

theorem back_inr_none {e : SideEv A R X.exports.length} (h : e.back f.exp = none)
    (t : List (Event A R X)) : back f (.inr e :: t) = none := by
  simp only [back, h]

end Back

/-- Reading through the identity keeps the trace. -/
theorem back_id {X : Iface Ty} : ∀ t : List (Event A R X), back (𝟙 X) t = some t
  | [] => rfl
  | .inl e :: t => by
    rw [back_inl_some (𝟙 X) (SideEv.back_id e), back_id t]
    rfl
  | .inr e :: t => by
    rw [back_inr_some (𝟙 X) (SideEv.back_id e), back_id t]
    rfl

/-- One import event, read through a composite. -/
theorem back_comp_inl {X Y Z : Iface Ty} (f : X ⟶ Y) (g : Y ⟶ Z) (e : SideEv A R Z.imports.length)
    (t : List (Event A R Z)) (ih : back (f ≫ g) t = (back g t).bind (back f)) :
    back (f ≫ g) (.inl e :: t) = (back g (.inl e :: t)).bind (back f) := by
  have he : e.back (f ≫ g).imp = (e.back g.imp).bind (SideEv.back f.imp) :=
    SideEv.back_comp f.imp_inj g.imp_inj e
  cases hg : e.back g.imp with
  | none =>
    have he' : e.back (f ≫ g).imp = none := by rw [he, hg]; rfl
    rw [back_inl_none _ he', back_inl_none _ hg, ih]
  | some e'' =>
    cases hf : e''.back f.imp with
    | none =>
      have he' : e.back (f ≫ g).imp = none := by rw [he, hg]; exact hf
      rw [back_inl_none _ he', back_inl_some _ hg, ih]
      cases back g t <;> simp [back_inl_none _ hf]
    | some e' =>
      have he' : e.back (f ≫ g).imp = some e' := by rw [he, hg]; exact hf
      rw [back_inl_some _ he', back_inl_some _ hg, ih]
      cases back g t <;> simp [back_inl_some _ hf]

/-- One export event, read through a composite. -/
theorem back_comp_inr {X Y Z : Iface Ty} (f : X ⟶ Y) (g : Y ⟶ Z) (e : SideEv A R Z.exports.length)
    (t : List (Event A R Z)) (ih : back (f ≫ g) t = (back g t).bind (back f)) :
    back (f ≫ g) (.inr e :: t) = (back g (.inr e :: t)).bind (back f) := by
  have he : e.back (f ≫ g).exp = (e.back g.exp).bind (SideEv.back f.exp) :=
    SideEv.back_comp f.exp_inj g.exp_inj e
  cases hg : e.back g.exp with
  | none =>
    have he' : e.back (f ≫ g).exp = none := by rw [he, hg]; rfl
    rw [back_inr_none _ he', back_inr_none _ hg]
    rfl
  | some e'' =>
    cases hf : e''.back f.exp with
    | none =>
      have he' : e.back (f ≫ g).exp = none := by rw [he, hg]; exact hf
      rw [back_inr_none _ he', back_inr_some _ hg]
      cases back g t <;> simp [back_inr_none _ hf]
    | some e' =>
      have he' : e.back (f ≫ g).exp = some e' := by rw [he, hg]; exact hf
      rw [back_inr_some _ he', back_inr_some _ hg, ih]
      cases back g t <;> simp [back_inr_some _ hf]

/-- **Strict functoriality of observation.** -/
theorem back_comp {X Y Z : Iface Ty} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ t : List (Event A R Z), back (f ≫ g) t = (back g t).bind (back f)
  | [] => rfl
  | .inl e :: t => back_comp_inl f g e t (back_comp f g t)
  | .inr e :: t => back_comp_inr f g e t (back_comp f g t)

/-- Observing a prefix of an observed trace: it is the observation of a prefix. -/
theorem back_prefix {Z X : Iface Ty} (f : Z ⟶ X) :
    ∀ {u : List (Event A R X)} {t s : List (Event A R Z)}, back f u = some t → s <+: t →
      ∃ u', u' <+: u ∧ back f u' = some s
  | [], t, s, h, hs => by
    have ht : t = [] := (Option.some.inj h).symm
    subst ht
    exact ⟨[], List.prefix_refl _, by rw [List.prefix_nil.1 hs]; rfl⟩
  | .inl e :: u, t, s, h, hs => by
    cases he : e.back f.imp with
    | none =>
      rw [back_inl_none f he] at h
      obtain ⟨u', hu', hb⟩ := back_prefix f h hs
      exact ⟨.inl e :: u', List.cons_prefix_cons.2 ⟨rfl, hu'⟩, by rw [back_inl_none f he]; exact hb⟩
    | some e' =>
      rw [back_inl_some f he] at h
      obtain ⟨t₀, ht₀, rfl⟩ := Option.map_eq_some_iff.1 h
      rcases s with _ | ⟨x, s₀⟩
      · exact ⟨[], List.nil_prefix, rfl⟩
      · obtain ⟨rfl, hs₀⟩ := List.cons_prefix_cons.1 hs
        obtain ⟨u', hu', hb⟩ := back_prefix f ht₀ hs₀
        refine ⟨.inl e :: u', List.cons_prefix_cons.2 ⟨rfl, hu'⟩, ?_⟩
        rw [back_inl_some f he, hb]
        rfl
  | .inr e :: u, t, s, h, hs => by
    cases he : e.back f.exp with
    | none => rw [back_inr_none f he] at h; cases h
    | some e' =>
      rw [back_inr_some f he] at h
      obtain ⟨t₀, ht₀, rfl⟩ := Option.map_eq_some_iff.1 h
      rcases s with _ | ⟨x, s₀⟩
      · exact ⟨[], List.nil_prefix, rfl⟩
      · obtain ⟨rfl, hs₀⟩ := List.cons_prefix_cons.1 hs
        obtain ⟨u', hu', hb⟩ := back_prefix f ht₀ hs₀
        refine ⟨.inr e :: u', List.cons_prefix_cons.2 ⟨rfl, hu'⟩, ?_⟩
        rw [back_inr_some f he, hb]
        rfl

/-! ## Observed trace sets -/

/-- Observing through the identity changes nothing. -/
theorem reduct_id {X : Iface Ty} (T : Set (List (Event A R X))) : reduct (𝟙 X) T = T := by
  ext t
  constructor
  · rintro ⟨u, hu, h⟩
    have hut : u = t := Option.some.inj ((back_id u).symm.trans h)
    exact hut ▸ hu
  · intro ht
    exact ⟨t, ht, back_id t⟩

/-- **Observation is strictly functorial.** -/
theorem reduct_comp {X Y Z : Iface Ty} (f : X ⟶ Y) (g : Y ⟶ Z) (T : Set (List (Event A R Z))) :
    reduct (f ≫ g) T = reduct f (reduct g T) := by
  ext t
  constructor
  · rintro ⟨u, hu, h⟩
    rw [back_comp, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, hvt⟩ := h
    exact ⟨v, ⟨u, hu, hv⟩, hvt⟩
  · rintro ⟨v, ⟨u, hu, hv⟩, hvt⟩
    refine ⟨u, hu, ?_⟩
    rw [back_comp, hv]
    exact hvt

/-- Observed trace sets of good trace sets are good. -/
theorem Good.reduct {Z X : Iface Ty} (f : Z ⟶ X) {T : Set (List (Event A R X))} (hT : Good T) :
    Good (Spec.reduct f T) where
  nil_mem := ⟨[], hT.nil_mem, rfl⟩
  of_prefix := by
    rintro s t ⟨u, hu, h⟩ hs
    obtain ⟨u', hu', hb⟩ := back_prefix f h hs
    exact ⟨u', hT.of_prefix hu hu', hb⟩

/-- Observation is monotone. -/
theorem reduct_mono {Z X : Iface Ty} (f : Z ⟶ X) {T T' : Set (List (Event A R X))}
    (h : T ⊆ T') : Spec.reduct f T ⊆ Spec.reduct f T' :=
  fun _ ⟨u, hu, hb⟩ => ⟨u, h hu, hb⟩

/-! ## Satisfaction through observed traces -/

/-- The traces of a model are good. -/
theorem Model.good {S : Semantics Ty A R} {X : Iface Ty} (M : Model S X) : Good M.traces :=
  (S.good M.prog).reduct M.obs

/-- The traces of a reduct are the observed traces. -/
theorem Model.traces_reduct (S : Semantics Ty A R) {X X' : Iface Ty} (f : X ⟶ X')
    (M : Model S X') : ((Model.reduct S f).obj M).traces = Spec.reduct f M.traces :=
  reduct_comp f M.obs _

/-- The traces of a program, as a model at its interface, are its traces. -/
theorem Model.traces_ofProg {S : Semantics Ty A R} {X : Iface Ty} (p : S.Prog X) :
    (Model.ofProg p).traces = S.traces p :=
  reduct_id _

/-- **Satisfaction is satisfaction by the observed traces of the model.** -/
theorem sat_iff (L : Logic Ty A R) (S : Semantics Ty A R) {X : Iface Ty} (M : Model S X)
    (s : Sen L X) : Sat L S M s ↔ L.Sat (Spec.reduct s.obs M.traces) s.φ := by
  unfold Sat Model.traces
  rw [reduct_comp]

/-- A program satisfies `φ` at its interface iff its traces do. -/
theorem models_iff (L : Logic Ty A R) (S : Semantics Ty A R) {X : Iface Ty} (p : S.Prog X)
    (φ : L.Fm X) : Models L S p φ ↔ L.Sat (S.traces p) φ := by
  unfold Models Sat Sen.atTop Model.ofProg
  rw [Category.id_comp, reduct_id]

end Silmaril.Wasm.Spec

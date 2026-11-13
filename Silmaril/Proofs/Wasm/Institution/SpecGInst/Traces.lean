module

public import Silmaril.Wasm.Institution.SpecGInst.Base

/-!
# The traces of a reduct of an interface game

`traces_reduct`: for an import-bijective interface morphism `f`, the traces of the `GInst` reduct
of a strategy along `specHom f` are the `Spec` observation along `f` of its traces. A move and its
image under `Game.Rel (specHom f)` are read by `back f` (`back_cons_rel`), and every observed
trace comes from such an image (`exists_rel_of_back`); the image is legal because the export map
is injective.
-/

public section

namespace Silmaril.Proofs.Wasm.Institution.SpecGInst

open CategoryTheory Silmaril.Games Silmaril.Wasm.Spec Silmaril.Wasm.Institution.GameInst
open Silmaril.Wasm.Institution.SpecGInst

variable {Ty A R : Type} {Z X : IfaceB Ty} (f : Z ⟶ X)

/-- The import map of `f` is injective. -/
theorem imp_inj : Function.Injective (BHom.hom f).imp := (BHom.hom f).imp_inj

/-- Preimages of imports. -/
theorem preimage_imp (i : X.X.Imp) : preimage? (BHom.hom f).imp i = some (BHom.inv f i) :=
  (preimage?_eq_some_iff (imp_inj f)).2 ((BHom.imp_inv f) i)

/-- **A move and its image are read by `back`.** -/
theorem back_cons_rel {a : Move (specGame A R X.X).E (specGame A R X.X).F}
    {c : Move (specGame A R Z.X).E (specGame A R Z.X).F} (h : Game.Rel (specHom f) a c)
    (u : List (Event A R X.X)) :
    back (BHom.hom f) (toEvent a :: u) = (back (BHom.hom f) u).map (toEvent c :: ·) := by
  cases h with
  | lask m =>
    have hb : (SideEv.ask m.1 m.2 : SideEv A R _).back (BHom.hom f).imp =
        some (.ask (BHom.inv f m.1) m.2) := by
      simp only [SideEv.back, preimage_imp f, Option.map_some]
    exact back_inl_some _ hb u
  | lans m n =>
    have hb : (SideEv.ans m.1 n : SideEv A R _).back (BHom.hom f).imp =
        some (.ans (BHom.inv f m.1) n) := by
      simp only [SideEv.back, preimage_imp f, Option.map_some]
    exact back_inl_some _ hb u
  | uask q =>
    obtain ⟨j, x⟩ := q
    have hb : (SideEv.ask ((BHom.hom f).exp j) x : SideEv A R _).back (BHom.hom f).exp =
        some (.ask j x) := by
      simp only [SideEv.back, preimage?_apply (BHom.hom f).exp_inj, Option.map_some]
    exact back_inr_some _ hb u
  | uans q n =>
    obtain ⟨j, x⟩ := q
    have hb : (SideEv.ans ((BHom.hom f).exp j) n : SideEv A R _).back (BHom.hom f).exp =
        some (.ans j n) := by
      simp only [SideEv.back, preimage?_apply (BHom.hom f).exp_inj, Option.map_some]
    exact back_inr_some _ hb u

/-- The image of a play is read by `back`. -/
theorem back_map_rel {s : List (Move (specGame A R X.X).E (specGame A R X.X).F)}
    {p : List (Move (specGame A R Z.X).E (specGame A R Z.X).F)}
    (h : List.Forall₂ (Game.Rel (specHom f)) s p) :
    back (BHom.hom f) (s.map toEvent) = some (p.map toEvent) := by
  induction h with
  | nil => rfl
  | cons hac _ ih => rw [List.map_cons, back_cons_rel f hac, ih]; rfl

/-- Extending an observed trace by the image of one more move. -/
theorem cons_of_rel {a : Move (specGame A R X.X).E (specGame A R X.X).F}
    {c : Move (specGame A R Z.X).E (specGame A R Z.X).F} (hac : Game.Rel (specHom f) a c)
    {s : List (Move (specGame A R X.X).E (specGame A R X.X).F)} {t : List (Event A R Z.X)}
    (h : back (BHom.hom f) ((a :: s).map toEvent) = some t)
    (ih : ∀ {t : List (Event A R Z.X)}, back (BHom.hom f) (s.map toEvent) = some t →
      ∃ p, List.Forall₂ (Game.Rel (specHom f)) s p ∧ p.map toEvent = t) :
    ∃ p, List.Forall₂ (Game.Rel (specHom f)) (a :: s) p ∧ p.map toEvent = t := by
  have h' : (back (BHom.hom f) (s.map toEvent)).map (toEvent c :: ·) = some t :=
    (back_cons_rel f hac _).symm.trans h
  obtain ⟨t', ht', hct⟩ := Option.map_eq_some_iff.1 h'
  obtain ⟨p, hp, hpt⟩ := ih ht'
  refine ⟨c :: p, .cons hac hp, ?_⟩
  rw [List.map_cons, hpt]
  exact hct

/-- An observed export event is in the image of the export map. -/
theorem inr_some {e : SideEv A R X.X.exports.length} {u : List (Event A R X.X)}
    {t : List (Event A R Z.X)} (h : back (BHom.hom f) (.inr e :: u) = some t) :
    ∃ e', e.back (BHom.hom f).exp = some e' := by
  cases he : e.back (BHom.hom f).exp with
  | none => exact absurd ((back_inr_none _ he u).symm.trans h) nofun
  | some e' => exact ⟨e', rfl⟩

/-- **Every observed trace is read from an image.** -/
theorem exists_rel_of_back :
    ∀ {s : List (Move (specGame A R X.X).E (specGame A R X.X).F)} {t : List (Event A R Z.X)},
      back (BHom.hom f) (s.map toEvent) = some t →
      ∃ p, List.Forall₂ (Game.Rel (specHom f)) s p ∧ p.map toEvent = t
  | [], t, h => ⟨[], .nil, Option.some.inj h⟩
  | a :: s, t, h => by
    have ih := fun {t : List (Event A R Z.X)} (h' : back (BHom.hom f) (s.map toEvent) = some t) =>
      exists_rel_of_back h'
    rcases a with (⟨m⟩ | ⟨m, r⟩) | (⟨⟨j', x⟩⟩ | ⟨⟨j', x⟩, r⟩)
    · exact cons_of_rel f (.lask m) h ih
    · exact cons_of_rel f (.lans (lo := sigOfHom (A := A) (R := R) (BHom.inv f))
        (up := sigOfHom (A := A) (R := R) (BHom.hom f).exp) m r) h ih
    · obtain ⟨_, he⟩ := inr_some f h
      obtain ⟨j, hj, -⟩ := Option.map_eq_some_iff.1 he
      obtain rfl : (BHom.hom f).exp j = j' := (preimage?_eq_some_iff (BHom.hom f).exp_inj).1 hj
      exact cons_of_rel f (.uask (lo := sigOfHom (A := A) (R := R) (BHom.inv f))
        (up := sigOfHom (A := A) (R := R) (BHom.hom f).exp) (j, x)) h ih
    · obtain ⟨_, he⟩ := inr_some f h
      obtain ⟨j, hj, -⟩ := Option.map_eq_some_iff.1 he
      obtain rfl : (BHom.hom f).exp j = j' := (preimage?_eq_some_iff (BHom.hom f).exp_inj).1 hj
      exact cons_of_rel f (.uans (lo := sigOfHom (A := A) (R := R) (BHom.inv f))
        (up := sigOfHom (A := A) (R := R) (BHom.hom f).exp) (j, x) r) h ih

/-- The upper renaming of `specHom f` is injective. -/
theorem up_inj : Function.Injective (specHom (A := A) (R := R) f).up.op := by
  rintro ⟨j₁, x₁⟩ ⟨j₂, x₂⟩ h
  simp only [specHom, sigOfHom] at h
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  rw [(BHom.hom f).exp_inj h₁, h₂]

/-- **The traces of the reduct are the observed traces.** -/
theorem traces_reduct (σ : (specGame A R X.X).Model) :
    stratTraces (Game.reduct (specHom f) σ) = Silmaril.Wasm.Spec.reduct (BHom.hom f) (stratTraces σ) := by
  ext t
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨-, s, hs, hr⟩ := (Game.mem_reduct_iff_rel _ σ p).1 hp
    exact ⟨s.map toEvent, ⟨s, hs, rfl⟩, back_map_rel f hr⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, hb⟩
    obtain ⟨p, hr, rfl⟩ := exists_rel_of_back f hb
    have hl : Legal p := Game.legal_of_rel_inj _ (up_inj f) hr (σ.legal hs)
    exact ⟨p, (Game.mem_reduct_iff_rel _ σ p).2 ⟨hl, s, hs, hr⟩, rfl⟩

end Silmaril.Proofs.Wasm.Institution.SpecGInst

module

public import Silmaril.Wasm.Models.Game.Defs
public import Silmaril.Games.Institution.Thms
public import Silmaril.Games.Reduct.Thms

/-!
# Wasm models in the institution of game semantics: theorems

* `mem_callPlay_iff`: the one-call play `c ↦ o` is a play of the observation strategy iff
  `o ∈ obs c`;
* `obsStrat_mono`, `obsStrat_le_iff`: **refinement of observation strategies is inclusion of
  observations**, so the atlas order of behaviour charts and the refinement order of `GInst`
  agree on observation strategies;
* `Emb.reduct_le`: for an embedding of direction `eq` or `sup` with a total read-back, the reduct
  of the target's strategy along `Emb.gameHom` refines the source's strategy (the lower half of
  the reduct is the identity, and the upper half is `Strategy.restrict_sound`);
* `Emb.sat_translate`: hence a universal `GInst` sentence true of the source's strategy at `p`
  holds of the target's strategy at `e.pt p` after translation (the satisfaction condition
  `GInst.reindex_sat`).

* `Emb.le_reduct`: for directions `eq` and `sub`, the source's strategy refines the reduct of the
  target's (the converse of `Strategy.restrict_sound`, `Strategy.restrict_complete`);
* `Emb.reduct_eq`: hence for direction `eq` **the reduct of the target's strategy is the source's
  strategy**, and `Emb.sat_translate_iff`: every `GInst` sentence, universal or not, transfers in
  both directions.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open CategoryTheory Silmaril.Games

variable {C O : Type}

theorem mem_obsStrat {obs : C → Set O} {s : List (Move Sig.empty (callSig C O))} :
    s ∈ obsStrat obs ↔ Legal s ∧ ∀ (c : C) (o : O),
      (.inr (.ans c o) : Move Sig.empty (callSig C O)) ∈ s → o ∈ obs c :=
  Iff.rfl

theorem callPlay_legal (c : C) (o : O) : Legal (callPlay c o) :=
  ⟨.idle, .cons (Step.ask (E := Sig.empty) (F := callSig C O) c)
    (.cons (Step.ret (E := Sig.empty) (F := callSig C O) c o) (.nil _))⟩

/-- **The one-call play `c ↦ o` is a play of the observation strategy iff `o ∈ obs c`.** -/
theorem mem_callPlay_iff {obs : C → Set O} {c : C} {o : O} :
    callPlay c o ∈ obsStrat obs ↔ o ∈ obs c := by
  constructor
  · intro h
    exact h.2 c o (by simp [callPlay])
  · intro h
    refine ⟨callPlay_legal c o, fun c' o' hm => ?_⟩
    simp only [callPlay, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm
    · cases hm
    · cases hm
      exact h

theorem obsStrat_mono {obs obs' : C → Set O} (h : ∀ c, obs c ⊆ obs' c) :
    obsStrat obs ≤ obsStrat obs' :=
  fun _ hs => ⟨hs.1, fun c o hm => h c (hs.2 c o hm)⟩

/-- **Refinement of observation strategies is inclusion of observations.** -/
theorem obsStrat_le_iff {obs obs' : C → Set O} :
    obsStrat obs ≤ obsStrat obs' ↔ ∀ c, obs c ⊆ obs' c := by
  refine ⟨fun h c o ho => ?_, obsStrat_mono⟩
  exact mem_callPlay_iff.mp (h (mem_callPlay_iff.mpr ho))

/-- Answers of an `UpRel`-image come from answers of the source play. -/
theorem upRel_ans {X G F : Sig.{0}} {ρ : Sig.Hom G F} {s : List (Move X F)}
    {p : List (Move X G)} (hrel : List.Forall₂ (UpRel ρ) s p) {q : G.Op} {a : G.Ar q}
    (hm : (.inr (.ans q a) : Move X G) ∈ p) :
    ∃ n, (.inr (.ans (ρ.op q) n) : Move X F) ∈ s ∧ a = ρ.ar q n := by
  induction hrel with
  | nil => exact absurd hm List.not_mem_nil
  | cons hr _ ih =>
    rcases List.mem_cons.1 hm with he | hm
    · subst he
      cases hr
      exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨n, hn, hna⟩ := ih hm
      exact ⟨n, List.mem_cons_of_mem _ hn, hna⟩

namespace WasmModel

variable {A B : WasmModel}

/-- The read-back view of a total read-back is the image of the observations. -/
theorem Emb.view_eq (e : A.Emb B) (t : e.Total) (x : B.Pt) (c : B.Call) :
    B.view e.readback x c = t.g '' B.obs x c := by
  ext o
  simp only [view, Set.mem_ofPred_eq, Set.mem_image, t.readback_eq, Option.some.injEq]

/-- For directions `eq` and `sup`, read-back target observations are source observations. -/
theorem Emb.view_subset (e : A.Emb B) (hd : e.dir ≠ .sub) {p : A.Pt} (hp : A.dom p)
    (c : A.Call) : B.view e.readback (e.pt p) (e.call c) ⊆ A.obs p c := by
  have h := e.sat p hp c
  cases hdir : e.dir
  · rw [hdir] at h
    exact (show B.view e.readback (e.pt p) (e.call c) = A.obs p c from h) ▸ subset_refl _
  · exact absurd hdir hd
  · rw [hdir] at h
    exact h

/-- The reduct along `Emb.gameHom` is a restriction. -/
theorem Emb.reduct_gameHom (e : A.Emb B) (t : e.Total) (σ : B.game.Model) :
    Game.reduct (e.gameHom t) σ =
      σ.restrict (⟨e.call, fun _ => t.g⟩ : Sig.Hom (callSig A.Call A.Obs) (callSig B.Call B.Obs)) :=
  Game.reduct_id_lo (E := Sig.empty) _ σ

/-- **The reduct of the target's strategy refines the source's** (directions `eq` and `sup`,
total read-back). -/
theorem Emb.reduct_le (e : A.Emb B) (t : e.Total) (hd : e.dir ≠ .sub) {p : A.Pt}
    (hp : A.dom p) : Game.reduct (e.gameHom t) (B.strat (e.pt p)) ≤ A.strat p := by
  intro s hs
  have hl : Legal s := (Game.reduct (e.gameHom t) (B.strat (e.pt p))).legal hs
  rw [Emb.reduct_gameHom] at hs
  obtain ⟨s', hs', hrel⟩ := Strategy.restrict_sound _ _ hs
  refine ⟨hl, fun c o hm => ?_⟩
  have hfrom : ∃ n, (.inr (.ans (e.call c) n) : Move Sig.empty (callSig B.Call B.Obs)) ∈ s' ∧
      o = t.g n := by
    rcases hrel with hrel | ⟨p', q, rfl, hrel⟩
    · exact upRel_ans hrel hm
    · rcases List.mem_append.1 hm with hm | hm
      · exact upRel_ans hrel hm
      · change (Sum.inr (Ev.ans c o) : Move Sig.empty (callSig A.Call A.Obs)) ∈
          ([Sum.inr (Ev.ask q)] : List (Move Sig.empty (callSig A.Call A.Obs))) at hm
        rw [List.mem_singleton] at hm
        cases hm
  obtain ⟨n, hn, rfl⟩ := hfrom
  have hnb : n ∈ B.obs (e.pt p) (e.call c) := hs'.2 _ _ hn
  apply e.view_subset hd hp c
  rw [e.view_eq t]
  exact ⟨n, hnb, rfl⟩

/-- **Transfer along an embedding**: a universal sentence of the source's strategy at `p` holds
of the target's strategy at `e.pt p` after translation. -/
theorem Emb.sat_translate (e : A.Emb B) (t : e.Total) (hd : e.dir ≠ .sub) {p : A.Pt}
    (hp : A.dom p) {φ : GSen A.game.E A.game.F} (hu : φ.Universal) (h : φ.holds (A.strat p)) :
    (Game.senMap (e.gameHom t) φ).holds (B.strat (e.pt p)) :=
  hu (e.reduct_le t hd hp) h

/-- The sentence part of `Emb.ginstCoHom` is the `GInst` translation along `Emb.gameHom`. -/
theorem Emb.ginstCoHom_sen (e : A.Emb B) (t : e.Total) (X : Discrete PUnit.{1})
    (φ : GSen A.game.E A.game.F) :
    ((e.ginstCoHom t).ρ.app X).sen φ = Game.senMap (e.gameHom t) φ :=
  rfl

end WasmModel

/-- Every play whose moves all have preimages satisfying `P` has a preimage play satisfying
`P`. -/
theorem exists_preimage {α β : Type} {R : α → β → Prop} {P : α → Prop} :
    ∀ {s : List β}, (∀ b ∈ s, ∃ a, R a b ∧ P a) →
      ∃ s' : List α, List.Forall₂ R s' s ∧ ∀ a ∈ s', P a
  | [], _ => ⟨[], .nil, fun _ h => absurd h List.not_mem_nil⟩
  | b :: s, h => by
    obtain ⟨a, hab, ha⟩ := h b List.mem_cons_self
    obtain ⟨s', hs', hP⟩ := exists_preimage (s := s) fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨a :: s', .cons hab hs', fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact hP x hx

namespace WasmModel

variable {A B : WasmModel}

/-- For directions `eq` and `sub`, source observations are read-back target observations. -/
theorem Emb.subset_view (e : A.Emb B) (hd : e.dir ≠ .sup) {p : A.Pt} (hp : A.dom p)
    (c : A.Call) : A.obs p c ⊆ B.view e.readback (e.pt p) (e.call c) := by
  have h := e.sat p hp c
  cases hdir : e.dir
  · rw [hdir] at h
    exact (show B.view e.readback (e.pt p) (e.call c) = A.obs p c from h) ▸ subset_refl _
  · rw [hdir] at h
    exact h
  · exact absurd hdir hd

/-- **The source's strategy refines the reduct of the target's** (directions `eq` and `sub`,
total read-back): the converse of `Emb.reduct_le`. -/
theorem Emb.le_reduct (e : A.Emb B) (t : e.Total) (hd : e.dir ≠ .sup) {p : A.Pt}
    (hp : A.dom p) : A.strat p ≤ Game.reduct (e.gameHom t) (B.strat (e.pt p)) := by
  intro s hs
  rw [Emb.reduct_gameHom]
  let ρ : Sig.Hom (callSig A.Call A.Obs) (callSig B.Call B.Obs) := ⟨e.call, fun _ => t.g⟩
  have hpre : ∀ b ∈ s, ∃ a, UpRel ρ a b ∧ ∀ (c : B.Call) (n : B.Obs),
      a = (.inr (.ans c n) : Move Sig.empty (callSig B.Call B.Obs)) → n ∈ B.obs (e.pt p) c := by
    intro b hb
    rcases b with (⟨m⟩ | ⟨m, _⟩) | (⟨c⟩ | ⟨c, o⟩)
    · exact m.elim
    · exact m.elim
    · exact ⟨_, UpRel.ask (ρ := ρ) c, fun _ _ h => by cases h⟩
    · have ho : o ∈ B.view e.readback (e.pt p) (e.call c) :=
        e.subset_view hd hp c (hs.2 c o hb)
      rw [e.view_eq t] at ho
      obtain ⟨n, hn, rfl⟩ := ho
      exact ⟨_, UpRel.ans (ρ := ρ) c n, fun c' n' h => by cases h; exact hn⟩
  obtain ⟨s', hr, hP⟩ := exists_preimage hpre
  have hs' : s' ∈ B.strat (e.pt p) :=
    ⟨Strategy.legal_of_upRel hr hs.1, fun c n hm => hP _ hm c n rfl⟩
  exact Strategy.restrict_complete _ ρ hs' hr hs.1

/-- **For an equality embedding, the reduct of the target's strategy is the source's.** -/
theorem Emb.reduct_eq (e : A.Emb B) (t : e.Total) (hd : e.dir = .eq) {p : A.Pt}
    (hp : A.dom p) : Game.reduct (e.gameHom t) (B.strat (e.pt p)) = A.strat p :=
  le_antisymm (e.reduct_le t (by rw [hd]; exact nofun) hp)
    (e.le_reduct t (by rw [hd]; exact nofun) hp)

/-- **Transfer along an equality embedding**: every `GInst` sentence holds of the source's
strategy at `p` iff its translation holds of the target's strategy at `e.pt p`. -/
theorem Emb.sat_translate_iff (e : A.Emb B) (t : e.Total) (hd : e.dir = .eq) {p : A.Pt}
    (hp : A.dom p) (φ : GSen A.game.E A.game.F) :
    (Game.senMap (e.gameHom t) φ).holds (B.strat (e.pt p)) ↔ φ.holds (A.strat p) := by
  change φ.holds (Game.reduct (e.gameHom t) (B.strat (e.pt p))) ↔ _
  rw [e.reduct_eq t hd hp]

/-- **Existential transfer** along an embedding of direction `eq` or `sub`: an existential
sentence true of the source's strategy holds of the target's strategy after translation. -/
theorem Emb.sat_translate_exist (e : A.Emb B) (t : e.Total) (hd : e.dir ≠ .sup) {p : A.Pt}
    (hp : A.dom p) {φ : GSen A.game.E A.game.F} (he : φ.Existential) (h : φ.holds (A.strat p)) :
    (Game.senMap (e.gameHom t) φ).holds (B.strat (e.pt p)) :=
  he (e.le_reduct t hd hp) h

end WasmModel

end Silmaril.Wasm.Models

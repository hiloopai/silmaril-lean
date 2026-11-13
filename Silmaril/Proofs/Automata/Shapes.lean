module

public import Silmaril.Automata.Shapes.Defs
public import Silmaril.Automata.Spec.Thms
public import Silmaril.Automata.Institution.Thms

/-!
# Standard problem shapes for finite machines: proofs

Transfer between typed machines and the JSON documents they are bound to.
-/

@[expose] public section

namespace Silmaril.Proofs.Automata

open Silmaril.Automata Silmaril.Automata.Shapes

theorem toLTS_eq_of_canon_eq {sp sp' : Spec} (h : sp.canon = sp'.canon) : sp.toLTS = sp'.toLTS := by
  have : ∀ s l d, sp.Step s l d ↔ sp'.Step s l d := fun s l d => by
    rw [← Spec.canon_step_iff, h, Spec.canon_step_iff]
  unfold Spec.toLTS
  congr 1
  funext s l d
  exact propext (this s l d)

theorem jsonReach_iff_of_bound {S L : Type} [FinNamed S] [FinNamed L] (M : DMachine S L)
    (d : Document) (h : M.toSpec.canon = d.spec.canon) (P : L → Bool) (a b : S) :
    Reach M P a b ↔ JsonReach d (((FinNamed.elems (α := L)).filter P).map FinNamed.name)
      (FinNamed.name a) (FinNamed.name b) := by
  have h1 : Reach M P a b ↔
      Inst.Sat (Inst.DMachine.model M) (.reach ((FinNamed.elems (α := L)).filter P) a b) := by
    unfold Reach Inst.Sat
    simp only [Inst.DMachine.model, List.mem_filter, FinNamed.complete, true_and]
    rfl
  rw [h1, Inst.sat_toSpec_iff]
  unfold JsonReach
  rw [← toLTS_eq_of_canon_eq h]
  rfl

theorem jsonBisimilar_iff_of_bound {S T L : Type} [FinNamed S] [FinNamed T] [FinNamed L]
    (M : DMachine S L) (N : DMachine T L) (d e : Document) (hd : M.toSpec.canon = d.spec.canon)
    (he : N.toSpec.canon = e.spec.canon) (s : S) (t : T) :
    Bisimilar M N s t ↔ JsonBisimilar d e (FinNamed.name s) (FinNamed.name t) := by
  unfold Bisimilar JsonBisimilar
  rw [← toLTS_eq_of_canon_eq hd, ← toLTS_eq_of_canon_eq he]
  constructor
  · rintro ⟨R, hR, hb⟩
    refine ⟨fun x y => ∃ s t, R s t ∧ x = FinNamed.name s ∧ y = FinNamed.name t,
      ⟨s, t, hR, rfl, rfl⟩, ?_⟩
    rintro x y ⟨s₁, t₁, hr, rfl, rfl⟩ μ
    constructor
    · intro x' hx
      change M.toSpec.Step _ μ x' at hx
      obtain ⟨a, l, a', hst, hed⟩ := (mem_toSpec_edges M _).mp hx
      obtain ⟨h1, h2, h3⟩ := Edge.mk.inj hed
      rw [← FinNamed.name_inj h1] at hst
      obtain ⟨t', ht', hr'⟩ := (hb hr l).1 a' hst
      exact ⟨FinNamed.name t', by
        change N.toSpec.Step _ _ _
        rw [h2]; exact (toSpec_step_iff N _ _ _).mpr ht', a', t', hr', h3, rfl⟩
    · intro y' hy
      change N.toSpec.Step _ μ y' at hy
      obtain ⟨a, l, a', hst, hed⟩ := (mem_toSpec_edges N _).mp hy
      obtain ⟨h1, h2, h3⟩ := Edge.mk.inj hed
      rw [← FinNamed.name_inj h1] at hst
      obtain ⟨s', hs', hr'⟩ := (hb hr l).2 a' hst
      exact ⟨FinNamed.name s', by
        change M.toSpec.Step _ _ _
        rw [h2]; exact (toSpec_step_iff M _ _ _).mpr hs', s', a', hr', rfl, h3⟩
  · rintro ⟨R, hR, hb⟩
    refine ⟨fun s t => R (FinNamed.name s) (FinNamed.name t), hR, ?_⟩
    intro s₁ t₁ hr l
    constructor
    · intro s' hs'
      obtain ⟨y, hy, hr'⟩ := (hb hr (FinNamed.name l)).1 (FinNamed.name s')
        ((toSpec_step_iff M _ _ _).mpr hs')
      change N.toSpec.Step _ _ _ at hy
      obtain ⟨a, k, a', hst, hed⟩ := (mem_toSpec_edges N _).mp hy
      obtain ⟨h1, h2, h3⟩ := Edge.mk.inj hed
      rw [← FinNamed.name_inj h1, ← FinNamed.name_inj h2] at hst
      exact ⟨a', hst, by show R _ _; rw [← h3]; exact hr'⟩
    · intro t' ht'
      obtain ⟨x, hx, hr'⟩ := (hb hr (FinNamed.name l)).2 (FinNamed.name t')
        ((toSpec_step_iff N _ _ _).mpr ht')
      change M.toSpec.Step _ _ _ at hx
      obtain ⟨a, k, a', hst, hed⟩ := (mem_toSpec_edges M _).mp hx
      obtain ⟨h1, h2, h3⟩ := Edge.mk.inj hed
      rw [← FinNamed.name_inj h1, ← FinNamed.name_inj h2] at hst
      exact ⟨a', hst, by show R _ _; rw [← h3]; exact hr'⟩

end Silmaril.Proofs.Automata

namespace Silmaril.Proofs.Automata

open Silmaril.Automata Silmaril.Automata.Shapes

attribute [local instance] memFintype

/-- `U` and `LU` contain every edge's endpoints and label. -/
def Closed (sp : Spec) (U LU : List String) : Prop :=
  ∀ e ∈ sp.edges, e.src ∈ U ∧ e.label ∈ LU ∧ e.dst ∈ U

theorem closed_all (sp : Spec) (X Y : List String) :
    Closed sp (X ++ sp.allStates) (Y ++ sp.allLabels) := by
  intro e he
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Spec.allStates, Spec.allLabels, List.mem_append,
    List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  · exact Or.inr (Or.inr ⟨e, he, Or.inl rfl⟩)
  · exact Or.inr (Or.inr ⟨e, he, rfl⟩)
  · exact Or.inr (Or.inr ⟨e, he, Or.inr rfl⟩)

theorem restrict_tr {sp : Spec} {U LU : List String} (x : {x // x ∈ U}) (l : {x // x ∈ LU})
    (y : {x // x ∈ U}) : (sp.restrict U LU).toLTS.Tr x l y ↔ sp.Step x.1 l.1 y.1 := by
  simp [Spec.restrict, NMachine.toLTS]

theorem reach_iff_restrict {sp : Spec} {U LU : List String} (hc : Closed sp U LU)
    (ls : List String) {a b : String} (ha : a ∈ U) (hb : b ∈ U) :
    ReachVia sp.toLTS (· ∈ ls) a b ↔
      ReachVia (sp.restrict U LU).toLTS (fun l => decide (l.1 ∈ ls) = true) ⟨a, ha⟩ ⟨b, hb⟩ := by
  constructor
  · intro h
    have key : ∀ y, ReachVia sp.toLTS (· ∈ ls) a y → ∃ hy : y ∈ U,
        ReachVia (sp.restrict U LU).toLTS (fun l => decide (l.1 ∈ ls) = true) ⟨a, ha⟩ ⟨y, hy⟩ := by
      intro y hy
      induction hy with
      | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
      | tail _ hst ih =>
        obtain ⟨hy, hr⟩ := ih
        obtain ⟨l, hl, htr⟩ := hst
        obtain ⟨-, hlU, hzU⟩ := hc _ htr
        exact ⟨hzU, Relation.ReflTransGen.tail hr
          ⟨⟨l, hlU⟩, by simpa using hl, (restrict_tr _ _ _).mpr htr⟩⟩
    obtain ⟨_, hr⟩ := key b h
    exact hr
  · intro h
    have key : ∀ y, ReachVia (sp.restrict U LU).toLTS (fun l => decide (l.1 ∈ ls) = true)
        ⟨a, ha⟩ y → ReachVia sp.toLTS (· ∈ ls) a y.1 := by
      intro y hy
      induction hy with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hst ih =>
        obtain ⟨l, hl, htr⟩ := hst
        exact Relation.ReflTransGen.tail ih ⟨l.1, by simpa using hl, (restrict_tr _ _ _).mp htr⟩
    exact key _ h

theorem bisimilar_iff_restrict {d e : Spec} {U V LU : List String} (hd : Closed d U LU)
    (he : Closed e V LU) {a b : String} (ha : a ∈ U) (hb : b ∈ V) :
    Cslib.LTS.Bisimilarity d.toLTS e.toLTS a b ↔
      Cslib.LTS.Bisimilarity (d.restrict U LU).toLTS (e.restrict V LU).toLTS ⟨a, ha⟩ ⟨b, hb⟩ := by
  constructor
  · rintro ⟨R, hR, hb'⟩
    refine ⟨fun x y => R x.1 y.1, hR, ?_⟩
    intro x y hr l
    refine ⟨fun x' hx => ?_, fun y' hy => ?_⟩
    · obtain ⟨y'', hy'', hr'⟩ := (hb' hr l.1).1 x'.1 ((restrict_tr _ _ _).mp hx)
      obtain ⟨-, -, hyV⟩ := he _ hy''
      exact ⟨⟨y'', hyV⟩, (restrict_tr _ _ _).mpr hy'', hr'⟩
    · obtain ⟨x'', hx'', hr'⟩ := (hb' hr l.1).2 y'.1 ((restrict_tr _ _ _).mp hy)
      obtain ⟨-, -, hxU⟩ := hd _ hx''
      exact ⟨⟨x'', hxU⟩, (restrict_tr _ _ _).mpr hx'', hr'⟩
  · rintro ⟨R, hR, hb'⟩
    refine ⟨fun x y => ∃ (hx : x ∈ U) (hy : y ∈ V), R ⟨x, hx⟩ ⟨y, hy⟩, ⟨ha, hb, hR⟩, ?_⟩
    rintro x y ⟨hx, hy, hr⟩ μ
    refine ⟨fun x' htr => ?_, fun y' htr => ?_⟩
    · obtain ⟨-, hμ, hx'⟩ := hd _ htr
      obtain ⟨y'', hy'', hr'⟩ :=
        (hb' hr ⟨μ, hμ⟩).1 ⟨x', hx'⟩ ((restrict_tr ⟨x, hx⟩ ⟨μ, hμ⟩ ⟨x', hx'⟩).mpr htr)
      exact ⟨y''.1, (restrict_tr _ _ _).mp hy'', hx', y''.2, hr'⟩
    · obtain ⟨-, hμ, hy'⟩ := he _ htr
      obtain ⟨x'', hx'', hr'⟩ :=
        (hb' hr ⟨μ, hμ⟩).2 ⟨y', hy'⟩ ((restrict_tr ⟨y, hy⟩ ⟨μ, hμ⟩ ⟨y', hy'⟩).mpr htr)
      exact ⟨x''.1, (restrict_tr _ _ _).mp hx'', x''.2, hy', hr'⟩

theorem similar_iff_restrict {d e : Spec} {U V LU : List String} (hd : Closed d U LU)
    (he : Closed e V LU) {a b : String} (ha : a ∈ U) (hb : b ∈ V) :
    Cslib.LTS.Similarity d.toLTS e.toLTS a b ↔
      Cslib.LTS.Similarity (d.restrict U LU).toLTS (e.restrict V LU).toLTS ⟨a, ha⟩ ⟨b, hb⟩ := by
  constructor
  · rintro ⟨R, hR, hs⟩
    refine ⟨fun x y => R x.1 y.1, hR, ?_⟩
    intro x y hr l x' hx
    obtain ⟨y'', hy'', hr'⟩ := hs hr l.1 x'.1 ((restrict_tr _ _ _).mp hx)
    obtain ⟨-, -, hyV⟩ := he _ hy''
    exact ⟨⟨y'', hyV⟩, (restrict_tr _ _ _).mpr hy'', hr'⟩
  · rintro ⟨R, hR, hs⟩
    refine ⟨fun x y => ∃ (hx : x ∈ U) (hy : y ∈ V), R ⟨x, hx⟩ ⟨y, hy⟩, ⟨ha, hb, hR⟩, ?_⟩
    rintro x y ⟨hx, hy, hr⟩ μ x' htr
    obtain ⟨-, hμ, hx'⟩ := hd _ htr
    obtain ⟨y'', hy'', hr'⟩ :=
      hs hr ⟨μ, hμ⟩ ⟨x', hx'⟩ ((restrict_tr ⟨x, hx⟩ ⟨μ, hμ⟩ ⟨x', hx'⟩).mpr htr)
    exact ⟨y''.1, (restrict_tr _ _ _).mp hy'', hx', y''.2, hr'⟩

theorem mem_runSet (sp : Spec) (w : List String) : ∀ (X : List String) (t : String),
    t ∈ Spec.runSet sp X w ↔ ∃ s ∈ X, sp.toLTS.MTr s w t := by
  induction w with
  | nil =>
    intro X t
    simp only [Spec.runSet]
    constructor
    · intro h; exact ⟨t, h, .refl⟩
    · rintro ⟨s, hs, h⟩; cases h; exact hs
  | cons l w ih =>
    intro X t
    simp only [Spec.runSet, ih]
    constructor
    · rintro ⟨m, hm, hmt⟩
      simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at hm
      obtain ⟨e, ⟨he, hsrc, hlab⟩, rfl⟩ := hm
      refine ⟨e.src, hsrc, .stepL (?_ : sp.Step e.src l e.dst) hmt⟩
      unfold Spec.Step; rw [← hlab]; exact he
    · rintro ⟨s, hs, h⟩
      cases h with
      | stepL htr hrest =>
        refine ⟨_, ?_, hrest⟩
        simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨_, ⟨htr, hs, rfl⟩, rfl⟩

theorem jsonAccepts_iff (d : Document) (w : List String) :
    JsonAccepts d w ↔ ∃ t ∈ Spec.runSet d.spec d.layers.initial w, t ∈ d.layers.accepting := by
  unfold JsonAccepts
  constructor
  · rintro ⟨s, hs, t, ht, h⟩
    exact ⟨t, (mem_runSet _ _ _ _).mpr ⟨s, hs, h⟩, ht⟩
  · rintro ⟨t, ht, hta⟩
    obtain ⟨s, hs, h⟩ := (mem_runSet _ _ _ _).mp ht
    exact ⟨s, hs, t, hta, h⟩

end Silmaril.Proofs.Automata

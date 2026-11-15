module

public import Silmaril.Games.Abstract.FullFun.Defs
import Silmaril.Proofs.Games.Abstract.FullFun.Laws

/-!
# Full observations: pure maps, whiskering and premonoidal structure (proofs)

* membership in `FullFun.map` (`mem_map`, `mem_map_trap`, `mem_map_div`, `mem_map_ret`);
* functoriality of `map` (`map_id`, `map_map`);
* interaction with sequencing: `seq_pure_map`, `seq_map`, `map_seq`, `pure_map_seq`;
* whiskering preserves the identity and sequencing (`whiskerRight_pure`, `whiskerRight_seq`,
  `whiskerLeft_pure`, `whiskerLeft_seq`), proved one context value at a time
  (`ext_comap_right`, `ext_comap_left`);
* interchange when one side is a pure map (`interchange_pure_left`, `interchange_pure_right`),
  and its failure for two effectful functions (`not_interchange`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.FullFun

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {E : Sig.{u}} {S A B C D : Type u}

/-! ## Membership -/

theorem mem_map (f : FullFun E S A B) (h : B → C) (s : S) (a : A) (x : CallBeh E S C) :
    x ∈ (f.map h).1 s a ↔ ∃ c e, (c, e) ∈ f.1 s a ∧ x = (c, FullFun.endMap h e) := by
  constructor
  · rintro ⟨⟨c, e⟩, hy, rfl⟩
    exact ⟨c, e, hy, rfl⟩
  · rintro ⟨c, e, hy, rfl⟩
    exact ⟨(c, e), hy, rfl⟩

theorem mem_map_trap (f : FullFun E S A B) (h : B → C) (s : S) (a : A) (c : List (Call E)) :
    (c, End.trap) ∈ (f.map h).1 s a ↔ (c, End.trap) ∈ f.1 s a := by
  rw [mem_map]
  constructor
  · rintro ⟨c', e, hy, he⟩
    obtain ⟨rfl, he⟩ := Prod.mk.inj he
    cases e with
    | ret => cases he
    | trap => exact hy
    | div => cases he
  · intro hy
    exact ⟨c, .trap, hy, rfl⟩

theorem mem_map_div (f : FullFun E S A B) (h : B → C) (s : S) (a : A) (c : List (Call E)) :
    (c, End.div) ∈ (f.map h).1 s a ↔ (c, End.div) ∈ f.1 s a := by
  rw [mem_map]
  constructor
  · rintro ⟨c', e, hy, he⟩
    obtain ⟨rfl, he⟩ := Prod.mk.inj he
    cases e with
    | ret => cases he
    | trap => cases he
    | div => exact hy
  · intro hy
    exact ⟨c, .div, hy, rfl⟩

theorem mem_map_ret (f : FullFun E S A B) (h : B → C) (s : S) (a : A) (c : List (Call E))
    (b' : C) (s' : S) :
    (c, End.ret b' s') ∈ (f.map h).1 s a ↔ ∃ b, (c, End.ret b s') ∈ f.1 s a ∧ h b = b' := by
  rw [mem_map]
  constructor
  · rintro ⟨c', e, hy, he⟩
    obtain ⟨rfl, he⟩ := Prod.mk.inj he
    cases e with
    | ret b s₁ =>
      simp only [FullFun.endMap] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨b, hy, rfl⟩
    | trap => cases he
    | div => cases he
  · rintro ⟨b, hy, rfl⟩
    exact ⟨c, .ret b s', hy, rfl⟩

theorem pure_map_fst (h : A → B) (s : S) (a : A) :
    ((FullFun.pure : FullFun E S A A).map h).1 s a = {([], End.ret (h a) s)} :=
  Set.image_singleton

/-! ## Functoriality -/

theorem endMap_id (e : End S B) : FullFun.endMap id e = e := by
  cases e <;> rfl

theorem endMap_comp (h : B → C) (h' : C → D) (e : End S B) :
    FullFun.endMap h' (FullFun.endMap h e) = FullFun.endMap (h' ∘ h) e := by
  cases e <;> rfl

theorem map_id (f : FullFun E S A B) : f.map id = f := by
  refine Prod.ext (funext fun s => funext fun a => ?_) rfl
  change (fun x => (x.1, FullFun.endMap id x.2)) '' f.1 s a = f.1 s a
  simp only [endMap_id, Prod.mk.eta, Set.image_id']

theorem map_map (f : FullFun E S A B) (h : B → C) (h' : C → D) :
    (f.map h).map h' = f.map (h' ∘ h) := by
  refine Prod.ext (funext fun s => funext fun a => ?_) rfl
  change (fun x => (x.1, FullFun.endMap h' x.2)) ''
      ((fun x => (x.1, FullFun.endMap h x.2)) '' f.1 s a) =
    (fun x => (x.1, FullFun.endMap (h' ∘ h) x.2)) '' f.1 s a
  rw [Set.image_image]
  simp only [endMap_comp]

/-! ## Sequencing -/

/-- Sequencing with a pure map is that map. -/
theorem seq_pure_map (f : FullFun E S A B) (h : B → C) :
    FullFun.seq f (FullFun.pure.map h) = f.map h := by
  refine Prod.ext (funext fun s => funext fun a => ?_) ?_
  · ext x
    rw [mem_map]
    simp only [FullFun.seq, AFun.seq, Set.mem_ofPred_eq, pure_map_fst, Set.mem_singleton_iff]
    constructor
    · rintro (⟨c, hf, rfl⟩ | ⟨c, hf, rfl⟩ | ⟨c₁, b, s₁, c₂, e, hf, hp, rfl⟩)
      · exact ⟨c, .trap, hf, rfl⟩
      · exact ⟨c, .div, hf, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        exact ⟨c₁, .ret b s₁, hf, by rw [List.append_nil]; rfl⟩
    · rintro ⟨c, e, hf, rfl⟩
      cases e with
      | ret b s₁ => exact .inr (.inr ⟨c, b, s₁, [], _, hf, rfl, by rw [List.append_nil]; rfl⟩)
      | trap => exact .inl ⟨c, hf, rfl⟩
      | div => exact .inr (.inl ⟨c, hf, rfl⟩)
  · funext s a
    ext ω
    simp only [FullFun.seq, FullFun.map, FullFun.pure, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, false_and, and_false, exists_false, or_false]

/-- A pure map before `g` is pre-composition of `g`. -/
theorem seq_map (f : FullFun E S A B) (h : B → C) (g : FullFun E S C D) :
    FullFun.seq (f.map h) g = FullFun.seq f (g.comap h) := by
  refine Prod.ext (funext fun s => funext fun a => ?_) ?_
  · ext x
    simp only [FullFun.seq, AFun.seq, Set.mem_ofPred_eq, mem_map_trap, mem_map_div]
    refine or_congr Iff.rfl (or_congr Iff.rfl ⟨?_, ?_⟩)
    · rintro ⟨c₁, b', s₁, c₂, e, hf, hg, rfl⟩
      obtain ⟨b, hf', rfl⟩ := (mem_map_ret f h s a c₁ b' s₁).1 hf
      exact ⟨c₁, b, s₁, c₂, e, hf', hg, rfl⟩
    · rintro ⟨c₁, b, s₁, c₂, e, hf, hg, rfl⟩
      exact ⟨c₁, h b, s₁, c₂, e, (mem_map_ret f h s a c₁ _ s₁).2 ⟨b, hf, rfl⟩, hg, rfl⟩
  · funext s a
    ext ω
    simp only [FullFun.seq, Set.mem_union, Set.mem_ofPred_eq]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨c, b', s₁, ω', hf, hg, rfl⟩
      obtain ⟨b, hf', rfl⟩ := (mem_map_ret f h s a c b' s₁).1 hf
      exact ⟨c, b, s₁, ω', hf', hg, rfl⟩
    · rintro ⟨c, b, s₁, ω', hf, hg, rfl⟩
      exact ⟨c, h b, s₁, ω', (mem_map_ret f h s a c _ s₁).2 ⟨b, hf, rfl⟩, hg, rfl⟩

/-- A pure map after a sequence is a pure map after its second part. -/
theorem map_seq (f : FullFun E S A B) (g : FullFun E S B C) (h : C → D) :
    (FullFun.seq f g).map h = FullFun.seq f (g.map h) := by
  refine Prod.ext (funext fun s => funext fun a => ?_) rfl
  ext x
  rw [mem_map]
  simp only [FullFun.seq, AFun.seq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, e, (⟨c', hf, he⟩ | ⟨c', hf, he⟩ | ⟨c₁, b, s₁, c₂, e', hf, hg, he⟩), rfl⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact .inl ⟨_, hf, rfl⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact .inr (.inl ⟨_, hf, rfl⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact .inr (.inr ⟨c₁, b, s₁, c₂, _, hf, (mem_map g h s₁ b _).2 ⟨c₂, _, hg, rfl⟩, rfl⟩)
  · rintro (⟨c, hf, rfl⟩ | ⟨c, hf, rfl⟩ | ⟨c₁, b, s₁, c₂, e, hf, hg, rfl⟩)
    · exact ⟨c, .trap, .inl ⟨c, hf, rfl⟩, rfl⟩
    · exact ⟨c, .div, .inr (.inl ⟨c, hf, rfl⟩), rfl⟩
    · obtain ⟨c₂', e', hg', he⟩ := (mem_map g h s₁ b _).1 hg
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨_, _, .inr (.inr ⟨c₁, b, s₁, _, _, hf, hg', rfl⟩), rfl⟩

/-- Sequencing after a pure map is pre-composition. -/
theorem pure_map_seq (h : A → B) (g : FullFun E S B C) :
    FullFun.seq (FullFun.pure.map h) g = g.comap h := by
  rw [seq_map]
  exact pure_seq _

theorem comap_pure_map {A' : Type u} (h : A → B) (k : A' → A) :
    ((FullFun.pure : FullFun E S A A).map h).comap k = FullFun.pure.map (h ∘ k) := by
  refine Prod.ext (funext fun s => funext fun a => ?_) rfl
  change ((FullFun.pure : FullFun E S A A).map h).1 s (k a) =
    ((FullFun.pure : FullFun E S A' A').map (h ∘ k)).1 s a
  rw [pure_map_fst, pure_map_fst]
  rfl

/-! ## Whiskering -/

/-- Full observations on pairs agree when they agree at each second component. -/
theorem ext_comap_right {X : Type u} {F G : FullFun E S (A × C) X}
    (h : ∀ c, F.comap (·, c) = G.comap (·, c)) : F = G := by
  refine Prod.ext (funext fun s => funext fun p => ?_) (funext fun s => funext fun p => ?_)
  · exact congrFun (congrFun (congrArg Prod.fst (h p.2)) s) p.1
  · exact congrFun (congrFun (congrArg Prod.snd (h p.2)) s) p.1

/-- Full observations on pairs agree when they agree at each first component. -/
theorem ext_comap_left {X : Type u} {F G : FullFun E S (C × A) X}
    (h : ∀ c, F.comap (c, ·) = G.comap (c, ·)) : F = G := by
  refine Prod.ext (funext fun s => funext fun p => ?_) (funext fun s => funext fun p => ?_)
  · exact congrFun (congrFun (congrArg Prod.fst (h p.1)) s) p.2
  · exact congrFun (congrFun (congrArg Prod.snd (h p.1)) s) p.2

theorem whiskerRight_pure : (FullFun.pure : FullFun E S A A).whiskerRight C = FullFun.pure :=
  Prod.ext (funext fun _ => funext fun _ => Set.image_singleton) rfl

theorem whiskerLeft_pure : (FullFun.pure : FullFun E S A A).whiskerLeft C = FullFun.pure :=
  Prod.ext (funext fun _ => funext fun _ => Set.image_singleton) rfl

theorem whiskerRight_seq (f : FullFun E S A B) (g : FullFun E S B D) (C : Type u) :
    (FullFun.seq f g).whiskerRight C = FullFun.seq (f.whiskerRight C) (g.whiskerRight C) := by
  refine ext_comap_right fun c => ?_
  change (FullFun.seq f g).map (·, c) = FullFun.seq (f.map (·, c)) (g.whiskerRight C)
  rw [seq_map, map_seq]
  rfl

theorem whiskerLeft_seq (f : FullFun E S A B) (g : FullFun E S B D) (C : Type u) :
    (FullFun.seq f g).whiskerLeft C = FullFun.seq (f.whiskerLeft C) (g.whiskerLeft C) := by
  refine ext_comap_left fun c => ?_
  change (FullFun.seq f g).map (c, ·) = FullFun.seq (f.map (c, ·)) (g.whiskerLeft C)
  rw [seq_map, map_seq]
  rfl

theorem whiskerRight_pure_map (h : A → B) (C : Type u) :
    ((FullFun.pure : FullFun E S A A).map h).whiskerRight C =
      FullFun.pure.map (Prod.map h id) := by
  refine ext_comap_right fun c => ?_
  rw [comap_pure_map]
  change ((FullFun.pure : FullFun E S A A).map h).map (·, c) = _
  rw [map_map]
  rfl

theorem whiskerLeft_pure_map (h : A → B) (C : Type u) :
    ((FullFun.pure : FullFun E S A A).map h).whiskerLeft C =
      FullFun.pure.map (Prod.map id h) := by
  refine ext_comap_left fun c => ?_
  rw [comap_pure_map]
  change ((FullFun.pure : FullFun E S A A).map h).map (c, ·) = _
  rw [map_map]
  rfl

/-! ## Interchange -/

/-- Interchange when the first component is a pure map. -/
theorem interchange_pure_left (h : A → B) (g : FullFun E S C D) :
    FullFun.seq (((FullFun.pure : FullFun E S A A).map h).whiskerRight C) (g.whiskerLeft B) =
      FullFun.seq (g.whiskerLeft A)
        (((FullFun.pure : FullFun E S A A).map h).whiskerRight D) := by
  rw [whiskerRight_pure_map, whiskerRight_pure_map, pure_map_seq]
  refine ext_comap_left fun a => ?_
  change (g.whiskerLeft B).comap (fun c => (h a, c)) =
    FullFun.seq (g.map (a, ·)) (FullFun.pure.map (Prod.map h id))
  rw [seq_map, comap_pure_map, seq_pure_map]
  rfl

/-- Interchange when the second component is a pure map. -/
theorem interchange_pure_right (f : FullFun E S A B) (k : C → D) :
    FullFun.seq (f.whiskerRight C) (((FullFun.pure : FullFun E S C C).map k).whiskerLeft B) =
      FullFun.seq (((FullFun.pure : FullFun E S C C).map k).whiskerLeft A)
        (f.whiskerRight D) := by
  rw [whiskerLeft_pure_map, whiskerLeft_pure_map, pure_map_seq]
  refine ext_comap_right fun c => ?_
  change FullFun.seq (f.map (·, c)) (FullFun.pure.map (Prod.map id k)) =
    (f.whiskerRight D).comap (fun a => (a, k c))
  rw [seq_map, comap_pure_map, seq_pure_map]
  rfl

/-! ## Interchange fails for effectful functions -/

/-- Two operations, each with a single answer. -/
def boolSig : Sig.{0} := ⟨Bool, fun _ => PUnit⟩

/-- Call `m` once, then return. -/
def callOnce (m : Bool) : FullFun boolSig PUnit PUnit PUnit :=
  (fun _ _ => {([⟨m, ⟨⟩⟩], End.ret ⟨⟩ ⟨⟩)}, fun _ _ => ∅)

theorem callOnce_mem {m : Bool} {c : List (Call boolSig)} {e : End PUnit PUnit}
    (h : (c, e) ∈ (callOnce m).1 ⟨⟩ ⟨⟩) : c = [⟨m, ⟨⟩⟩] ∧ e = End.ret ⟨⟩ ⟨⟩ :=
  Prod.mk.inj h

/-- **The interchange law fails**: running two effectful functions on the two components in
either order gives different call logs. -/
theorem not_interchange :
    FullFun.seq ((callOnce true).whiskerRight PUnit) ((callOnce false).whiskerLeft PUnit) ≠
      FullFun.seq ((callOnce false).whiskerLeft PUnit) ((callOnce true).whiskerRight PUnit) := by
  intro heq
  have hm : ([⟨true, ⟨⟩⟩, ⟨false, ⟨⟩⟩], End.ret (⟨⟩, ⟨⟩) ⟨⟩) ∈
      (FullFun.seq ((callOnce true).whiskerRight PUnit)
        ((callOnce false).whiskerLeft PUnit)).1 ⟨⟩ (⟨⟩, ⟨⟩) :=
    .inr (.inr ⟨[⟨true, ⟨⟩⟩], (⟨⟩, ⟨⟩), ⟨⟩, [⟨false, ⟨⟩⟩], _, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩)
  rw [heq] at hm
  rcases hm with ⟨c, hc, -⟩ | ⟨c, hc, -⟩ | ⟨c₁, b, s₁, c₂, e, hc₁, -, he⟩
  · cases (callOnce_mem ((mem_map_trap (callOnce false) _ _ _ _).1 hc)).2
  · cases (callOnce_mem ((mem_map_div (callOnce false) _ _ _ _).1 hc)).2
  · obtain ⟨_, hy, -⟩ := (mem_map_ret (callOnce false) _ _ _ _ _ _).1 hc₁
    obtain ⟨rfl, -⟩ := callOnce_mem hy
    have h₁ := congrArg (fun l => (List.head? l).map Sigma.fst) (Prod.mk.inj he).1
    cases h₁

end Silmaril.Proofs.Games.Abstract.FullFun

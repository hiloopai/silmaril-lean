module

public import Silmaril.Games.Abstract.FullFun.Defs
public import Silmaril.Games.Abstract.HostRunInf.Thms
import Silmaril.Proofs.Games.Abstract.FullFun.Basic

/-!
# Full observations: associativity, identities and iteration (proofs)

* `seq_assoc_fin`, `seq_assoc_inf`: sequencing is associative, finite part (`AFun.seq`) and
  productive runs (`List.append` and `Stream'.append_append_stream`);
* `seq_pure`, `pure_seq`: the identity is a unit on both sides;
* `consistent_streamConcat`: a concatenated stream is consistent exactly when every segment is;
* `hostObsInf_iter`: host preservation of iteration.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.FullFun

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {E : Sig.{u}} {S A B C D : Type u}

/-- Associativity of `AFun.seq`. -/
theorem seq_assoc_fin (f : AFun E S A B) (g : AFun E S B C) (h : AFun E S C D) :
    AFun.seq (AFun.seq f g) h = AFun.seq f (AFun.seq g h) := by
  funext s a
  ext x
  simp only [AFun.seq, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c₁, b, s₁, c₂, e, hc, hh, rfl⟩)
    · rcases hc with ⟨c', hf, he⟩ | ⟨c', _, he⟩ | ⟨d₁, b, s₁, d₂, e, hf, hg, he⟩
      · obtain ⟨rfl, -⟩ := Prod.mk.inj he
        exact .inl ⟨c, hf, rfl⟩
      · cases (Prod.mk.inj he).2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact .inr (.inr ⟨d₁, b, s₁, d₂, _, hf, .inl ⟨d₂, hg, rfl⟩, rfl⟩)
    · rcases hc with ⟨c', _, he⟩ | ⟨c', hf, he⟩ | ⟨d₁, b, s₁, d₂, e, hf, hg, he⟩
      · cases (Prod.mk.inj he).2
      · obtain ⟨rfl, -⟩ := Prod.mk.inj he
        exact .inr (.inl ⟨c, hf, rfl⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact .inr (.inr ⟨d₁, b, s₁, d₂, _, hf, .inr (.inl ⟨d₂, hg, rfl⟩), rfl⟩)
    · rcases hc with ⟨c', _, he⟩ | ⟨c', _, he⟩ | ⟨d₁, b', s', d₂, e', hf, hg, he⟩
      · cases (Prod.mk.inj he).2
      · cases (Prod.mk.inj he).2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact .inr (.inr ⟨d₁, b', s', d₂ ++ c₂, e, hf,
          .inr (.inr ⟨d₂, b, s₁, c₂, e, hg, hh, rfl⟩), by rw [List.append_assoc]⟩)
  · rintro (⟨c, hf, rfl⟩ | ⟨c, hf, rfl⟩ | ⟨c₁, b, s₁, c₂, e, hf, hc, rfl⟩)
    · exact .inl ⟨c, .inl ⟨c, hf, rfl⟩, rfl⟩
    · exact .inr (.inl ⟨c, .inr (.inl ⟨c, hf, rfl⟩), rfl⟩)
    · rcases hc with ⟨c', hg, he⟩ | ⟨c', hg, he⟩ | ⟨d₁, b', s', d₂, e', hg, hh, he⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact .inl ⟨_, .inr (.inr ⟨c₁, b, s₁, _, _, hf, hg, rfl⟩), rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact .inr (.inl ⟨_, .inr (.inr ⟨c₁, b, s₁, _, _, hf, hg, rfl⟩), rfl⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact .inr (.inr ⟨c₁ ++ d₁, b', s', d₂, _, .inr (.inr ⟨c₁, b, s₁, d₁, _, hf, hg, rfl⟩),
          hh, by rw [List.append_assoc]⟩)

/-- Associativity of sequencing, productive runs. -/
theorem seq_assoc_inf (f : FullFun E S A B) (g : FullFun E S B C) (h : FullFun E S C D) :
    (FullFun.seq (FullFun.seq f g) h).2 = (FullFun.seq f (FullFun.seq g h)).2 := by
  funext s a
  ext ω
  simp only [FullFun.seq, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ((hf | ⟨c, b, s₁, ω', hf, hg, rfl⟩) | ⟨c, d, s₂, ω', hc, hh, rfl⟩)
    · exact .inl hf
    · exact .inr ⟨c, b, s₁, ω', hf, .inl hg, rfl⟩
    · simp only [AFun.seq, Set.mem_ofPred_eq] at hc
      rcases hc with ⟨c', _, he⟩ | ⟨c', _, he⟩ | ⟨d₁, b, s₁, d₂, e, hf, hg, he⟩
      · cases (Prod.mk.inj he).2
      · cases (Prod.mk.inj he).2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact .inr ⟨d₁, b, s₁, d₂ ++ₛ ω', hf, .inr ⟨d₂, d, s₂, ω', hg, hh, rfl⟩,
          Stream'.append_append_stream _ _ _⟩
  · rintro (hf | ⟨c, b, s₁, ω', hf, hg | ⟨c₂, d, s₂, ω'', hg, hh, rfl⟩, rfl⟩)
    · exact .inl (.inl hf)
    · exact .inl (.inr ⟨c, b, s₁, ω', hf, hg, rfl⟩)
    · refine .inr ⟨c ++ c₂, d, s₂, ω'', ?_, hh, (Stream'.append_append_stream _ _ _).symm⟩
      exact .inr (.inr ⟨c, b, s₁, c₂, _, hf, hg, rfl⟩)

/-- The identity is a right unit. -/
theorem seq_pure (f : FullFun E S A B) : FullFun.seq f FullFun.pure = f := by
  refine Prod.ext ?_ ?_
  · funext s a
    ext ⟨c, e⟩
    simp only [FullFun.seq, FullFun.pure, AFun.seq, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro (⟨c', hf, he⟩ | ⟨c', hf, he⟩ | ⟨c₁, b, s₁, c₂, e', hf, hp, he⟩)
      · rwa [he]
      · rwa [he]
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        rwa [he, List.append_nil]
    · intro hf
      cases e with
      | ret b s₁ => exact .inr (.inr ⟨c, b, s₁, [], _, hf, rfl, by rw [List.append_nil]⟩)
      | trap => exact .inl ⟨c, hf, rfl⟩
      | div => exact .inr (.inl ⟨c, hf, rfl⟩)
  · funext s a
    ext ω
    simp only [FullFun.seq, FullFun.pure, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, false_and, and_false, exists_false, or_false]

/-- The identity is a left unit. -/
theorem pure_seq (g : FullFun E S A B) : FullFun.seq FullFun.pure g = g := by
  refine Prod.ext ?_ (funext fun s => funext fun a => pure_seq_inf g s a)
  funext s a
  ext x
  simp only [FullFun.seq, FullFun.pure, AFun.seq, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro (⟨c', hp, -⟩ | ⟨c', hp, -⟩ | ⟨c₁, b, s₁, c₂, e', hp, hg, rfl⟩)
    · cases (Prod.mk.inj hp).2
    · cases (Prod.mk.inj hp).2
    · obtain ⟨rfl, he⟩ := Prod.mk.inj hp
      cases he
      exact hg
  · intro hg
    exact .inr (.inr ⟨[], a, s, x.1, x.2, rfl, hg, rfl⟩)

/-- A list is a prefix of itself in front of a stream. -/
theorem streamPrefix_appendStream {α : Type u} (c : List α) (ω : Nat → α) :
    Shape.StreamPrefix c (c ++ₛ ω) :=
  fun _ h => append_get_lt c ω h

/-- A chain of streams, each a segment in front of the next. -/
theorem appendStream_chain {α : Type u} {w : Nat → Nat → α} {cs : Nat → List α}
    (h : ∀ n, w n = cs n ++ₛ w (n + 1)) (n : Nat) :
    w 0 = ((List.range n).flatMap cs) ++ₛ w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ih, h n]
    exact (Stream'.append_append_stream _ (cs n) (w (n + 1))).symm

/-- A chain of streams of unbounded total length is the concatenation of its segments. -/
theorem streamConcat_of_appendChain {α : Type u} {w : Nat → Nat → α} {cs : Nat → List α}
    (h : ∀ n, w n = cs n ++ₛ w (n + 1))
    (hu : ∀ N, ∃ n, N ≤ ((List.range n).flatMap cs).length) : Shape.StreamConcat cs (w 0) := by
  refine ⟨fun n => ?_, hu⟩
  rw [appendStream_chain h n]
  exact streamPrefix_appendStream _ _

/-- Consistency of a concatenated stream is consistency of every segment. -/
theorem consistent_streamConcat {R : HostRel E} {l : Nat → List (Call E)} {ω : Nat → Call E}
    (h : Shape.StreamConcat l ω) :
    (∀ n, R (ω n).1 (.answer (ω n).2)) ↔ ∀ n, R.Consistent (l n) := by
  obtain ⟨hp, hu⟩ := h
  constructor
  · intro hω n x hx
    have hm : x ∈ (List.range (n + 1)).flatMap l :=
      List.mem_flatMap.2 ⟨n, List.mem_range.2 (Nat.lt_succ_self n), hx⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    rw [← hp (n + 1) i hi]
    exact hω i
  · intro hl i
    obtain ⟨k, hk⟩ := hu (i + 1)
    have hi : i < ((List.range k).flatMap l).length := hk
    rw [hp k i hi]
    obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 (List.getElem_mem hi)
    exact hl j _ hj

/-- **Host preservation of iteration** (productive part). -/
theorem hostObsInf_iter {R : HostRel E} (F : FullFun E S A (B ⊕ A)) (s : S) (a : A)
    (ω : Nat → Call E) :
    ω ∈ hostObsInf R (FullFun.iter F).2 s a ↔
      (∃ (c : List (Call E)) (s' : S) (a' : A) (ω' : Nat → Call E),
          FullFun.ContChain F.1 s a c s' a' ∧ R.Consistent c ∧ ω' ∈ hostObsInf R F.2 s' a' ∧
          ω = c ++ₛ ω') ∨
        ∃ (σ : Nat → S × A) (l : Nat → List (Call E)), σ 0 = (s, a) ∧
          (∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ F.1 (σ n).1 (σ n).2) ∧
          (∀ n, R.Consistent (l n)) ∧ Shape.StreamConcat l ω := by
  constructor
  · rintro ⟨⟨c, s', a', ω', hc, hf, rfl⟩ | ⟨σ, l, h0, hσ, hl⟩, hω⟩
    · obtain ⟨hc₁, hc₂⟩ := (consistent_append c ω').mp hω
      exact .inl ⟨c, s', a', ω', hc, hc₁, ⟨hf, hc₂⟩, rfl⟩
    · exact .inr ⟨σ, l, h0, hσ, (consistent_streamConcat hl).1 hω, hl⟩
  · rintro (⟨c, s', a', ω', hc, hc₁, ⟨hf, hc₂⟩, rfl⟩ | ⟨σ, l, h0, hσ, hR, hl⟩)
    · exact ⟨.inl ⟨c, s', a', ω', hc, hf, rfl⟩, (consistent_append c ω').mpr ⟨hc₁, hc₂⟩⟩
    · exact ⟨.inr ⟨σ, l, h0, hσ, hl⟩, (consistent_streamConcat hl).2 hR⟩

end Silmaril.Proofs.Games.Abstract.FullFun

module

public import Silmaril.Wasm.Institution.DivGames.Graph.Defs

@[expose] public section

/-!
# The divergence-aware game logic: proofs

* `behOf_ofBeh`: the stateless server `ofBeh B` has exactly the
  single-invocation behaviours `B`.
* `scopedLe_upperR_iff`: the Galois connection behind the entry comorphism:
  refinement through `X` below `upperR R δ'` is `R`-refinement of the
  single-invocation behaviours of the exports in `X`.
-/

namespace Silmaril.Wasm.Institution.DivGames

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Games Silmaril.Wasm.Institution.Games

variable {E : Silmaril.Games.Sig.{0}}

/-! ## The stateless server -/

private theorem good_of_exch_prefix {B : USig.Op → Set (Behaviour Val)} {q : USig.Op}
    {b : Behaviour Val} : ∀ {xs : List (USig.Op × Behaviour Val)}, Good B xs →
      exch (E := E) q b <+: flat xs → b ≠ .diverges ∧ b ∈ B q
  | [], _, hp => absurd hp.length_le (by simp [exch, flat])
  | ⟨q', b'⟩ :: xs, hg, hp => by
    have hp' : exch (E := E) q b <+: exch q' b' ++ flat xs := hp
    have h₂ : exch (E := E) q b = exch q' b' :=
      (List.prefix_of_prefix_length_le hp' (List.prefix_append _ _) (by simp [exch])).eq_of_length
        (by simp [exch])
    cases h₂
    exact hg _ List.mem_cons_self

theorem mem_exch_ofBeh {B : USig.Op → Set (Behaviour Val)} {q : USig.Op} {b : Behaviour Val} :
    exch q b ∈ (ofBeh (E := E) B).toStrategy ↔ b ≠ .diverges ∧ b ∈ B q := by
  constructor
  · intro h
    obtain ⟨-, u, hu, hp⟩ := Strategy.mem_generate.1 h
    rcases hu with rfl | ⟨⟨xs, hg, rfl⟩, -⟩
    · rcases hp with hp | ⟨p₀, o, he, -, ho⟩
      · exact absurd hp.length_le (by simp [exch])
      · exact (exch_ne_concat he ho).elim
    · rcases hp with hp | ⟨p₀, o, he, -, ho⟩
      · exact good_of_exch_prefix hg hp
      · exact (exch_ne_concat he ho).elim
  · rintro ⟨hb, hB⟩
    have hg : Good B [(q, b)] := fun e he => by
      rw [List.mem_singleton.1 he]
      exact ⟨hb, hB⟩
    exact Strategy.subset_generate ⟨[(q, b)], hg, rfl⟩ ⟨_, path_flat [(q, b)]⟩

theorem mem_div_ask_ofBeh {B : USig.Op → Set (Behaviour Val)} {q : USig.Op} :
    [.inr (.ask q)] ∈ (ofBeh (E := E) B).div ↔ .diverges ∈ B q := by
  constructor
  · rintro ⟨xs, q', -, hq', he⟩
    have hl : (flat (E := E) xs).length = 0 := by
      have := congrArg List.length he
      simp only [List.length_append, List.length_singleton] at this
      omega
    rw [List.length_eq_zero_iff.1 hl, List.nil_append] at he
    cases he
    exact hq'
  · intro h
    exact ⟨[], q, fun _ he => absurd he List.not_mem_nil, h, rfl⟩

/-- The stateless server has exactly the behaviours it is given. -/
theorem behOf_ofBeh (B : USig.Op → Set (Behaviour Val)) (q : USig.Op) :
    behOf (ofBeh (E := E) B) q = B q := by
  ext b
  by_cases hb : b = .diverges
  · rw [hb]
    exact ⟨fun h => h.elim (fun h' => (h'.1 rfl).elim) fun h' => mem_div_ask_ofBeh.1 h'.2,
      fun h => .inr ⟨rfl, mem_div_ask_ofBeh.2 h⟩⟩
  · exact ⟨fun h => h.elim (fun h' => (mem_exch_ofBeh.1 h'.2).2) fun h' => (hb h'.1).elim,
      fun h => .inl ⟨hb, mem_exch_ofBeh.2 ⟨hb, h⟩⟩⟩

/-! ## The Galois connection -/

theorem scoped_exch {X : Set String} {q : USig.Op} (hq : q.1.1 ∈ X) (b : Behaviour Val) :
    Scoped (E := E) X (exch q b) := by
  intro q' hq'
  have he : q' = q := by simpa [exch] using hq'
  rw [he]
  exact hq

theorem scoped_ask {X : Set String} {q : USig.Op} (hq : q.1.1 ∈ X) :
    Scoped (E := E) X [.inr (.ask q)] := by
  intro q' hq'
  have he : q' = q := by simpa using hq'
  rw [he]
  exact hq

private theorem plays_upper {X : Set String} {R : BRel} {δ δ' : DStrategy E USig}
    (h : ∀ q : USig.Op, q.1.1 ∈ X → Behaviours.Refines R (behOf δ q) (behOf δ' q))
    {p : List (Move E USig)} (hs : Scoped X p) (hp : p ∈ δ.toStrategy) : p ∈ upperPlays R δ' := by
  refine ⟨δ.toStrategy.legal hp, fun q b hpre hne => ?_⟩
  have hq : q.1.1 ∈ X := hs q (hpre.subset (by simp [exch]))
  exact h q hq b (.inl ⟨hne, δ.toStrategy.of_prefix hp hpre⟩)

/-- **The Galois connection**: refinement through `X` below `upperR R δ'` is
`R`-refinement of the single-invocation behaviours of the exports in `X`. -/
theorem scopedLe_upperR_iff {X : Set String} {R : BRel} {δ δ' : DStrategy E USig} :
    ScopedLe X δ (upperR R δ') ↔
      ∀ q : USig.Op, q.1.1 ∈ X → Behaviours.Refines R (behOf δ q) (behOf δ' q) := by
  constructor
  · intro h q hq b hb
    rcases hb with ⟨hne, hm⟩ | ⟨rfl, hd⟩
    · exact (h.1 _ (scoped_exch hq b) hm).2 q b (List.prefix_refl _) hne
    · exact (h.2.1 _ (scoped_ask hq) hd).2.2 q rfl
  · intro h
    refine ⟨fun p hs hp => plays_upper h hs hp, fun p hs hp => ?_, fun I hI hs => ?_⟩
    · refine ⟨plays_upper h hs (δ.div_mem hp), δ.div_run hp, fun q hpq => ?_⟩
      have hq : q.1.1 ∈ X := hs q (by rw [hpq]; exact List.mem_singleton_self _)
      exact h q hq .diverges (.inr ⟨rfl, hpq ▸ hp⟩)
    · exact ⟨δ.inf_isInf hI, fun p hp => plays_upper h (hs p hp) (δ.inf_sub hI hp)⟩

end Silmaril.Wasm.Institution.DivGames

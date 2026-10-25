module

public import Silmaril.Wasm.Behaviour.Basic

/-!
# The behaviour relation library

The relations of the behavior-refinement hierarchy, defined on the shared `Behaviour` type
and lifted to the behaviour *sets* that a nondeterministic semantics produces.

| Relation | Meaning | Kind |
|---|---|---|
| `Eq` | identical observation | equivalence |
| `TrapDiv` | trap and divergence identified | equivalence |
| `TrapRefines` | `b` may trap where `b'` does not | preorder, bottom `traps` |
| `TrapRefinesDiv` | the same, modulo `TrapDiv` | preorder, bottom `traps`/`diverges` |

The inclusions are

```
            Eq  ⊆  TrapRefines
            ∩           ∩
         TrapDiv ⊆ TrapRefinesDiv
```

and the two refinements are *antisymmetric up to* the equivalence directly
above them: `TrapRefines ∩ TrapRefinesᵒᵖ = Eq` (`trapRefines_antisymm`) and
`TrapRefinesDiv ∩ TrapRefinesDivᵒᵖ = TrapDiv` (`trapRefinesDiv_antisymm`). That
is the sense in which each equivalence is the kernel of its refinement, as
the contextual-refinement contract asks for.

## Why trap insertion is the right notion for engines and compilers

A real engine may trap where the specification does not — stack exhaustion, an
allocation failure, an implementation limit — and the specification explicitly
permits resource exhaustion. It may never *remove* a trap or change a returned
value. That is exactly `TrapRefines`, whose bottom element is the semantics that
always traps (`alwaysTraps`, `trapRefines_alwaysTraps`). The same relation is
what compiler correctness becomes once stack overflow is admitted; see a separate compiler-refinement development (not included in this package).

## Demonic and angelic liftings

A semantics is nondeterministic, so the object of study is a `Set (Behaviour V)`.
`Behaviours.Refines R s t` is the **demonic** (∀∃) lifting: *every* behaviour of
`s` is `R`-related to *some* behaviour of `t`. This is the one that means
"`s` is a correct implementation of `t`", and the one used everywhere below.
`Behaviours.MayRefine` is the **angelic** (∃∃) lifting, recorded for
completeness; it is not a preorder in general and is used only for
counterexample statements.
-/

@[expose] public section

namespace Silmaril.Wasm

universe u v w

namespace Behaviour

variable {V : Type u} {W : Type v} {X : Type w}

/-! ## Trap ≈ divergence

The partial-correctness view: judge a semantics only on the values it returns,
identifying the two ways of producing none. -/

/-- Trap and divergence identified, everything else on the nose. -/
def TrapDiv (b : Behaviour V) (b' : Behaviour V) : Prop :=
  b = b' ∨ (b.NoResult ∧ b'.NoResult)

theorem TrapDiv.refl (b : Behaviour V) : TrapDiv b b := Or.inl rfl

theorem TrapDiv.symm {b b' : Behaviour V} (h : TrapDiv b b') : TrapDiv b' b :=
  h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.2, h.1⟩)

theorem TrapDiv.trans {b b' b'' : Behaviour V} (h : TrapDiv b b') (h' : TrapDiv b' b'') :
    TrapDiv b b'' := by
  rcases h with rfl | ⟨hb, hb'⟩
  · exact h'
  · rcases h' with rfl | ⟨_, hb''⟩
    · exact Or.inr ⟨hb, hb'⟩
    · exact Or.inr ⟨hb, hb''⟩

theorem trapDiv_equivalence : Equivalence (TrapDiv (V := V)) :=
  ⟨TrapDiv.refl, TrapDiv.symm, TrapDiv.trans⟩

@[simp] theorem trapDiv_traps_diverges : TrapDiv (.traps : Behaviour V) .diverges :=
  Or.inr ⟨trivial, trivial⟩

@[simp] theorem trapDiv_diverges_traps : TrapDiv (.diverges : Behaviour V) .traps :=
  Or.inr ⟨trivial, trivial⟩

/-- On returning behaviours, `TrapDiv` is equality: it identifies nothing that
produces a value. -/
theorem TrapDiv.eq_of_returns {vs : List V} {b : Behaviour V}
    (h : TrapDiv (.returns vs) b) : b = .returns vs :=
  h.elim Eq.symm (fun h => absurd h.1 (by simp))

/-! ## Trap insertion

A refinement, not an equivalence: `b` may trap where `b'` does not. -/

/-- `b ⊑ b'`: the implementation behaviour `b` either traps, or is exactly the
specification behaviour `b'`. -/
def TrapRefines (b b' : Behaviour V) : Prop := b = .traps ∨ b = b'

theorem TrapRefines.refl (b : Behaviour V) : TrapRefines b b := Or.inr rfl

theorem TrapRefines.trans {b b' b'' : Behaviour V} (h : TrapRefines b b')
    (h' : TrapRefines b' b'') : TrapRefines b b'' := by
  rcases h with h | rfl
  · exact Or.inl h
  · exact h'

/-- `traps` is the bottom element. -/
@[simp] theorem trapRefines_traps (b : Behaviour V) : TrapRefines .traps b := Or.inl rfl

/-- Trap insertion never removes a trap: a refinement of a returning behaviour
either traps or returns the same values. -/
theorem TrapRefines.returns_cases {b : Behaviour V} {vs : List V}
    (h : TrapRefines b (.returns vs)) : b = .traps ∨ b = .returns vs := h

/-- Trap insertion is antisymmetric: its kernel is equality. -/
theorem trapRefines_antisymm {b b' : Behaviour V} (h : TrapRefines b b')
    (h' : TrapRefines b' b) : b = b' := by
  rcases h with rfl | rfl
  · rcases h' with rfl | rfl <;> rfl
  · rfl

/-! ## Trap insertion modulo trap ≈ divergence -/

/-- `b ⊑' b'`: the implementation behaviour `b` produces no result, or is exactly
`b'`. This is `TrapRefines` composed with `TrapDiv`, and it is well defined on
the `TrapDiv` quotient (`trapRefinesDiv_congr`). -/
def TrapRefinesDiv (b b' : Behaviour V) : Prop := b.NoResult ∨ b = b'

theorem TrapRefinesDiv.refl (b : Behaviour V) : TrapRefinesDiv b b := Or.inr rfl

theorem TrapRefinesDiv.trans {b b' b'' : Behaviour V} (h : TrapRefinesDiv b b')
    (h' : TrapRefinesDiv b' b'') : TrapRefinesDiv b b'' := by
  rcases h with h | rfl
  · exact Or.inl h
  · exact h'

@[simp] theorem trapRefinesDiv_traps (b : Behaviour V) : TrapRefinesDiv .traps b :=
  Or.inl trivial

@[simp] theorem trapRefinesDiv_diverges (b : Behaviour V) : TrapRefinesDiv .diverges b :=
  Or.inl trivial

/-- `TrapDiv`-related behaviours produce a result together. -/
theorem TrapDiv.noResult_iff {b c : Behaviour V} (h : TrapDiv b c) :
    b.NoResult ↔ c.NoResult :=
  h.elim (fun h => h ▸ Iff.rfl) (fun h => iff_of_true h.1 h.2)

/-- Well definedness on the `TrapDiv` quotient. -/
theorem trapRefinesDiv_congr {b c b' c' : Behaviour V} (hb : TrapDiv b c)
    (hb' : TrapDiv b' c') : TrapRefinesDiv b b' ↔ TrapRefinesDiv c c' := by
  have fwd : ∀ {x y u w : Behaviour V}, TrapDiv x u → TrapDiv y w →
      TrapRefinesDiv x y → TrapRefinesDiv u w := by
    rintro x y u w hxu hyw (h | rfl)
    · exact Or.inl (hxu.noResult_iff.mp h)
    · by_cases hx : x.NoResult
      · exact Or.inl (hxu.noResult_iff.mp hx)
      · have hxu' : x = u := hxu.elim id fun h => absurd h.1 hx
        have hyw' : x = w := hyw.elim id fun h => absurd h.1 hx
        exact Or.inr (hxu'.symm.trans hyw')
  exact ⟨fwd hb hb', fwd hb.symm hb'.symm⟩

/-- The kernel of `TrapRefinesDiv` is `TrapDiv`. -/
theorem trapRefinesDiv_antisymm {b b' : Behaviour V} (h : TrapRefinesDiv b b')
    (h' : TrapRefinesDiv b' b) : TrapDiv b b' := by
  rcases h with h | rfl
  · rcases h' with h' | rfl
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-! ## The inclusion lattice -/

theorem TrapRefines.of_eq {b b' : Behaviour V} (h : b = b') : TrapRefines b b' := Or.inr h

theorem TrapDiv.of_eq {b b' : Behaviour V} (h : b = b') : TrapDiv b b' := Or.inl h

theorem TrapRefines.trapRefinesDiv {b b' : Behaviour V} (h : TrapRefines b b') :
    TrapRefinesDiv b b' := by
  rcases h with rfl | h
  · exact Or.inl trivial
  · exact Or.inr h

theorem TrapDiv.trapRefinesDiv {b b' : Behaviour V} (h : TrapDiv b b') :
    TrapRefinesDiv b b' := h.elim Or.inr (fun h => Or.inl h.1)

/-- `Eq` and `TrapRefines` are incomparable with `TrapDiv` in the other
direction: trap insertion does not identify a trap with divergence. -/
theorem not_trapRefines_diverges_traps :
    ¬ TrapRefines (.diverges : Behaviour V) .traps := by
  rintro (h | h) <;> cases h

/-- `TrapRefines` is strictly finer than `TrapRefinesDiv`. -/
theorem not_trapRefines_of_diverges {b : Behaviour V} (h : b = .returns []) :
    ¬ TrapRefines (.diverges : Behaviour V) b := by
  subst h; rintro (h | h) <;> cases h

/-! ## Stability under value renaming -/

@[simp] theorem trapDiv_map {f : V → W} (hf : Function.Injective f) {b b' : Behaviour V} :
    TrapDiv (map f b) (map f b') ↔ TrapDiv b b' := by
  simp only [TrapDiv, noResult_map]
  exact or_congr ⟨fun h => map_injective hf h, congrArg _⟩ Iff.rfl

@[simp] theorem trapRefines_map {f : V → W} (hf : Function.Injective f) {b b' : Behaviour V} :
    TrapRefines (map f b) (map f b') ↔ TrapRefines b b' := by
  constructor
  · rintro (h | h)
    · exact Or.inl (by cases b <;> simp_all [map])
    · exact Or.inr (map_injective hf h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem TrapRefines.map {f : V → W} {b b' : Behaviour V} (h : TrapRefines b b') :
    TrapRefines (Behaviour.map f b) (Behaviour.map f b') := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem TrapDiv.map {f : V → W} {b b' : Behaviour V} (h : TrapDiv b b') :
    TrapDiv (Behaviour.map f b) (Behaviour.map f b') := by
  rcases h with rfl | ⟨hb, hb'⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by simpa using hb, by simpa using hb'⟩

theorem TrapRefinesDiv.map {f : V → W} {b b' : Behaviour V} (h : TrapRefinesDiv b b') :
    TrapRefinesDiv (Behaviour.map f b) (Behaviour.map f b') := by
  rcases h with h | rfl
  · exact Or.inl (by simpa using h)
  · exact Or.inr rfl

end Behaviour

/-! ## Lifting to behaviour sets -/

namespace Behaviours

open Behaviour

variable {V : Type u} {W : Type v} {X : Type w}

/-- The **demonic** (∀∃) lifting: every behaviour of `s` is `R`-related to some
behaviour of `t`. Read "`s` implements `t` up to `R`". -/
def Refines (R : Behaviour V → Behaviour W → Prop)
    (s : Set (Behaviour V)) (t : Set (Behaviour W)) : Prop :=
  ∀ b ∈ s, ∃ b' ∈ t, R b b'

/-- The **angelic** (∃∃) lifting. Not a preorder; recorded for completeness. -/
def MayRefine (R : Behaviour V → Behaviour W → Prop)
    (s : Set (Behaviour V)) (t : Set (Behaviour W)) : Prop :=
  ∃ b ∈ s, ∃ b' ∈ t, R b b'

/-- Two-sided refinement: the equivalence generated by a relation. -/
def Equiv (R : Behaviour V → Behaviour W → Prop)
    (s : Set (Behaviour V)) (t : Set (Behaviour W)) : Prop :=
  Refines R s t ∧ Refines (fun b b' => R b' b) t s

theorem Refines.mono {R S : Behaviour V → Behaviour W → Prop}
    (h : ∀ b b', R b b' → S b b') {s : Set (Behaviour V)} {t : Set (Behaviour W)}
    (hr : Refines R s t) : Refines S s t :=
  fun b hb => (hr b hb).imp fun _ h' => ⟨h'.1, h _ _ h'.2⟩

theorem Refines.mono_right {R : Behaviour V → Behaviour W → Prop}
    {s : Set (Behaviour V)} {t t' : Set (Behaviour W)} (ht : t ⊆ t')
    (hr : Refines R s t) : Refines R s t' :=
  fun b hb => (hr b hb).imp fun _ h' => ⟨ht h'.1, h'.2⟩

theorem Refines.mono_left {R : Behaviour V → Behaviour W → Prop}
    {s s' : Set (Behaviour V)} {t : Set (Behaviour W)} (hs : s' ⊆ s)
    (hr : Refines R s t) : Refines R s' t :=
  fun b hb => hr b (hs hb)

theorem Refines.refl (s : Set (Behaviour V)) : Refines (· = ·) s s :=
  fun b hb => ⟨b, hb, rfl⟩

theorem Refines.trans {R : Behaviour V → Behaviour W → Prop}
    {S : Behaviour W → Behaviour X → Prop} {T : Behaviour V → Behaviour X → Prop}
    (hRS : ∀ b b' b'', R b b' → S b' b'' → T b b'')
    {s : Set (Behaviour V)} {t : Set (Behaviour W)} {u : Set (Behaviour X)}
    (h : Refines R s t) (h' : Refines S t u) : Refines T s u := by
  intro b hb
  obtain ⟨b', hb', hr⟩ := h b hb
  obtain ⟨b'', hb'', hr'⟩ := h' b' hb'
  exact ⟨b'', hb'', hRS _ _ _ hr hr'⟩

/-- Refinement at `Eq` is set inclusion. -/
theorem refines_eq_iff {s t : Set (Behaviour V)} : Refines (· = ·) s t ↔ s ⊆ t := by
  constructor
  · intro h b hb
    obtain ⟨b', hb', rfl⟩ := h b hb
    exact hb'
  · exact fun h b hb => ⟨b, h hb, rfl⟩

/-- Two-sided refinement at `Eq` is set equality. -/
theorem equiv_eq_iff {s t : Set (Behaviour V)} : Equiv (· = ·) s t ↔ s = t := by
  rw [Equiv, refines_eq_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine Set.Subset.antisymm h₁ fun b hb => ?_
    obtain ⟨b', hb', rfl⟩ := h₂ b hb
    exact hb'
  · rintro rfl
    exact ⟨Set.Subset.rfl, fun b hb => ⟨b, hb, rfl⟩⟩

/-- Refinement along a value renaming is image inclusion. -/
theorem refines_map_iff {f : V → W} {s : Set (Behaviour V)} {t : Set (Behaviour W)} :
    Refines (fun b b' => Behaviour.map f b = b') s t ↔ Behaviour.mapSet f s ⊆ t := by
  constructor
  · rintro h b ⟨a, ha, rfl⟩
    obtain ⟨b', hb', rfl⟩ := h a ha
    exact hb'
  · exact fun h b hb => ⟨Behaviour.map f b, h ⟨b, hb, rfl⟩, rfl⟩

/-! ## Refinement at a preorder

`Refines` inherits reflexivity and transitivity from the relation it lifts, so a
preorder on behaviours — trap insertion, trap insertion modulo `TrapDiv` — lifts
to a preorder on behaviour sets. That is what makes a chain of compiler phases
compose. -/

/-- The demonic lifting of a reflexive relation is reflexive. -/
theorem Refines.refl_of {R : Behaviour V → Behaviour V → Prop} (hR : ∀ b, R b b)
    (s : Set (Behaviour V)) : Refines R s s := fun b hb => ⟨b, hb, hR b⟩

/-- The demonic lifting of a transitive relation is transitive. -/
theorem Refines.trans_of {R : Behaviour V → Behaviour V → Prop}
    (hR : ∀ b b' b'', R b b' → R b' b'' → R b b'') {s t u : Set (Behaviour V)}
    (h : Refines R s t) (h' : Refines R t u) : Refines R s u :=
  Refines.trans hR h h'

/-- Trap insertion on behaviour sets is reflexive: a phase that inserts no trap
refines its source. -/
theorem refines_trapRefines_refl (s : Set (Behaviour V)) : Refines TrapRefines s s :=
  Refines.refl_of TrapRefines.refl s

/-- Trap insertion on behaviour sets is transitive: compiler phases compose. -/
theorem Refines.trapRefines_trans {s t u : Set (Behaviour V)} (h : Refines TrapRefines s t)
    (h' : Refines TrapRefines t u) : Refines TrapRefines s u :=
  Refines.trans_of (R := TrapRefines) (fun _ _ _ h₁ h₂ => h₁.trans h₂) h h'

/-- Trap insertion on behaviour sets is a preorder. -/
instance isPreorder_refines_trapRefines :
    IsPreorder (Set (Behaviour V)) (Refines TrapRefines) where
  refl := refines_trapRefines_refl
  trans := fun _ _ _ => Refines.trapRefines_trans

/-- Trap insertion modulo trap ≈ divergence on behaviour sets is reflexive. -/
theorem refines_trapRefinesDiv_refl (s : Set (Behaviour V)) : Refines TrapRefinesDiv s s :=
  Refines.refl_of TrapRefinesDiv.refl s

/-- Trap insertion modulo trap ≈ divergence on behaviour sets is transitive. -/
theorem Refines.trapRefinesDiv_trans {s t u : Set (Behaviour V)}
    (h : Refines TrapRefinesDiv s t) (h' : Refines TrapRefinesDiv t u) :
    Refines TrapRefinesDiv s u :=
  Refines.trans_of (R := TrapRefinesDiv) (fun _ _ _ h₁ h₂ => h₁.trans h₂) h h'

/-! ## The bottom semantics -/

/-- The semantics that always traps: the bottom element of trap-insertion
refinement. -/
def alwaysTraps : Set (Behaviour V) := {Behaviour.traps}

/-- Every nonempty behaviour set is refined by the always-trapping one. -/
theorem trapRefines_alwaysTraps {t : Set (Behaviour V)} (ht : t.Nonempty) :
    Refines TrapRefines alwaysTraps t := by
  rintro b rfl
  obtain ⟨b', hb'⟩ := ht
  exact ⟨b', hb', Or.inl rfl⟩

end Behaviours

end Silmaril.Wasm

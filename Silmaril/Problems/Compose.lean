module

/-!
# Composing solutions: the assume–guarantee shape

A problem may depend on other problems (`deps` in `problem.toml`,
`docs/Problems.md`). A *composite* solution is an ordinary theorem built from
component solutions and a **link theorem**: the component statements, taken
together, imply the composite statement. Nothing here is specific to problems:
statements are plain propositions and solutions are plain proofs, so a
component solution is used by name, exactly like any other theorem.

* `All ps` is the conjunction of a list of statements, and `compose` is the
  list-shaped composition rule: component solutions plus a link give the
  composite.
* `AG` is an assume–guarantee contract `assume → guarantee`; `AG.seq` composes
  two contracts in sequence (the second component's assumption may use the
  first's guarantee), and `AG.weaken` adapts a contract to a stronger
  assumption and a weaker guarantee.

The link theorem is where the real work of a composition is: it is stated
over the component *statements*, never over their proofs, so a component can
be re-solved (a different proof, a different tier of evidence with the same
statement) without touching the composite.
-/

@[expose] public section

namespace Silmaril.Problems

/-- The conjunction of a list of statements. Reducible, so that a proof is
written `⟨h₁, h₂, trivial⟩`. -/
@[reducible] def All : List Prop → Prop
  | [] => True
  | p :: ps => p ∧ All ps

@[simp] theorem all_nil : All [] ↔ True := Iff.rfl

@[simp] theorem all_cons {p : Prop} {ps : List Prop} : All (p :: ps) ↔ p ∧ All ps := Iff.rfl

theorem all_iff_forall {ps : List Prop} : All ps ↔ ∀ p ∈ ps, p := by
  induction ps with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => trivial⟩
  | cons p ps ih =>
    constructor
    · intro ⟨h, hs⟩ q hq
      cases hq with
      | head => exact h
      | tail _ m => exact ih.mp hs q m
    · intro h
      exact ⟨h p (.head _), ih.mpr fun q hq => h q (.tail _ hq)⟩

theorem All.of_mem {ps : List Prop} (h : All ps) {p : Prop} (hp : p ∈ ps) : p :=
  all_iff_forall.mp h p hp

theorem all_append {ps qs : List Prop} : All (ps ++ qs) ↔ All ps ∧ All qs := by
  induction ps with
  | nil => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons p ps ih =>
    exact ⟨fun ⟨h, hs⟩ => ⟨⟨h, (ih.mp hs).1⟩, (ih.mp hs).2⟩,
      fun ⟨⟨h, hs⟩, hq⟩ => ⟨h, ih.mpr ⟨hs, hq⟩⟩⟩

/-- **Composition.** Solutions of the component statements, and a link theorem
from the components to the composite, give a solution of the composite. -/
theorem compose {components : List Prop} {composite : Prop}
    (solutions : All components) (link : All components → composite) : composite :=
  link solutions

/-- An assume–guarantee contract. -/
structure AG where
  /-- What the environment (callers, linked components, the OS) provides. -/
  assume : Prop
  /-- What the component then guarantees. -/
  guarantee : Prop

/-- The contract holds: under its assumption, its guarantee does. -/
def AG.Holds (c : AG) : Prop := c.assume → c.guarantee

/-- Strengthen the assumption and weaken the guarantee of a contract. -/
theorem AG.weaken {c d : AG} (h : c.Holds) (pre : d.assume → c.assume)
    (post : d.assume → c.guarantee → d.guarantee) : d.Holds :=
  fun a => post a (h (pre a))

/-- **Sequential assume–guarantee composition.** The composite's assumption
establishes the first component's; with the first guarantee it establishes
the second component's; and the two guarantees give the composite's. The three
link obligations `pre`, `mid` and `post` are the link theorem. -/
theorem AG.seq {c₁ c₂ c : AG} (h₁ : c₁.Holds) (h₂ : c₂.Holds)
    (pre : c.assume → c₁.assume) (mid : c.assume → c₁.guarantee → c₂.assume)
    (post : c.assume → c₁.guarantee → c₂.guarantee → c.guarantee) : c.Holds :=
  fun a =>
    have g₁ := h₁ (pre a)
    post a g₁ (h₂ (mid a g₁))

/-- Component contracts whose assumptions all hold give all their guarantees. -/
theorem AG.guarantees {cs : List AG} (hs : All (cs.map AG.Holds))
    (ha : All (cs.map AG.assume)) : All (cs.map AG.guarantee) := by
  induction cs with
  | nil => trivial
  | cons d ds ih =>
    simp only [List.map_cons] at hs ha ⊢
    exact ⟨hs.1 ha.1, ih hs.2 ha.2⟩

/-- **Parallel composition** of a list of contracts under a shared assumption:
the composite assumption establishes every component's, and all component
guarantees give the composite's. -/
theorem AG.par {cs : List AG} {c : AG} (hs : All (cs.map AG.Holds))
    (pre : c.assume → All (cs.map AG.assume))
    (post : c.assume → All (cs.map AG.guarantee) → c.guarantee) : c.Holds :=
  fun a => post a (AG.guarantees hs (pre a))

end Silmaril.Problems

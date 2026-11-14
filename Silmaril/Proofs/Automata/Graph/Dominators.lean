module

public import Silmaril.Automata.Graph.Defs

/-!
# Dominator-tree problems: proofs

The immediate-dominator tree is exact, exact trees are unique on reachable nodes, and sound
trees are not unique.
-/

@[expose] public section

namespace Silmaril.Proofs.Automata.Graph

open Silmaril.Machine.Graph Silmaril.Automata.Graph

variable {g : Digraph}

theorem ancestor_cases {p : Parent} {c b a : Nat} (h : Ancestor p c b) (hp : p b = some a) :
    c = a ∨ Ancestor p c a := by
  cases h with
  | parent h' => rw [hp] at h'; cases h'; exact Or.inl rfl
  | up h' hrest => rw [hp] at h'; cases h'; exact Or.inr hrest

theorem ancestor_idom_sdom {a b : Nat} (h : Ancestor g.idom a b) : g.StrictlyDominates a b := by
  induction h with
  | parent hp => exact Digraph.idom_strictlyDominates hp
  | up hp _ ih =>
    have hbc := Digraph.idom_strictlyDominates hp
    have hc := Digraph.reachable_of_idom hp
    refine ⟨ih.1.trans hbc.1, fun hac => ?_⟩
    subst hac
    exact hbc.2 (Digraph.Dominates.antisymm hc hbc.1 ih.1)

theorem sdom_ancestor_idom : ∀ (n : Nat) (a b : Nat), g.domDepth b ≤ n → g.Reachable b →
    g.StrictlyDominates a b → Ancestor g.idom a b
  | n, a, b, hn, hb, hab => by
    have hne : b ≠ g.entry := by
      intro he; subst he
      exact hab.2 (Digraph.Dominates.eq_entry hab.1)
    obtain ⟨c, hc, hcb, hmax⟩ := Digraph.idom_spec hb hne
    have hac : g.Dominates a c := hmax a hab
    by_cases h : a = c
    · subst h; exact .parent hc
    · have hcr : g.Reachable c := Digraph.Dominates.reachable hb hcb.1
      have hlt := Digraph.domDepth_lt_of_idom hc
      cases n with
      | zero => omega
      | succ n =>
        exact .up hc (sdom_ancestor_idom n a c (by omega) hcr ⟨hac, h⟩)

theorem idom_exact (g : Digraph) : DomExact g g.idom := fun a b hb =>
  ⟨ancestor_idom_sdom, sdom_ancestor_idom _ a b (Nat.le_refl _) hb⟩

theorem idom_sound (g : Digraph) : DomSound g g.idom := by
  refine ⟨Digraph.idom_none_entry g, fun b hb hne => ?_⟩
  obtain ⟨a, ha, hab, -⟩ := Digraph.idom_spec hb hne
  exact ⟨a, ha, hab⟩

/-- An exact tree is the immediate-dominator tree on reachable nodes. -/
theorem exact_eq_idom {p : Parent} (hp : DomExact g p) {b : Nat} (hb : g.Reachable b) :
    p b = g.idom b := by
  by_cases hne : b = g.entry
  · subst hne
    rw [Digraph.idom_none_entry]
    cases h : p g.entry with
    | none => rfl
    | some a =>
      exfalso
      have := (hp a g.entry hb).mp (.parent h)
      exact this.2 (Digraph.Dominates.eq_entry this.1)
  · obtain ⟨i, hi, hib, himax⟩ := Digraph.idom_spec hb hne
    rw [hi]
    -- the entry is an ancestor, so `b` has a parent
    have hent : Ancestor p g.entry b := (hp _ _ hb).mpr ⟨Digraph.Dominates.entry g b, fun h => hne h.symm⟩
    obtain ⟨a, ha⟩ : ∃ a, p b = some a := by
      cases hent with
      | parent h => exact ⟨_, h⟩
      | up h _ => exact ⟨_, h⟩
    have hab : g.StrictlyDominates a b := (hp a b hb).mp (.parent ha)
    have har : g.Reachable a := Digraph.Dominates.reachable hb hab.1
    -- every strict dominator of `b` dominates `a`
    have hia : g.Dominates i a := by
      rcases ancestor_cases ((hp i b hb).mpr hib) ha with h | h
      · rw [h]; exact Digraph.Dominates.refl g a
      · exact ((hp i a har).mp h).1
    have hai : g.Dominates a i := himax a hab
    rw [ha, Digraph.Dominates.antisymm har hia hai]

/-- **Exact dominator trees are unique on reachable nodes.** -/
theorem exact_unique {p q : Parent} (hp : DomExact g p) (hq : DomExact g q) {b : Nat}
    (hb : g.Reachable b) : p b = q b := by
  rw [exact_eq_idom hp hb, exact_eq_idom hq hb]

theorem ancestor_transfer {p q : Parent} (hpq : ∀ b, g.Reachable b → p b = q b)
    (hq : ∀ a b, q b = some a → g.Reachable b → g.Reachable a) :
    ∀ {a b}, g.Reachable b → Ancestor p a b → Ancestor q a b := by
  intro a b hb h
  induction h with
  | parent h => rw [hpq _ hb] at h; exact .parent h
  | up h _ ih =>
    rw [hpq _ hb] at h
    exact .up h (ih (hq _ _ h hb))

theorem idom_parent_reachable : ∀ a b, g.idom b = some a → g.Reachable b → g.Reachable a :=
  fun _ _ h hb => Digraph.Dominates.reachable hb (Digraph.idom_strictlyDominates h).1

/-- **The exact-tree problem is a finite check**: a tree is exact iff it agrees with the
immediate-dominator tree on the reachable nodes. -/
theorem domExact_iff {p : Parent} : DomExact g p ↔ ∀ b, g.Reachable b → p b = g.idom b := by
  constructor
  · exact fun hp b hb => exact_eq_idom hp hb
  · intro hpi a b hb
    have hp_reach : ∀ a b, p b = some a → g.Reachable b → g.Reachable a := fun a b h hb =>
      idom_parent_reachable a b (by rw [← hpi b hb]; exact h) hb
    constructor
    · intro h
      exact ancestor_idom_sdom (ancestor_transfer hpi idom_parent_reachable hb h)
    · intro h
      exact ancestor_transfer (fun b hb => (hpi b hb).symm) hp_reach hb
        (sdom_ancestor_idom _ a b (Nat.le_refl _) hb h)

theorem starTree_sound (g : Digraph) : DomSound g (starTree g) := by
  refine ⟨by simp [starTree], fun b hb hne => ⟨g.entry, by simp [starTree, hb, hne], ?_⟩⟩
  exact ⟨Digraph.Dominates.entry g b, fun h => hne h.symm⟩

end Silmaril.Proofs.Automata.Graph

module

public import Silmaril.Logic.Consequence.Translation.Defs
public import Silmaril.Logic.Consequence.Signed.Defs
public import Silmaril.Logic.Institution.Room

/-!
# Multiple-conclusion consequence systems

`MultiSystem C D := System (List C) (List D)`: `M Γ Δ` reads `Γ ⊢ Δ`, a list of antecedents
against a list of succedents. Every law about `System` (order, lattice, pullback, translations)
applies. The intended reading is **conjunction on the left, disjunction on the right**, which is
what the semantic system `multiEntails` says. As with `System`, a raw multi-system carries no
structural rule.

* **Weakening.** The default notion is membership inclusion: `WeakL` (more antecedents),
  `WeakR` (more succedents), `Weak` (both). Order- or multiplicity-sensitive (substructural)
  variants stay opt-in, through `System.MonoWrt` with `List.Sublist` or `List.Subperm`.
* `M.single`: the restriction to singleton succedents, a `System (List C) D`.
* `rightExt R`: the least right-weak extension of a single-conclusion system,
  `Γ ⊢ Δ :↔ ∃ d ∈ Δ, R Γ d`. It is **not** the semantic completion: `multiEntails` can prove
  `⊢ [p, q]` with neither `⊢ p` nor `⊢ q` (`Thms`).
* `posPartAlong e M`: the part of `M` on formulas embedded by an explicit `e : A → C`.
  `posPart` takes `e := Signed.pos`.
* `multiEntails satC satD Γ Δ`: every model of all of `Γ` satisfies some member of `Δ`. With
  `Δ = []` it says that `Γ` has no model (inconsistency); with `Γ = []` it says that the
  disjunction of `Δ` is valid.
* `roomMulti R`: `multiEntails` of a room. `corridorMulti f` translates it along a corridor,
  mapping both sides by the sentence translation.
-/

@[expose] public section

namespace Silmaril.Consequence

open Silmaril.Logic

universe u v w m₁ m₂

/-- Multiple-conclusion systems: lists of antecedents against lists of succedents. -/
abbrev MultiSystem (C : Type u) (D : Type v) := System (List C) (List D)

namespace MultiSystem

variable {C : Type u} {D : Type v} {A : Type w}

/-- Left weakening by membership inclusion. -/
def WeakL (M : MultiSystem C D) : Prop := System.MonoWrt (fun Γ Γ' : List C => Γ ⊆ Γ') M

/-- Right weakening by membership inclusion. -/
def WeakR (M : MultiSystem C D) : Prop := ∀ ⦃Γ : List C⦄ ⦃Δ Δ' : List D⦄, Δ ⊆ Δ' → M Γ Δ → M Γ Δ'

/-- Weakening on both sides (the default, membership-inclusion notion). -/
def Weak (M : MultiSystem C D) : Prop := M.WeakL ∧ M.WeakR

/-- The restriction to singleton succedents. -/
def single (M : MultiSystem C D) : System (List C) D := fun Γ d => M Γ [d]

/-- The part of `M` on formulas embedded by `e`. -/
def posPartAlong (e : A → C) (M : MultiSystem C C) : MultiSystem A A :=
  M.pullback (List.map e) (List.map e)

/-- The positive part of a system over signed formulas. -/
def posPart (M : MultiSystem (Signed A) (Signed A)) : MultiSystem A A := posPartAlong Signed.pos M

end MultiSystem

/-- The least right-weak extension of a single-conclusion system: some succedent follows. -/
def rightExt {C : Type u} {D : Type v} (R : System (List C) D) : MultiSystem C D :=
  fun Γ Δ => ∃ d ∈ Δ, R Γ d

/-- Semantic multiple-conclusion consequence: every model of all antecedents satisfies some
succedent. -/
def multiEntails {Mod : Type w} {C : Type u} {D : Type v} (satC : Mod → C → Prop)
    (satD : Mod → D → Prop) : MultiSystem C D :=
  fun Γ Δ => ∀ m, (∀ c ∈ Γ, satC m c) → ∃ d ∈ Δ, satD m d

/-- Multiple-conclusion consequence in a room. -/
def roomMulti (R : Institution.Room.{w, m₁, m₂}) : MultiSystem R.Sen R.Sen :=
  multiEntails R.Sat R.Sat

/-- A corridor translates multiple-conclusion consequence, mapping both sides. -/
def corridorMulti {R₁ R₂ : Institution.Room.{w, m₁, m₂}} (f : Institution.Corridor R₁ R₂) :
    Translation (roomMulti R₁) (roomMulti R₂) :=
  ⟨List.map f.sen, List.map f.sen, fun Γ Δ h M hM => by
    obtain ⟨d, hd, hs⟩ := h (f.mod.obj M) fun c hc => (f.sat M c).1 (hM _ (List.mem_map_of_mem hc))
    exact ⟨f.sen d, List.mem_map_of_mem hd, (f.sat M d).2 hs⟩⟩

end Silmaril.Consequence

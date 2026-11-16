module

public import Silmaril.Logic.Consequence.Multi.Defs
public import Silmaril.Logic.Consequence.Signed.Thms
public import Silmaril.Logic.Consequence.Translation.Thms

/-!
# Multiple-conclusion consequence systems: laws

**Single and multiple conclusions.** `single_rightExt`: the singleton restriction of
`rightExt R` is `R`. `rightExt_weakR`: `rightExt R` is right-weak. `rightExt_le_iff`: among
right-weak systems it is the least one whose singleton restriction contains `R`.
`rightExt_single_le`: `rightExt M.single ≤ M` for right-weak `M`. `not_rightExt_nil`: it never
proves the empty succedent. `rightExt_ne_multiEntails`: it is not the semantic completion, since
`multiEntails` can prove `⊢ [true, false]` while no single member follows.

**Semantics.** `multiEntails_nil_right`: `Γ ⊢ []` iff `Γ` has no model (empty succedent is
inconsistency of the conjunction). `multiEntails_nil_left`: `⊢ Δ` iff every model satisfies some
member of `Δ` (validity of the disjunction). `multiEntails_weak`: semantic consequence has
membership weakening on both sides. `multiEntails_single`: the singleton restriction is
single-conclusion semantic consequence. `roomMulti_single`: in a room, it is `Room.Entails` from
the members of the list.

**Corridors.** `corridorMulti_id`, `corridorMulti_comp`: translation along corridors respects
identities and composition.

**Positive parts.** `posPartAlong_weak`: restricting along an embedding keeps weakening.
-/

@[expose] public section

namespace Silmaril.Consequence

open Silmaril.Logic CategoryTheory

universe u v w m₁ m₂

variable {C : Type u} {D : Type v}

theorem single_rightExt (R : System (List C) D) : (rightExt R).single = R :=
  funext₂ fun _ _ => propext ⟨fun ⟨_, hd, h⟩ => List.mem_singleton.1 hd ▸ h,
    fun h => ⟨_, List.mem_singleton_self _, h⟩⟩

theorem rightExt_weakR (R : System (List C) D) : (rightExt R).WeakR :=
  fun _ _ _ hΔ ⟨d, hd, h⟩ => ⟨d, hΔ hd, h⟩

theorem rightExt_le_iff {R : System (List C) D} {M : MultiSystem C D} (hM : M.WeakR) :
    rightExt R ≤ M ↔ R ≤ M.single :=
  ⟨fun h Γ d hR => h Γ [d] ⟨d, List.mem_singleton_self d, hR⟩,
    fun h _ _ ⟨d, hd, hR⟩ => hM (fun _ hx => (List.mem_singleton.1 hx) ▸ hd) (h _ d hR)⟩

theorem rightExt_single_le {M : MultiSystem C D} (hM : M.WeakR) : rightExt M.single ≤ M :=
  (rightExt_le_iff hM).2 le_rfl

theorem not_rightExt_nil (R : System (List C) D) (Γ : List C) : ¬ rightExt R Γ [] :=
  fun ⟨_, hd, _⟩ => List.not_mem_nil hd

section Semantics

variable {Mod : Type w} (satC : Mod → C → Prop) (satD : Mod → D → Prop)

theorem multiEntails_nil_right (Γ : List C) :
    multiEntails satC satD Γ [] ↔ ∀ m, ¬ ∀ c ∈ Γ, satC m c := by
  simp [multiEntails]

theorem multiEntails_nil_left (Δ : List D) :
    multiEntails satC satD [] Δ ↔ ∀ m, ∃ d ∈ Δ, satD m d := by
  simp [multiEntails]

theorem multiEntails_weak : (multiEntails satC satD).Weak :=
  ⟨fun _ _ hΓ _ h m hm => h m fun c hc => hm c (hΓ hc),
    fun _ _ _ hΔ h m hm => (h m hm).imp fun _ ⟨hd, hs⟩ => ⟨hΔ hd, hs⟩⟩

theorem multiEntails_single (Γ : List C) (d : D) :
    (multiEntails satC satD).single Γ d ↔ ∀ m, (∀ c ∈ Γ, satC m c) → satD m d := by
  simp [MultiSystem.single, multiEntails]

end Semantics

/-- `rightExt` is not the semantic completion: over the models `Bool`, with `b` satisfied
exactly by `b`, `⊢ [true, false]` holds semantically but neither `⊢ true` nor `⊢ false`. -/
theorem rightExt_ne_multiEntails :
    multiEntails (fun m b : Bool => m = b) (fun m b : Bool => m = b) [] [true, false] ∧
      ¬ rightExt (multiEntails (fun m b : Bool => m = b) (fun m b : Bool => m = b)).single
        [] [true, false] := by
  refine ⟨fun m _ => by cases m <;> simp, fun ⟨d, _, h⟩ => ?_⟩
  cases d
  · exact absurd (h true (by simp)) (by simp)
  · exact absurd (h false (by simp)) (by simp)

theorem roomMulti_single (R : Institution.Room.{w, m₁, m₂}) (Γ : List R.Sen) (φ : R.Sen) :
    (roomMulti R).single Γ φ ↔ R.Entails {ψ | ψ ∈ Γ} φ := by
  simp [roomMulti, MultiSystem.single, multiEntails, Institution.Room.Entails]

theorem corridorMulti_id (R : Institution.Room.{w, m₁, m₂}) :
    corridorMulti (𝟙 R) = Translation.id (roomMulti R) :=
  Translation.ext (funext List.map_id) (funext List.map_id)

theorem corridorMulti_comp {R₁ R₂ R₃ : Institution.Room.{w, m₁, m₂}} (f : R₁ ⟶ R₂)
    (g : R₂ ⟶ R₃) : corridorMulti (f ≫ g) = (corridorMulti f).comp (corridorMulti g) :=
  Translation.ext (funext fun l => by simp [corridorMulti, Translation.comp])
    (funext fun l => by simp [corridorMulti, Translation.comp])

theorem MultiSystem.posPartAlong_weak {A : Type w} {M : MultiSystem C C} (e : A → C)
    (h : M.Weak) : (MultiSystem.posPartAlong e M).Weak :=
  ⟨fun _ _ hΓ _ hm => h.1 (List.map_subset e hΓ) hm,
    fun _ _ _ hΔ hm => h.2 (List.map_subset e hΔ) hm⟩

end Silmaril.Consequence

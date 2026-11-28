module

public import Silmaril.Formats.Sqlite.File.Freeblocks.Defs

@[expose] public section

namespace Silmaril.Proofs.Formats.Sqlite.File.Freeblocks

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.File.Freeblocks

private theorem read_zero (view : File.View) (content fuel : Nat) :
    read? view content fuel 0 = some [] := by
  cases fuel <;> simp [read?]

theorem read_bounded_ordered (view : File.View) (content fuel offset : Nat) (blocks : List Span)
    (decoded : read? view content fuel offset = some blocks) :
    Chain view offset blocks ∧ blocks.Pairwise (fun a b => a.stop ≤ b.start) ∧
      ∀ block ∈ blocks, content ≤ block.start ∧ block.start + 4 ≤ block.stop ∧
        block.stop ≤ view.length ∧ offset ≤ block.start := by
  induction fuel generalizing offset blocks with
  | zero =>
    by_cases done : offset = 0
    · simp [read?, done] at decoded
      subst blocks
      subst offset
      exact ⟨.nil, by simp, by simp⟩
    · simp [read?, done] at decoded
  | succ fuel ih =>
    by_cases done : offset = 0
    · simp [read?, done] at decoded
      subst blocks
      subst offset
      exact ⟨.nil, by simp, by simp⟩
    · cases next : view.be? offset 2 with
      | none => simp [read?, done, next] at decoded
      | some following =>
        cases size : view.be? (offset + 2) 2 with
        | none => simp [read?, done, next, size] at decoded
        | some length =>
          simp only [read?, ite_eq_right done, next, size] at decoded
          split at decoded
          · rename_i bounded
            obtain ⟨rest, readRest, rfl⟩ := Option.map_eq_some_iff.mp decoded
            obtain ⟨chain, ordered, within⟩ := ih following rest readRest
            have above : ∀ span ∈ rest, offset + length ≤ span.start := by
              intro span membership
              rcases bounded.2.2.2 with endMarker | monotone
              · rw [endMarker, read_zero] at readRest
                cases readRest
                simp at membership
              · exact Nat.le_trans monotone (within span membership).2.2.2
            refine ⟨.cons done next size chain, List.pairwise_cons.mpr ⟨above, ordered⟩, ?_⟩
            intro block membership
            rcases List.mem_cons.mp membership with rfl | membership
            · exact ⟨bounded.1, Nat.add_le_add_left bounded.2.1 _, bounded.2.2.1, Nat.le_refl _⟩
            · obtain ⟨lower, nonempty, upper, _⟩ := within block membership
              exact ⟨lower, nonempty, upper, Nat.le_trans (Nat.le_add_right _ _) (above block membership)⟩
          · contradiction

private theorem cover_end (lo hi : Nat) (blocks : List Span) (checked : covers lo hi blocks = true) :
    lo ≤ hi := by
  induction blocks generalizing lo with
  | nil => simp [covers] at checked; simp [checked]
  | cons head rest ih =>
    simp [covers] at checked
    exact Nat.le_trans (checked.1.1 ▸ Nat.le_of_lt checked.1.2) (ih head.stop checked.2)

theorem cover_order (lo hi : Nat) (blocks : List Span) (checked : covers lo hi blocks = true) :
    blocks.Pairwise (fun a b => a.stop ≤ b.start) ∧
      ∀ span ∈ blocks, lo ≤ span.start ∧ span.start < span.stop ∧ span.stop ≤ hi := by
  induction blocks generalizing lo with
  | nil => simp
  | cons head rest ih =>
    simp [covers] at checked
    obtain ⟨⟨start, nonempty⟩, suffix⟩ := checked
    obtain ⟨ordered, bounds⟩ := ih head.stop suffix
    refine ⟨List.pairwise_cons.mpr ⟨fun span present => (bounds span present).1, ordered⟩, ?_⟩
    intro span present
    rcases List.mem_cons.mp present with rfl | present
    · exact ⟨Nat.le_of_eq start.symm, nonempty, cover_end span.stop hi rest suffix⟩
    · obtain ⟨lower, h₁, h₂⟩ := bounds span present
      exact ⟨Nat.le_trans (start ▸ Nat.le_of_lt nonempty) lower, h₁, h₂⟩

private theorem cover_lookup (lo hi : Nat) (blocks : List Span) (checked : covers lo hi blocks = true)
    (index : Nat) (lower : lo ≤ index) (upper : index < hi) :
    ∃ span ∈ blocks, span.start ≤ index ∧ index < span.stop := by
  induction blocks generalizing lo with
  | nil =>
    simp [covers] at checked
    rw [checked] at lower
    exact False.elim ((Nat.not_lt_of_ge lower) upper)
  | cons head rest ih =>
    simp [covers] at checked
    obtain ⟨⟨start, _⟩, suffix⟩ := checked
    by_cases here : index < head.stop
    · exact ⟨head, List.mem_cons_self, start.symm ▸ lower, here⟩
    · obtain ⟨span, member, inside⟩ := ih head.stop suffix (Nat.le_of_not_gt here)
      exact ⟨span, List.mem_cons_of_mem head member, inside⟩

private theorem point_unique (spans : List Span)
    (ordered : spans.Pairwise (fun a b => a.stop ≤ b.start))
    (index : Nat) (first second : Span)
    (firstMem : first ∈ spans) (secondMem : second ∈ spans)
    (firstInside : first.start ≤ index ∧ index < first.stop)
    (secondInside : second.start ≤ index ∧ index < second.stop) :
    first = second := by
  induction spans with
  | nil => simp at firstMem
  | cons head rest ih =>
    obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp firstMem with firstHead | firstTail
    · rcases List.mem_cons.mp secondMem with secondHead | secondTail
      · exact firstHead.trans secondHead.symm
      · rw [firstHead] at firstInside
        exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans (before second secondTail) secondInside.1)) firstInside.2)
    · rcases List.mem_cons.mp secondMem with secondHead | secondTail
      · rw [secondHead] at secondInside
        exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans (before first firstTail) firstInside.1)) secondInside.2)
      · exact ih tail firstTail secondTail

/-- Each byte in an accepted content area has exactly one covering span. -/
theorem cover_partition (lo hi : Nat) (spans : List Span) (checked : covers lo hi spans = true)
    (index : Nat) (lower : lo ≤ index) (upper : index < hi) :
    ∃ span ∈ spans, (span.start ≤ index ∧ index < span.stop) ∧
      ∀ other ∈ spans, (other.start ≤ index ∧ index < other.stop) → other = span := by
  obtain ⟨span, member, inside⟩ := cover_lookup lo hi spans checked index lower upper
  exact ⟨span, member, inside, fun other present contains =>
    point_unique spans (cover_order lo hi spans checked).1 index other span present member contains inside⟩

end Silmaril.Proofs.Formats.Sqlite.File.Freeblocks

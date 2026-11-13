module

public import Silmaril.Wasm.Wac.TargetsT.Defs
public import Silmaril.Wasm.Wac.Types.Thms

/-!
# WAC: typed `targets` on binaries is WIT subtyping

* `fitsB_iff`: the verdict is `Sub` of the component's kind and the world's;
* `fitsB_iff_items`: item by item: every import of the component has an item of the same name
  among the world's imports at a supertype, and every export of the world one among the
  component's exports at a subtype.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.TargetsT

theorem fitsB_iff (ci ce wi we : Externs) :
    fitsB ci ce wi we = true ↔ Sub (.comp none ci ce) (.comp none (promoteEx wi) (promoteEx we)) :=
  sub_iff _ _

theorem anyMatch_iff (as : Externs) (k : String) (b : Kind) :
    anyMatch as k b = true ↔ ∃ a, (k, a) ∈ as ∧ sub a b = true := by
  induction as with
  | nil => simp [anyMatch]
  | cons p as ih =>
    obtain ⟨k', a⟩ := p
    simp only [anyMatch, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ih, List.mem_cons,
      Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, h⟩ | ⟨a', h, h'⟩)
      · exact ⟨a, .inl ⟨rfl, rfl⟩, h⟩
      · exact ⟨a', .inr h, h'⟩
    · rintro ⟨a', (⟨rfl, rfl⟩ | h), h'⟩
      · exact .inl ⟨rfl, h'⟩
      · exact .inr ⟨a', h, h'⟩

theorem subEx_iff (as bs : Externs) :
    subEx as bs = true ↔ ∀ k b, (k, b) ∈ bs → ∃ a, (k, a) ∈ as ∧ sub a b = true := by
  induction bs with
  | nil => simp [subEx]
  | cons p bs ih =>
    obtain ⟨k, b⟩ := p
    simp only [subEx, Bool.and_eq_true, anyMatch_iff, ih, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ⟨h₁, h₂⟩ k' b' (⟨rfl, rfl⟩ | h)
      · exact h₁
      · exact h₂ k' b' h
    · intro h
      exact ⟨h k b (.inl ⟨rfl, rfl⟩), fun k' b' h' => h k' b' (.inr h')⟩

/-- **Typed targets, item by item.** -/
theorem fitsB_iff_items (ci ce wi we : Externs) :
    fitsB ci ce wi we = true ↔
      (∀ n k, (n, k) ∈ ci → ∃ k', (n, k') ∈ promoteEx wi ∧ sub k' k = true) ∧
      (∀ n k, (n, k) ∈ promoteEx we → ∃ k', (n, k') ∈ ce ∧ sub k' k = true) := by
  simp only [fitsB, sub, Bool.and_eq_true, subEx_iff]

end Silmaril.Wasm.Wac.TargetsT

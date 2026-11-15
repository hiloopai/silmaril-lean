module

public import Silmaril.Games.Abstract.FullFun.Defs
public import Silmaril.Games.Abstract.HostRunInf.Thms

/-!
# Full observations: host preservation of sequencing (proofs)

`hostObsInf_seq`: against a relational host, the productive observations of `f ; g` are the
productive observations of `f`, or a finished return of `f` with a consistent log followed by
a productive observation of `g`. Consistency of the joined stream splits exactly into the
prefix and the tail.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.FullFun

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {E : Sig.{u}} {S A B C : Type u}

theorem append_get_lt {α : Type u} (c : List α) (ω : Nat → α) {n : Nat} (h : n < c.length) :
    (c ++ₛ ω) n = c[n] := by
  induction c generalizing n with
  | nil => simp at h
  | cons x c ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih (by simpa using h)

theorem append_get_ge {α : Type u} (c : List α) (ω : Nat → α) (n : Nat) :
    (c ++ₛ ω) (c.length + n) = ω n := by
  induction c with
  | nil => simp [Stream'.appendStream']
  | cons x c ih =>
    rw [List.length_cons, Nat.add_right_comm]
    exact ih

/-- **Consistency of a joined stream** splits into the prefix and the tail. -/
theorem consistent_append {R : HostRel E} (c : List (Call E)) (ω : Nat → Call E) :
    (∀ n, R ((c ++ₛ ω) n).1 (.answer ((c ++ₛ ω) n).2)) ↔
      R.Consistent c ∧ ∀ n, R (ω n).1 (.answer (ω n).2) := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun n => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have := h i
      rwa [append_get_lt c ω hi] at this
    · have := h (c.length + n)
      rwa [append_get_ge] at this
  · rintro ⟨hc, hω⟩ n
    by_cases hn : n < c.length
    · rw [append_get_lt c ω hn]
      exact hc _ (List.getElem_mem hn)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hn)
      rw [append_get_ge]
      exact hω k

/-- **Host preservation of sequencing** (productive part). -/
theorem hostObsInf_seq {R : HostRel E} (f : FullFun E S A B) (g : FullFun E S B C) (s : S)
    (a : A) (ω : Nat → Call E) :
    ω ∈ hostObsInf R (FullFun.seq f g).2 s a ↔
      ω ∈ hostObsInf R f.2 s a ∨
        ∃ (c : List (Call E)) (b : B) (s₁ : S) (ω' : Nat → Call E),
          (c, End.ret b s₁) ∈ f.1 s a ∧ R.Consistent c ∧ ω' ∈ hostObsInf R g.2 s₁ b ∧
          ω = c ++ₛ ω' := by
  constructor
  · rintro ⟨hm | ⟨c, b, s₁, ω', hf, hg, rfl⟩, hc⟩
    · exact .inl ⟨hm, hc⟩
    · obtain ⟨hc₁, hc₂⟩ := (consistent_append c ω').mp hc
      exact .inr ⟨c, b, s₁, ω', hf, hc₁, ⟨hg, hc₂⟩, rfl⟩
  · rintro (⟨hm, hc⟩ | ⟨c, b, s₁, ω', hf, hc₁, ⟨hg, hc₂⟩, rfl⟩)
    · exact ⟨.inl hm, hc⟩
    · exact ⟨.inr ⟨c, b, s₁, ω', hf, hg, rfl⟩, (consistent_append c ω').mpr ⟨hc₁, hc₂⟩⟩

/-- The identity has no productive run. -/
theorem pure_inf (s : S) (a : A) : (FullFun.pure : FullFun E S A A).2 s a = ∅ := rfl

/-- Sequencing after the identity keeps the productive runs. -/
theorem pure_seq_inf (g : FullFun E S A B) (s : S) (a : A) :
    (FullFun.seq FullFun.pure g).2 s a = g.2 s a := by
  ext ω
  simp only [FullFun.seq, FullFun.pure, Set.mem_union, Set.mem_empty_iff_false, false_or,
    Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq, End.ret.injEq]
  constructor
  · rintro ⟨c, b, s₁, ω', ⟨rfl, rfl, rfl⟩, hg, rfl⟩
    exact hg
  · intro h
    exact ⟨[], a, s, ω, ⟨rfl, rfl, rfl⟩, h, rfl⟩

end Silmaril.Proofs.Games.Abstract.FullFun

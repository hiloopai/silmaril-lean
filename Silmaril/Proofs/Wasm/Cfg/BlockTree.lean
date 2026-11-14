module

public import Silmaril.Wasm.Cfg.BlockTree.Defs

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.BlockTree

open Silmaril.Wasm Silmaril.Wasm.Cfg

mutual
theorem walk_prefix (path : List SeqStep) (k : Nat) (acc : List Instr) :
    ∀ (is : List Instr), ∀ x ∈ walk path k acc is, path <+: x.1.seq
  | [], x, hx => by
    unfold walk at hx
    split at hx
    · simp at hx
    · simp at hx; subst hx; exact List.prefix_refl _
  | i :: is, x, hx => by
    unfold walk at hx
    split at hx
    · simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact List.prefix_refl _
      · obtain ⟨s, hs⟩ := nested_prefix path k i x hx
        exact (List.prefix_append _ _).trans hs
      · exact walk_prefix path (k + 1) [] is x hx
    · exact walk_prefix path k (i :: acc) is x hx
theorem nested_prefix (path : List SeqStep) (k : Nat) :
    ∀ (i : Instr), ∀ x ∈ nested path k i, ∃ s, path ++ [s] <+: x.1.seq
  | .block _ b, x, hx => ⟨_, walk_prefix _ 0 [] b x (by simpa [nested] using hx)⟩
  | .loop _ b, x, hx => ⟨_, walk_prefix _ 0 [] b x (by simpa [nested] using hx)⟩
  | .tryTable _ _ b, x, hx => ⟨_, walk_prefix _ 0 [] b x (by simpa [nested] using hx)⟩
  | .if_ _ t e, x, hx => by
    simp only [nested, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ⟨_, walk_prefix _ 0 [] t x hx⟩
    · exact ⟨_, walk_prefix _ 0 [] e x hx⟩
  | i, x, hx => by
    rw [nested.eq_def] at hx
    split at hx
    all_goals first
      | exact ⟨_, walk_prefix _ 0 [] _ x hx⟩
      | (rw [List.mem_append] at hx
         exact hx.elim (fun h => ⟨_, walk_prefix _ 0 [] _ x h⟩)
           (fun h => ⟨_, walk_prefix _ 0 [] _ x h⟩))
      | simp at hx
end

theorem nested_ne (path : List SeqStep) (k : Nat) (i : Instr) :
    ∀ x ∈ nested path k i, x.1.seq ≠ path := by
  intro x hx h
  obtain ⟨s, hs⟩ := nested_prefix path k i x hx
  have := hs.length_le
  rw [h] at this; simp only [List.length_append, List.length_singleton] at this; omega

/-- The blocks `walk` lists at its own sequence path are exactly that sequence's segmentation,
numbered from `k`. -/
theorem walk_top (path : List SeqStep) :
    ∀ (is : List Instr) (k : Nat) (acc : List Instr),
      (walk path k acc is).filter (fun x => x.1.seq == path) =
        (segmentAux acc is).mapIdx fun j s => (⟨path, k + j⟩, s)
  | [], k, acc => by
    unfold walk segmentAux
    split <;> simp
  | i :: is, k, acc => by
    unfold walk segmentAux
    split
    · have hn : (nested path k i).filter (fun x => x.1.seq == path) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx; simpa using nested_ne path k i x hx
      simp only [List.filter_cons, List.filter_append, hn, beq_self_eq_true, ite_true,
        List.nil_append, walk_top path is (k + 1) [], List.mapIdx_cons, Nat.add_zero]
      congr 1
      apply List.ext_getElem (by simp)
      intro n _ _; simp [Nat.add_assoc, Nat.add_comm 1 n]
    · exact walk_top path is k (i :: acc)

end Silmaril.Wasm.Cfg.Proofs.BlockTree

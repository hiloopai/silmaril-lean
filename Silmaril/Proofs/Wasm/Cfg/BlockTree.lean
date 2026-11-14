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

/-- `walk` is the pre-order traversal of the segmentation it computes. -/
theorem walk_eq (path : List SeqStep) :
    ∀ (is : List Instr) (k : Nat) (acc : List Instr),
      walk path k acc is = ((segmentAux acc is).zipIdx k).flatMap
        fun p => (⟨path, p.2⟩, p.1) :: (p.1.term.map (nested path p.2)).getD []
  | [], k, acc => by
    unfold walk segmentAux
    split <;> simp
  | i :: is, k, acc => by
    unfold walk segmentAux
    split
    · rw [walk_eq path is (k + 1) []]
      simp [List.zipIdx_cons]
    · exact walk_eq path is k (i :: acc)

theorem mem_nested (path : List SeqStep) (m : Nat) (t : Instr) (x : BlockId × Segment) :
    x ∈ nested path m t ↔ ∃ a c, armOf t a = some c ∧ x ∈ walk (path ++ [(m, a)]) 0 [] c := by
  constructor
  · intro hx
    cases t <;> simp only [nested, List.mem_append, List.not_mem_nil] at hx
    all_goals first
      | exact ⟨0, _, rfl, hx⟩
      | (rcases hx with hx | hx
         · exact ⟨0, _, rfl, hx⟩
         · exact ⟨1, _, rfl, hx⟩)
  · rintro ⟨a, c, ha, hx⟩
    cases t <;> rcases a with _ | _ | a <;> simp [armOf] at ha <;> subst ha <;> simp [nested, hx]

/-- **Every block `walk` lists is the one `blockAt` names**, and conversely. -/
theorem mem_walk (path : List SeqStep) (q : List SeqStep) :
    ∀ (is : List Instr) (k : Nat) (acc : List Instr) (j : Nat) (s : Segment),
      (⟨path ++ q, j⟩, s) ∈ walk path k acc is ↔ blockAt (segmentAux acc is) k q j = some s := by
  induction q generalizing path with
  | nil =>
    intro is k acc j s
    rw [walk_eq]
    simp only [List.append_nil, List.mem_flatMap, List.mem_cons, blockAt]
    constructor
    · rintro ⟨⟨seg, m⟩, hm, h | h⟩
      · simp only [Prod.mk.injEq, BlockId.mk.injEq] at h
        obtain ⟨⟨-, rfl⟩, rfl⟩ := h
        rw [List.mem_zipIdx_iff_le_and_getElem?_sub] at hm
        simpa [hm.1] using hm.2
      · exfalso
        cases ht : seg.term with
        | none => simp [ht] at h
        | some t =>
          simp only [ht, Option.map_some, Option.getD_some] at h
          exact nested_ne path m t _ h rfl
    · intro h
      split at h
      · refine ⟨(s, j), ?_, Or.inl rfl⟩
        rw [List.mem_zipIdx_iff_le_and_getElem?_sub]; exact ⟨by assumption, h⟩
      · simp at h
  | cons st q ih =>
    obtain ⟨m, a⟩ := st
    intro is k acc j s
    rw [walk_eq]
    simp only [List.mem_flatMap, List.mem_cons, blockAt]
    constructor
    · rintro ⟨⟨seg, m'⟩, hm, h | h⟩
      · simp at h
      · rw [List.mem_zipIdx_iff_le_and_getElem?_sub] at hm
        cases ht : seg.term with
        | none => simp [ht] at h
        | some t =>
          simp only [ht, Option.map_some, Option.getD_some] at h
          obtain ⟨a', c, ha, hx⟩ := (mem_nested path m' t _).1 h
          have hp := walk_prefix _ 0 [] c _ hx
          simp only [List.prefix_append_right_inj, List.cons_prefix_cons, Prod.mk.injEq] at hp
          obtain ⟨⟨rfl, rfl⟩, -⟩ := hp
          rw [show path ++ (m', a') :: q = (path ++ [(m', a')]) ++ q by simp] at hx
          rw [ih] at hx
          simp only at hm
          simp [hm.1, hm.2, ht, ha, segment, hx]
    · intro h
      split at h
      · rename_i hk
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨seg, hseg, t, ht, c, hc, h⟩ := h
        refine ⟨(seg, m), ?_, Or.inr ?_⟩
        · rw [List.mem_zipIdx_iff_le_and_getElem?_sub]; exact ⟨hk, hseg⟩
        · simp only [ht, Option.map_some, Option.getD_some]
          refine (mem_nested path m t _).2 ⟨a, c, hc, ?_⟩
          rw [show path ++ (m, a) :: q = (path ++ [(m, a)]) ++ q by simp, ih]
          simpa [segment] using h
      · simp at h

end Silmaril.Wasm.Cfg.Proofs.BlockTree

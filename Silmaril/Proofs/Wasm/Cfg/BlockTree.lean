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

/-! ## Block identities are distinct -/

theorem step_eq {path s : List SeqStep} {x y : SeqStep} (hx : path ++ [x] <+: s)
    (hy : path ++ [y] <+: s) : x = y := by
  have h1 := hx.getElem (i := path.length) (by simp)
  have h2 := hy.getElem (i := path.length) (by simp)
  simpa using h1.trans h2.symm

theorem ne_of_step {path s : List SeqStep} {x : SeqStep} (hx : path ++ [x] <+: s) : s ≠ path := by
  intro h; have := hx.length_le; rw [h] at this; simp at this; omega

theorem mem_nested_step (path : List SeqStep) (m : Nat) (t : Instr) (x : BlockId × Segment)
    (hx : x ∈ nested path m t) : ∃ a, path ++ [(m, a)] <+: x.1.seq := by
  obtain ⟨a, c, -, h⟩ := (mem_nested path m t x).1 hx
  exact ⟨a, walk_prefix _ 0 [] c x h⟩

/-- The identities `walk` lists from position `k`: blocks of its own sequence at positions `≥ k`,
or blocks below a segment at a position `≥ k`. -/
theorem walk_shape (path : List SeqStep) :
    ∀ (is : List Instr) (k : Nat) (acc : List Instr), ∀ x ∈ walk path k acc is,
      (x.1.seq = path ∧ k ≤ x.1.idx) ∨ ∃ m a, k ≤ m ∧ path ++ [(m, a)] <+: x.1.seq
  | [], k, acc, x, hx => by
    unfold walk at hx
    split at hx
    · simp at hx
    · simp at hx; subst hx; simp
  | i :: is, k, acc, x, hx => by
    unfold walk at hx
    split at hx
    · simp only [List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · simp
      · obtain ⟨a, h⟩ := mem_nested_step path k i x hx
        exact Or.inr ⟨k, a, le_rfl, h⟩
      · rcases walk_shape path is (k + 1) [] x hx with ⟨h1, h2⟩ | ⟨m, a, h1, h2⟩
        · exact Or.inl ⟨h1, by omega⟩
        · exact Or.inr ⟨m, a, by omega, h2⟩
    · exact walk_shape path is k (i :: acc) x hx

theorem arms_nodup (path : List SeqStep) (k : Nat) (t e : List Instr)
    (ht : ((walk (path ++ [(k, 0)]) 0 [] t).map (·.1)).Nodup)
    (he : ((walk (path ++ [(k, 1)]) 0 [] e).map (·.1)).Nodup) :
    ((walk (path ++ [(k, 0)]) 0 [] t).map (·.1) ++
      (walk (path ++ [(k, 1)]) 0 [] e).map (·.1)).Nodup := by
  rw [List.nodup_append]
  refine ⟨ht, he, ?_⟩
  simp only [List.mem_map]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
  have h1 := walk_prefix _ 0 [] t x hx
  have h2 := walk_prefix _ 0 [] e y hy
  rw [h] at h1
  have := step_eq h1 h2; simp at this

mutual
theorem walk_nodup (path : List SeqStep) (k : Nat) (acc : List Instr) :
    ∀ (is : List Instr), ((walk path k acc is).map (·.1)).Nodup
  | [] => by
    unfold walk; split <;> simp
  | i :: is => by
    unfold walk
    split
    · simp only [List.map_cons, List.map_append, List.nodup_cons, List.nodup_append,
        List.mem_append, List.mem_map, not_or, not_exists, not_and]
      refine ⟨⟨?_, ?_⟩, nested_nodup path k i, walk_nodup path (k + 1) [] is, ?_⟩
      · intro x hx h
        obtain ⟨a, ha⟩ := mem_nested_step path k i x hx
        exact ne_of_step ha (by rw [h])
      · intro x hx h
        rcases walk_shape path is (k + 1) [] x hx with ⟨_, h2⟩ | ⟨m, a, h1, h2⟩
        · rw [h] at h2; simp at h2; omega
        · rw [h] at h2; exact ne_of_step h2 rfl
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
        obtain ⟨a, ha⟩ := mem_nested_step path k i x hx
        rw [h] at ha
        rcases walk_shape path is (k + 1) [] y hy with ⟨h1, _⟩ | ⟨m, b, h1, h2⟩
        · exact ne_of_step ha h1
        · have := step_eq ha h2; simp at this; omega
    · exact walk_nodup path k (i :: acc) is
theorem nested_nodup (path : List SeqStep) (k : Nat) :
    ∀ (i : Instr), ((nested path k i).map (·.1)).Nodup
  | .block _ b => by simpa [nested] using walk_nodup (path ++ [(k, 0)]) 0 [] b
  | .loop _ b => by simpa [nested] using walk_nodup (path ++ [(k, 0)]) 0 [] b
  | .tryTable _ _ b => by simpa [nested] using walk_nodup (path ++ [(k, 0)]) 0 [] b
  | .if_ _ t e => by
    simpa [nested] using arms_nodup path k t e (walk_nodup _ 0 [] t) (walk_nodup _ 0 [] e)
  | i => by
    rw [nested.eq_def]
    split
    all_goals first
      | (simp; done)
      | exact walk_nodup _ 0 [] _
      | (simp only [List.map_append]; exact arms_nodup path k _ _ (walk_nodup _ 0 [] _) (walk_nodup _ 0 [] _))
end

end Silmaril.Wasm.Cfg.Proofs.BlockTree

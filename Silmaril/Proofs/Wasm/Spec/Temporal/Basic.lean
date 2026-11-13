module

public import Silmaril.Wasm.Spec.Temporal.Defs

@[expose] public section

/-!
# Temporal logics: proofs

Positions of finite traces and infinite words, the meaning of `□ A` in each reading of LTL, and
the decomposition of a good trace set into maximal behaviours (`exists_maximal_or_limit`: every
trace extends to a maximal finite trace or lies on an infinite limit). Summary in
`Silmaril.Wasm.Spec.Temporal.Thms`.
-/

namespace Silmaril.Wasm.Spec

variable {α : Type}

/-! ## Positions -/

/-- `EveryPos` by indices. -/
theorem everyPos_iff_get {P : List α → α → Prop} {t : List α} :
    EveryPos P t ↔ ∀ k (hk : k < t.length), P (t.take k) (t.get ⟨k, hk⟩) := by
  constructor
  · intro h k hk
    have hdec : t = t.take k ++ t[k] :: t.drop (k + 1) := by
      rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
    exact h _ _ _ hdec
  · rintro h hs e r rfl
    have hk : hs.length < (hs ++ e :: r).length := by simp
    have he : (hs ++ e :: r).get ⟨hs.length, hk⟩ = e := List.getElem_of_append rfl rfl
    have := h hs.length hk
    rwa [List.take_left, he] at this

/-- A predicate of events alone holds everywhere iff it holds of every event. -/
theorem everyPos_iff_mem {Q : α → Prop} {t : List α} :
    EveryPos (fun _ e => Q e) t ↔ ∀ e ∈ t, Q e := by
  constructor
  · intro h e he
    obtain ⟨hs, r, rfl⟩ := List.append_of_mem he
    exact h hs e r rfl
  · rintro h hs e r rfl
    exact h e (by simp)

/-- The prefix of length `n + 1` of a word. -/
theorem prefixList_succ (w : ℕ → α) (n : ℕ) : prefixList w (n + 1) = prefixList w n ++ [w n] :=
  List.ofFn_succ_last

@[simp] theorem length_prefixList (w : ℕ → α) (n : ℕ) : (prefixList w n).length = n := by
  simp [prefixList]

/-! ## `□` in each reading -/

namespace LTL

/-- `□ φ` on a finite trace. -/
theorem holdsFin_alw {t : List α} {k : ℕ} {φ : LTL α} :
    HoldsFin t k (alw φ) ↔ ∀ j, k ≤ j → j < t.length → HoldsFin t j φ := by
  simp only [alw, ev, HoldsFin, implies_true, and_true, not_exists, not_and,
    not_not]

/-- `□ φ` on an infinite word. -/
theorem holdsInf_alw {w : ℕ → α} {k : ℕ} {φ : LTL α} :
    HoldsInf w k (alw φ) ↔ ∀ j, k ≤ j → HoldsInf w j φ := by
  simp only [alw, ev, HoldsInf, implies_true, and_true, not_exists, not_and,
    not_not]

/-- `□ A` on a finite trace is `A` at every position. -/
theorem holdsFin_alw_atom {t : List α} {p : List α → α → Prop} :
    HoldsFin t 0 (alw (atom p)) ↔ EveryPos p t := by
  rw [holdsFin_alw, everyPos_iff_get]
  constructor
  · intro h k hk
    obtain ⟨_, hp⟩ := h k (Nat.zero_le k) hk
    exact hp
  · intro h j _ hj
    exact ⟨hj, h j hj⟩

/-- `□ A` on an infinite word is `A` at every position. -/
theorem holdsInf_alw_atom {w : ℕ → α} {p : List α → α → Prop} :
    HoldsInf w 0 (alw (atom p)) ↔ ∀ j, p (prefixList w j) (w j) := by
  rw [holdsInf_alw]
  exact ⟨fun h j => h j (Nat.zero_le j), fun h j _ => h j⟩

end LTL

/-- `A` everywhere on the prefixes of a word is `A` at every position of the word. -/
theorem everyPos_prefixList_iff {w : ℕ → α} {p : List α → α → Prop} :
    (∀ n, EveryPos p (prefixList w n)) ↔ ∀ j, p (prefixList w j) (w j) := by
  constructor
  · intro h j
    exact h (j + 1) _ _ [] (by rw [prefixList_succ])
  · intro h n
    rw [everyPos_iff_get]
    intro k hk
    have hk' : k < n := by simpa using hk
    have htake : (prefixList w n).take k = prefixList w k :=
      List.ext_getElem (by simp; omega) fun i _ _ => by simp [prefixList]
    have hget : (prefixList w n).get ⟨k, hk⟩ = w k := by simp [prefixList]
    rw [htake, hget]
    exact h k

/-! ## Maximal behaviours of good trace sets -/

section Chain

variable {T : Set (List α)} {t : List α}

/-- A chain of ever longer traces of `T` above `t`, when no trace above `t` is maximal. -/
noncomputable def extChain (hT : t ∈ T)
    (step : ∀ u : {u // t <+: u ∧ u ∈ T}, {e // u.1 ++ [e] ∈ T}) :
    ℕ → {u // t <+: u ∧ u ∈ T}
  | 0 => ⟨t, List.prefix_refl t, hT⟩
  | n + 1 =>
    ⟨(extChain hT step n).1 ++ [(step (extChain hT step n)).1],
      (extChain hT step n).2.1.trans (List.prefix_append _ _), (step (extChain hT step n)).2⟩

variable (hT : t ∈ T) (step : ∀ u : {u // t <+: u ∧ u ∈ T}, {e // u.1 ++ [e] ∈ T})

theorem extChain_length (n : ℕ) : (extChain hT step n).1.length = t.length + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ((extChain hT step n).1 ++ _).length = _
    rw [List.length_append, ih]
    rfl

theorem extChain_mono {n m : ℕ} (h : n ≤ m) : (extChain hT step n).1 <+: (extChain hT step m).1 := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (List.prefix_append _ _)

/-- The limit word of the chain. -/
noncomputable def extWord (k : ℕ) : α :=
  (extChain hT step (k + 1)).1[k]'(by rw [extChain_length]; omega)

theorem extWord_prefix (n : ℕ) : prefixList (extWord hT step) n = (extChain hT step n).1.take n := by
  refine List.ext_getElem (by simp [extChain_length]) fun i h₁ h₂ => ?_
  have hi : i < n := by simpa using h₁
  have hlen : i < (extChain hT step (i + 1)).1.length := by rw [extChain_length]; omega
  have hmono := extChain_mono hT step (Nat.succ_le_of_lt hi)
  simp only [prefixList, List.getElem_ofFn, List.getElem_take, extWord]
  exact List.IsPrefix.getElem hmono hlen

end Chain

/-- **Every trace of a good set extends to a maximal finite trace or lies on an infinite
limit.** -/
theorem exists_maximal_or_limit {T : Set (List α)} (hG : Good T) {t : List α} (ht : t ∈ T) :
    (∃ u, t <+: u ∧ Maximal T u) ∨ ∃ w ∈ limits T, prefixList w t.length = t := by
  by_cases hmax : ∃ u, t <+: u ∧ Maximal T u
  · exact .inl hmax
  · right
    have hext : ∀ u : {u // t <+: u ∧ u ∈ T}, ∃ e, u.1 ++ [e] ∈ T := by
      intro u
      by_contra hno
      exact hmax ⟨u.1, u.2.1, u.2.2, fun e he => hno ⟨e, he⟩⟩
    let step : ∀ u : {u // t <+: u ∧ u ∈ T}, {e // u.1 ++ [e] ∈ T} :=
      fun u => ⟨(hext u).choose, (hext u).choose_spec⟩
    refine ⟨extWord ht step, fun n => ?_, ?_⟩
    · rw [extWord_prefix]
      exact hG.of_prefix (extChain ht step n).2.2 (List.take_prefix _ _)
    · rw [extWord_prefix]
      exact List.prefix_iff_eq_take.1 (extChain ht step t.length).2.1 |>.symm

end Silmaril.Wasm.Spec

namespace Silmaril.Wasm.Spec

variable {α : Type}

/-- The maximal prefixes of a list: the list itself. -/
theorem maximal_prefixesOf_iff {l t : List α} : Maximal (prefixesOf l) t ↔ t = l := by
  constructor
  · rintro ⟨ht, hno⟩
    obtain ⟨r, rfl⟩ := ht
    rcases r with _ | ⟨e, r⟩
    · exact (List.append_nil t).symm
    · exact absurd (show t ++ [e] <+: t ++ e :: r from ⟨r, by simp⟩) (hno e)
  · rintro rfl
    refine ⟨List.prefix_refl t, fun e he => ?_⟩
    have hlen := he.length_le
    simp only [List.length_append, List.length_singleton] at hlen
    omega

/-- The prefixes of a list have no infinite limit. -/
theorem limits_prefixesOf (l : List α) : limits (prefixesOf l) = ∅ := by
  ext w
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hw
  have hlen := (hw (l.length + 1)).length_le
  simp only [length_prefixList] at hlen
  omega

/-- On the prefixes of one trace, maximal-behaviour LTL is finite-trace LTL on the trace. -/
theorem ltlMax_prefixesOf_iff {Ty A R : Type} {X : Iface Ty} (l : List (Event A R X))
    (φ : LTLFm A R X) : (ltlMax Ty A R).Sat (prefixesOf l) φ ↔ LTL.HoldsFin l 0 φ := by
  constructor
  · rintro ⟨-, hfin⟩
    exact hfin l (maximal_prefixesOf_iff.2 rfl)
  · intro h
    refine ⟨fun w hw => ?_, fun t ht => ?_⟩
    · rw [limits_prefixesOf] at hw
      exact absurd hw (Set.notMem_empty w)
    · rw [maximal_prefixesOf_iff.1 ht]
      exact h

end Silmaril.Wasm.Spec

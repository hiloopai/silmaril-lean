module

public import Silmaril.Semantics.Accept.Grammar.Defs

/-! # Proofs: derivations of small grammars

Derivation lemmas behind `Silmaril.Semantics.Accept.Grammar.Thms`: strings without
nonterminals derive only themselves, one-step productions from a single nonterminal, and the
languages of `Grammar.empty`, `Grammar.word w` and `Grammar.nested x y`.
-/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Grammar

open Silmaril.Accept.Grammar

universe u

variable {T : Type u}

theorem not_mem_map_terminal {N : Type} (w : List T) (n : N) :
    Symbol.nonterminal n ∉ w.map (Symbol.terminal : T → Symbol T N) := by
  simp

theorem map_terminal_injective {N : Type} :
    Function.Injective (List.map (Symbol.terminal : T → Symbol T N)) :=
  List.map_injective_iff.2 fun _ _ h => Symbol.terminal.inj h

/-- A string without nonterminals derives only itself. -/
theorem derives_eq_of_forall_not_mem {g : ContextFreeGrammar T} {u v : List (Symbol T g.NT)}
    (hu : ∀ n, Symbol.nonterminal n ∉ u) (h : g.Derives u v) : v = u := by
  rcases h.eq_or_head with h | ⟨w, hw, -⟩
  · exact h.symm
  · obtain ⟨r, -, hr⟩ := hw.exists_nonterminal_input_mem
    exact absurd hr (hu _)

/-- One production step from a single nonterminal applies a rule for it. -/
theorem produces_singleton_iff {g : ContextFreeGrammar T} {n : g.NT}
    {v : List (Symbol T g.NT)} :
    g.Produces [Symbol.nonterminal n] v ↔ ∃ r ∈ g.rules, r.input = n ∧ v = r.output := by
  constructor
  · rintro ⟨r, hr, h⟩
    obtain ⟨p, q, h1, rfl⟩ := ContextFreeRule.rewrites_iff.1 h
    cases p with
    | nil =>
      simp only [List.nil_append, List.singleton_append, List.cons.injEq,
        Symbol.nonterminal.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨r, hr, rfl, by simp⟩
    | cons a p => simp at h1
  · rintro ⟨r, hr, rfl, rfl⟩
    exact ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩

/-- A terminal word is derivable from a single nonterminal only through at least one step. -/
theorem derives_singleton_map_terminal {g : ContextFreeGrammar T} {n : g.NT} {w : List T}
    (h : g.Derives [Symbol.nonterminal n] (w.map Symbol.terminal)) :
    ∃ r ∈ g.rules, r.input = n ∧ g.Derives r.output (w.map Symbol.terminal) := by
  rcases h.eq_or_head with h | ⟨v, hv, hd⟩
  · exact absurd (h ▸ List.mem_singleton_self _) (not_mem_map_terminal w n)
  · obtain ⟨r, hr, hi, rfl⟩ := produces_singleton_iff.1 hv
    exact ⟨r, hr, hi, hd⟩

theorem lang_empty : lang (empty : ContextFreeGrammar T) = ∅ := by
  ext w
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨r, hr, -⟩ := derives_singleton_map_terminal (g := empty) h
  exact Finset.notMem_empty r hr

theorem mem_word_rules {w : List T} {r : ContextFreeRule T Unit} :
    r ∈ (word w).rules ↔ r = ⟨(), w.map Symbol.terminal⟩ :=
  Finset.mem_singleton

theorem lang_word (w : List T) : lang (word w) = {w} := by
  ext w'
  simp only [Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨r, hr, -, hd⟩ := derives_singleton_map_terminal (g := word w) h
    obtain rfl := mem_word_rules.1 hr
    exact map_terminal_injective (derives_eq_of_forall_not_mem (not_mem_map_terminal w) hd)
  · rintro rfl
    exact ContextFreeGrammar.Produces.single
      ⟨_, Finset.mem_singleton_self _, ContextFreeRule.Rewrites.input_output⟩

/-! ## The nested grammar `S → x S y | ε` -/

section Nested

variable (x y : T)

/-- `n` copies of the terminal `a`, as a string of the nested grammar. -/
abbrev reps (n : ℕ) (a : T) : List (Symbol T Unit) := List.replicate n (Symbol.terminal a)

/-- The sentential forms of the nested grammar: `xⁿ S yⁿ` or `xⁿ yⁿ`. -/
def NestedForm (s : List (Symbol T Unit)) : Prop :=
  ∃ n, s = reps n x ++ Symbol.nonterminal () :: reps n y ∨ s = reps n x ++ reps n y

theorem mem_nested_rules {r : ContextFreeRule T Unit} :
    r ∈ (nested x y).rules ↔ r = nestedStep x y ∨ r = nestedStop := by
  simp

theorem not_mem_reps (n : ℕ) (a : T) : Symbol.nonterminal () ∉ reps n a := by
  simp [List.mem_replicate]

theorem reps_succ_split (n : ℕ) :
    reps n x ++ ([Symbol.terminal x, Symbol.nonterminal (), Symbol.terminal y] ++ reps n y) =
      reps (n + 1) x ++ Symbol.nonterminal () :: reps (n + 1) y := by
  unfold reps
  rw [List.replicate_succ', List.replicate_succ]
  simp

theorem nestedForm_of_generates {s : List (Symbol T Unit)}
    (h : (nested x y).Derives [Symbol.nonterminal ()] s) : NestedForm x y s := by
  induction h with
  | refl => exact ⟨0, Or.inl rfl⟩
  | tail _ hp ih =>
    obtain ⟨n, hs | hs⟩ := ih
    · obtain ⟨r, hr, hrw⟩ := hp
      obtain ⟨p, q, h1, rfl⟩ := ContextFreeRule.rewrites_iff.1 hrw
      rw [List.append_assoc, List.singleton_append, hs,
        List.append_cons_inj_of_notMem (not_mem_reps n x) (not_mem_reps n y)] at h1
      obtain ⟨rfl, -, rfl⟩ := h1
      rcases (mem_nested_rules x y).1 hr with rfl | rfl
      · exact ⟨n + 1, Or.inl (by rw [List.append_assoc]; exact reps_succ_split x y n)⟩
      · exact ⟨n, Or.inr (by simp [nestedStop])⟩
    · obtain ⟨r, -, hr⟩ := hp.exists_nonterminal_input_mem
      rw [hs] at hr
      simp [List.mem_replicate] at hr

theorem derives_nested (n : ℕ) :
    (nested x y).Derives [Symbol.nonterminal ()]
      (reps n x ++ Symbol.nonterminal () :: reps n y) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    refine ih.trans_produces ⟨nestedStep x y, (mem_nested_rules x y).2 (Or.inl rfl), ?_⟩
    rw [← reps_succ_split x y n]
    have h := ContextFreeRule.rewrites_of_exists_parts (nestedStep x y) (reps n x) (reps n y)
    rw [List.append_assoc, List.append_assoc] at h
    exact h

theorem lang_nested : lang (nested x y) = nestedLang x y := by
  ext w
  constructor
  · intro h
    obtain ⟨n, hs | hs⟩ := nestedForm_of_generates x y h
    · exact absurd (hs ▸ by simp) (not_mem_map_terminal w ())
    · refine ⟨n, map_terminal_injective (N := Unit) ?_⟩
      simpa [List.map_replicate] using hs
  · rintro ⟨n, rfl⟩
    refine (derives_nested x y n).trans_produces ⟨nestedStop, by simp [nested], ?_⟩
    rw [← List.singleton_append]
    simpa [List.append_assoc, List.map_replicate, nestedStop] using
      ContextFreeRule.rewrites_of_exists_parts (nestedStop : ContextFreeRule T Unit)
        (reps n x) (reps n y)

end Nested

theorem nestedCheck_iff [DecidableEq T] (x y : T) (w : List T) :
    nestedCheck x y w = true ↔ w ∈ nestedLang x y := by
  simp only [nestedCheck, decide_eq_true_eq, nestedLang, Set.mem_ofPred_eq]
  constructor
  · exact fun h => ⟨_, h⟩
  · rintro ⟨n, rfl⟩
    have : (n + n) / 2 = n := by omega
    simp [this]

end Silmaril.Proofs.Semantics.Accept.Grammar

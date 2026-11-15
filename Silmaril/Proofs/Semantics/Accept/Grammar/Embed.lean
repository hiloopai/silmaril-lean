module

public import Silmaril.Semantics.Accept.Grammar.Defs
import Silmaril.Proofs.Semantics.Accept.Grammar.Basic

/-! # Proofs: grammar embeddings, renaming and union

An injective map `φ : g.NT → G.NT` such that `G` contains the renamed rules of `g`, and every
rule of `G` whose input lies in the image of `φ` is a renamed rule of `g`, makes derivations of
`G` from renamed strings exactly the renamed derivations of `g` (`derives_map_terminal_iff`).
Renaming along an injective map and the two halves of a union grammar are instances.
-/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Grammar

open Silmaril.Accept.Grammar

universe u

variable {T : Type u}

theorem mapSym_injective {N N' : Type} {φ : N → N'} (hφ : Function.Injective φ) :
    Function.Injective (mapSym (T := T) φ) := by
  rintro (a | a) (b | b) h <;> simp only [mapSym, reduceCtorEq, Symbol.terminal.injEq,
    Symbol.nonterminal.injEq] at h ⊢
  · exact h
  · exact hφ h

theorem map_mapSym_map_terminal {N N' : Type} (φ : N → N') (w : List T) :
    (w.map Symbol.terminal).map (mapSym φ) = w.map Symbol.terminal := by
  simp [List.map_map, Function.comp_def, mapSym]

section Embed

variable {g G : ContextFreeGrammar T} {φ : g.NT → G.NT}

/-- The rules of `g`, renamed, are rules of `G`. -/
def RulesMap (g G : ContextFreeGrammar T) (φ : g.NT → G.NT) : Prop :=
  ∀ r ∈ g.rules, mapRule φ r ∈ G.rules

/-- Every rule of `G` for a nonterminal in the image of `φ` is a renamed rule of `g`. -/
def RulesReflect (g G : ContextFreeGrammar T) (φ : g.NT → G.NT) : Prop :=
  ∀ r ∈ G.rules, ∀ a, r.input = φ a → ∃ r₀ ∈ g.rules, mapRule φ r₀ = r

theorem produces_map (hfwd : RulesMap g G φ) {u v : List (Symbol T g.NT)}
    (h : g.Produces u v) : G.Produces (u.map (mapSym φ)) (v.map (mapSym φ)) := by
  obtain ⟨r, hr, hrw⟩ := h
  obtain ⟨p, q, rfl, rfl⟩ := ContextFreeRule.rewrites_iff.1 hrw
  refine ⟨mapRule φ r, hfwd r hr, ?_⟩
  simpa [mapRule, mapSym] using ContextFreeRule.rewrites_of_exists_parts (mapRule φ r)
    (p.map (mapSym φ)) (q.map (mapSym φ))

theorem derives_map (hfwd : RulesMap g G φ) {u v : List (Symbol T g.NT)}
    (h : g.Derives u v) : G.Derives (u.map (mapSym φ)) (v.map (mapSym φ)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hp ih => exact ih.tail (produces_map hfwd hp)

theorem produces_of_map (hφ : Function.Injective φ) (hbwd : RulesReflect g G φ)
    {u : List (Symbol T g.NT)} {v : List (Symbol T G.NT)}
    (h : G.Produces (u.map (mapSym φ)) v) :
    ∃ v', v = v'.map (mapSym φ) ∧ g.Produces u v' := by
  obtain ⟨r, hr, hrw⟩ := h
  obtain ⟨p, q, h1, rfl⟩ := ContextFreeRule.rewrites_iff.1 hrw
  rw [List.append_assoc, List.singleton_append] at h1
  obtain ⟨p', s', rfl, rfl, hs⟩ := List.map_eq_append_iff.1 h1
  obtain ⟨b, q', rfl, hb, rfl⟩ := List.map_eq_cons_iff.1 hs
  cases b with
  | terminal t => simp [mapSym] at hb
  | nonterminal a =>
    simp only [mapSym, Symbol.nonterminal.injEq] at hb
    obtain ⟨r₀, hr₀, rfl⟩ := hbwd r hr a hb.symm
    obtain rfl : a = r₀.input := hφ hb
    refine ⟨p' ++ r₀.output ++ q', by simp [mapRule], r₀, hr₀, ?_⟩
    simpa using ContextFreeRule.rewrites_of_exists_parts r₀ p' q'

theorem derives_of_map (hφ : Function.Injective φ) (hbwd : RulesReflect g G φ)
    {u : List (Symbol T g.NT)} {v : List (Symbol T G.NT)}
    (h : G.Derives (u.map (mapSym φ)) v) :
    ∃ v', v = v'.map (mapSym φ) ∧ g.Derives u v' := by
  induction h with
  | refl => exact ⟨u, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hp ih =>
    obtain ⟨v', rfl, hd⟩ := ih
    obtain ⟨v'', rfl, hp'⟩ := produces_of_map hφ hbwd hp
    exact ⟨v'', rfl, hd.tail hp'⟩

/-- Along an embedding of grammars, a renamed string derives a terminal word in `G` iff the
string derives it in `g`. -/
theorem derives_map_terminal_iff (hφ : Function.Injective φ) (hfwd : RulesMap g G φ)
    (hbwd : RulesReflect g G φ) {u : List (Symbol T g.NT)} {w : List T} :
    G.Derives (u.map (mapSym φ)) (w.map Symbol.terminal) ↔
      g.Derives u (w.map Symbol.terminal) := by
  constructor
  · intro h
    obtain ⟨v', hv, hd⟩ := derives_of_map hφ hbwd h
    rw [← map_mapSym_map_terminal φ w] at hv
    rwa [List.map_injective_iff.2 (mapSym_injective hφ) hv]
  · intro h
    have h' := derives_map hfwd h
    rwa [map_mapSym_map_terminal] at h'

end Embed

/-! ## Renaming -/

theorem lang_rename (g : ContextFreeGrammar T) {N : Type} {f : g.NT → N}
    (hf : Function.Injective f) : lang (rename g f) = lang g := by
  classical
  ext w
  refine derives_map_terminal_iff (u := [Symbol.nonterminal g.initial]) (G := rename g f) hf
    (fun r hr => Finset.mem_image_of_mem _ hr) ?_
  intro r hr _ _
  exact Finset.mem_image.1 hr

/-! ## Union -/

section Union

variable (g₁ g₂ : ContextFreeGrammar T)

theorem rulesMap_union_inl : RulesMap g₁ (union g₁ g₂) (some ∘ Sum.inl) := fun r hr => by
  classical
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩))

theorem rulesMap_union_inr : RulesMap g₂ (union g₁ g₂) (some ∘ Sum.inr) := fun r hr => by
  classical
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr (Or.inr ⟨r, hr, rfl⟩))

theorem rulesReflect_union_inl : RulesReflect g₁ (union g₁ g₂) (some ∘ Sum.inl) := by
  classical
  intro r hr a ha
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hr
  rcases hr with rfl | rfl | ⟨r₀, hr₀, rfl⟩ | ⟨r₀, -, rfl⟩
  · simp at ha
  · simp at ha
  · exact ⟨r₀, hr₀, rfl⟩
  · simp [mapRule] at ha

theorem rulesReflect_union_inr : RulesReflect g₂ (union g₁ g₂) (some ∘ Sum.inr) := by
  classical
  intro r hr a ha
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hr
  rcases hr with rfl | rfl | ⟨r₀, -, rfl⟩ | ⟨r₀, hr₀, rfl⟩
  · simp at ha
  · simp at ha
  · simp [mapRule] at ha
  · exact ⟨r₀, hr₀, rfl⟩

theorem lang_union : lang (union g₁ g₂) = lang g₁ ∪ lang g₂ := by
  classical
  ext w
  have h₁ := derives_map_terminal_iff (u := [Symbol.nonterminal g₁.initial]) (w := w)
    (Option.some_injective _ |>.comp Sum.inl_injective) (rulesMap_union_inl g₁ g₂)
    (rulesReflect_union_inl g₁ g₂)
  have h₂ := derives_map_terminal_iff (u := [Symbol.nonterminal g₂.initial]) (w := w)
    (Option.some_injective _ |>.comp Sum.inr_injective) (rulesMap_union_inr g₁ g₂)
    (rulesReflect_union_inr g₁ g₂)
  simp only [Set.mem_union]
  constructor
  · intro h
    obtain ⟨r, hr, hi, hd⟩ := derives_singleton_map_terminal (g := union g₁ g₂) h
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hr
    rcases hr with rfl | rfl | ⟨r₀, -, rfl⟩ | ⟨r₀, -, rfl⟩
    · exact Or.inl (h₁.1 hd)
    · exact Or.inr (h₂.1 hd)
    · simp [mapRule] at hi
    · simp [mapRule] at hi
  · rintro (h | h)
    · refine Relation.ReflTransGen.head (produces_singleton_iff.2
        ⟨⟨none, [.nonterminal (some (.inl g₁.initial))]⟩, ?_, rfl, rfl⟩) (h₁.2 h)
      exact Finset.mem_insert_self _ _
    · refine Relation.ReflTransGen.head (produces_singleton_iff.2
        ⟨⟨none, [.nonterminal (some (.inr g₂.initial))]⟩, ?_, rfl, rfl⟩) (h₂.2 h)
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

end Union

end Silmaril.Proofs.Semantics.Accept.Grammar

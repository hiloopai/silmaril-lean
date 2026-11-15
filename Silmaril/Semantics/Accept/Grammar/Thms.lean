module

public import Silmaril.Semantics.Accept.Grammar.Defs
public import Silmaril.Semantics.Accept.Thms
import Silmaril.Proofs.Semantics.Accept.Grammar.Basic
import Silmaril.Proofs.Semantics.Accept.Grammar.Embed

/-!
# Context-free grammars as presentations: laws

Statements about `Silmaril.Semantics.Accept.Grammar.Defs`; longer proofs are in
`Silmaril.Proofs.Semantics.Accept.Grammar.Basic` and `…Grammar.Embed`.

* the grammar language as an acceptor set: `mem_lang`, `lang_eq_preimage`,
  `lang_eq_acceptsSome`, `lang_reverse`;
* grammars as presentations: `presents_iff` (sound and complete), `Presents.unique`,
  `Presents.congr`, `isContextFree_iff_exists_presents`;
* Bool checkers against a grammar: `sound_lang_iff`, `complete_lang_iff`, `decides_lang_iff`,
  `decides_lang_iff_ofBool_eq`, transport along presentations (`Accept.Decides.of_presents`,
  `Accept.Decides.presents_iff`, `Accept.Sound.trans_grammar`,
  `Accept.Complete.trans_grammar`; these extend the checker namespaces of
  `Silmaril.Semantics.Accept.Thms` so dot notation works) and along reversal
  (`Accept.Decides.reverse_grammar`);
* small grammars: `lang_empty`, `lang_word`, and the nested grammar `S → x S y | ε` with
  `lang_nested : lang (nested x y) = nestedLang x y` and `decides_nestedCheck`;
* renaming and union: `lang_rename` (injective renaming preserves the language),
  `lang_union`, `Presents.union`, `Accept.Decides.union_grammar`;
* context-freeness: `isContextFree_empty`, `isContextFree_singleton`, `isContextFree_union`,
  `isContextFree_nestedLang`.
-/

@[expose] public section

namespace Silmaril.Accept.Grammar

universe u

variable {T : Type u} {g g' : ContextFreeGrammar T} {L L' : Set (List T)}
  {check : List T → Bool}

/-! ## The grammar language as an acceptor set -/

@[simp] theorem mem_lang {w : List T} : w ∈ lang g ↔ g.Generates (w.map Symbol.terminal) :=
  Iff.rfl

@[simp] theorem mem_sentential {s : List (Symbol T g.NT)} : s ∈ sentential g ↔ g.Generates s :=
  Iff.rfl

/-- A word is in the language iff its string of terminals is a sentential form. -/
theorem lang_eq_preimage : lang g = List.map Symbol.terminal ⁻¹' sentential g := rfl

/-- The language is existential acceptance of the deterministic runner that embeds a word as
a string of terminals, with the sentential forms as accepting outcomes. -/
theorem lang_eq_acceptsSome :
    lang g = acceptsSome (detRun (List.map Symbol.terminal)) (sentential g) := by
  rw [acceptsSome_detRun]; rfl

/-- Reversing every rule reverses the language (Mathlib's `language_reverse`). -/
theorem lang_reverse : lang g.reverse = List.reverse ⁻¹' lang g :=
  ContextFreeGrammar.language_reverse

/-! ## Grammars as presentations -/

theorem presents_iff : Presents g L ↔ Sound g L ∧ Complete g L :=
  Set.Subset.antisymm_iff

theorem Presents.sound (h : Presents g L) : Sound g L := (presents_iff.1 h).1

theorem Presents.complete (h : Presents g L) : Complete g L := (presents_iff.1 h).2

theorem presents_lang (g : ContextFreeGrammar T) : Presents g (lang g) := rfl

theorem sound_iff : Sound g L ↔ ∀ w, g.Generates (w.map Symbol.terminal) → w ∈ L := Iff.rfl

theorem complete_iff : Complete g L ↔ ∀ w ∈ L, g.Generates (w.map Symbol.terminal) := Iff.rfl

theorem Sound.mono (h : Sound g L) (hL : L ⊆ L') : Sound g L' := h.trans hL

theorem Complete.anti (h : Complete g L') (hL : L ⊆ L') : Complete g L := hL.trans h

/-- A grammar presents at most one language. -/
theorem Presents.unique (h : Presents g L) (h' : Presents g L') : L = L' := h.symm.trans h'

/-- Grammars with equal languages present the same sets. -/
theorem Presents.congr (h : lang g = lang g') : Presents g L ↔ Presents g' L := by
  rw [Presents, Presents, h]

theorem isContextFree_iff_exists_presents :
    Language.IsContextFree (T := T) L ↔ ∃ g : ContextFreeGrammar T, Presents g L := Iff.rfl

theorem Presents.isContextFree (h : Presents g L) : Language.IsContextFree (T := T) L :=
  ⟨g, h⟩

/-! ## Bool checkers against a grammar -/

/-- A checker is sound for a grammar iff every word it accepts is derivable. -/
theorem sound_lang_iff :
    Accept.Sound check (lang g) ↔ ∀ w, check w = true → g.Generates (w.map Symbol.terminal) :=
  Iff.rfl

/-- A checker is complete for a grammar iff it accepts every derivable word. -/
theorem complete_lang_iff :
    Accept.Complete check (lang g) ↔ ∀ w, g.Generates (w.map Symbol.terminal) → check w = true :=
  Iff.rfl

theorem decides_lang_iff :
    Decides check (lang g) ↔ ∀ w, check w = true ↔ g.Generates (w.map Symbol.terminal) :=
  Iff.rfl

/-- A checker decides a grammar's language iff its accepted set is that language. -/
theorem decides_lang_iff_ofBool_eq : Decides check (lang g) ↔ ofBool check = lang g :=
  decides_iff_ofBool_eq

/-- A checker for `L` decides the language of every grammar presenting `L`. -/
theorem _root_.Silmaril.Accept.Decides.of_presents (hc : Decides check L) (hg : Presents g L) :
    Decides check (lang g) := hg ▸ hc

/-- Given a checker for the grammar's language, the grammar presents `L` iff the checker
accepts exactly `L`. -/
theorem _root_.Silmaril.Accept.Decides.presents_iff (hc : Decides check (lang g)) :
    Presents g L ↔ ofBool check = L := by
  rw [Presents, decides_iff_ofBool_eq.1 hc]

/-- Deciding transports along grammars with equal languages. -/
theorem decides_lang_congr (h : lang g = lang g') :
    Decides check (lang g) ↔ Decides check (lang g') := by
  rw [h]

/-- A checker sound for a grammar that is sound for `L` is sound for `L`. -/
theorem _root_.Silmaril.Accept.Sound.trans_grammar (hc : Accept.Sound check (lang g))
    (hg : Grammar.Sound g L) :
    Accept.Sound check L := hc.mono hg

/-- A checker complete for a grammar that is complete for `L` is complete for `L`. -/
theorem _root_.Silmaril.Accept.Complete.trans_grammar (hc : Accept.Complete check (lang g))
    (hg : Grammar.Complete g L) :
    Accept.Complete check L := hc.anti hg

/-- A checker for `g` gives a checker for the reversed grammar: reverse, then check. -/
theorem _root_.Silmaril.Accept.Decides.reverse_grammar (hc : Decides check (lang g)) :
    Decides (check ∘ List.reverse) (lang g.reverse) := by
  rw [lang_reverse]; exact hc.comp List.reverse

/-! ## Small grammars -/

@[simp] theorem lang_empty : lang (empty : ContextFreeGrammar T) = ∅ :=
  Proofs.Semantics.Accept.Grammar.lang_empty

@[simp] theorem lang_word (w : List T) : lang (word w) = {w} :=
  Proofs.Semantics.Accept.Grammar.lang_word w

/-- The headline example: `S → x S y | ε` derives exactly the words `xⁿ yⁿ` (soundness and
completeness of the grammar for `nestedLang x y`). -/
theorem lang_nested (x y : T) : lang (nested x y) = nestedLang x y :=
  Proofs.Semantics.Accept.Grammar.lang_nested x y

theorem presents_nested (x y : T) : Presents (nested x y) (nestedLang x y) := lang_nested x y

theorem decides_nestedCheck_nestedLang [DecidableEq T] (x y : T) :
    Decides (nestedCheck x y) (nestedLang x y) :=
  Proofs.Semantics.Accept.Grammar.nestedCheck_iff x y

/-- `nestedCheck x y` decides the language of the grammar `S → x S y | ε`. -/
theorem decides_nestedCheck [DecidableEq T] (x y : T) :
    Decides (nestedCheck x y) (lang (nested x y)) :=
  (decides_nestedCheck_nestedLang x y).of_presents (presents_nested x y)

/-! ## Renaming and union -/

/-- Renaming nonterminals along an injective map preserves the language. -/
theorem lang_rename (g : ContextFreeGrammar T) {N : Type} {f : g.NT → N}
    (hf : Function.Injective f) : lang (rename g f) = lang g :=
  Proofs.Semantics.Accept.Grammar.lang_rename g hf

/-- The union grammar derives exactly the words derived by either grammar. -/
theorem lang_union (g₁ g₂ : ContextFreeGrammar T) : lang (union g₁ g₂) = lang g₁ ∪ lang g₂ :=
  Proofs.Semantics.Accept.Grammar.lang_union g₁ g₂

theorem Presents.union (h₁ : Presents g L) (h₂ : Presents g' L') :
    Presents (union g g') (L ∪ L') := by
  rw [Presents, lang_union, h₁, h₂]

/-- Checkers for two grammars combine by `||` into a checker for their union grammar. -/
theorem _root_.Silmaril.Accept.Decides.union_grammar {check' : List T → Bool}
    (hc : Decides check (lang g)) (hc' : Decides check' (lang g')) :
    Decides (fun w => check w || check' w) (lang (union g g')) :=
  lang_union g g' ▸ hc.or hc'

/-! ## Context-freeness -/

theorem isContextFree_empty : Language.IsContextFree (T := T) (∅ : Set (List T)) :=
  ⟨empty, lang_empty⟩

theorem isContextFree_singleton (w : List T) :
    Language.IsContextFree (T := T) ({w} : Set (List T)) :=
  ⟨word w, lang_word w⟩

/-- Context-free languages are closed under union (not in Mathlib at the pinned version). -/
theorem isContextFree_union (h : Language.IsContextFree (T := T) L)
    (h' : Language.IsContextFree (T := T) L') :
    Language.IsContextFree (T := T) (L ∪ L' : Set (List T)) :=
  let ⟨_, hg⟩ := h
  let ⟨_, hg'⟩ := h'
  (Presents.union hg hg').isContextFree

theorem isContextFree_nestedLang (x y : T) : Language.IsContextFree (T := T) (nestedLang x y) :=
  (presents_nested x y).isContextFree

end Silmaril.Accept.Grammar

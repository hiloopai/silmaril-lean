module

public import Silmaril.Proofs.Parse.ByteParse.Choice

/-!
# Fast, verified binary parsers: laws and grammars

The proof principles for `Silmaril.Parse.ByteParse` (proofs in
`Silmaril/Proofs/Parse/ByteParse/`):

* **Soundness** `Sound G p` and **completeness** `Complete G p` (or
  `CompleteAtEnd G p` for parsers delimited by their window) for every
  primitive: `byte`, `expect`, `bytes`, `rest`, `sized`, `opt`, `many`,
  `vec` (`Vec G` of silmaril), `untilEnd` (`Seq G`), `uN`/`sN` (silmaril's
  `UN`/`SN`, the Wasm LEB128 grammars with their length bounds), `le`
  (little-endian), `name` (sound for silmaril's `Name`, complete for the
  canonical UTF-8 encoding), `tagged`, `choice`, `filterMap`.
* **Composition**: `Sound.bind`/`Complete.bind` (concatenation, `Spec.bind`),
  `.map`, `.sized` (the sub-parser consumes its window exactly and cannot read
  past it), `Complete.bindAtEnd`.
* **Lawful grammars**: the `Grammar α` and `GrammarE α` of `Silmaril.Parse.ByteParse.Defs` pair a
  parser with its grammar; `Grammar.Lawful g` (`GrammarE.Lawful g`, complete at the end of
  the window) states both laws. Every combinator has an instance (`Grammar.lawful_bind`,
  `lawful_vec`, `GrammarE.lawful_after`, …) and `Grammar.Lawful.tagged` covers tagged unions,
  so `g.sound` and `g.complete` hold for every grammar built from them; the tactic
  `grammar_lawful` below proves `g.Lawful` for such a `g`. Introduction lemmas: `seq_G`,
  `tagged_G`, `vec_G`, …
* **Round trips**: `Grammar.roundTrip`/`Complete.run_append`
  (`parse (enc ++ rest) = ok a |enc|`), `GrammarE.runAll_complete`, and the
  encoder laws `Enc.*_G` (`G (enc a) a`, silmaril's `encU_sound`/`encS_sound`
  for LEB128).
* **Unambiguity**: `Grammar.functional`.
-/

@[expose] public section

namespace Silmaril.Parse.ByteParse

/-- `grammar_lawful` proves `g.Lawful` (or `GrammarE.Lawful`) for a grammar built from the
combinators: by instance search, else by the instance of its outermost combinator; a tagged
union by cases on the branches of its tag function. A branch it cannot see through (a helper
returning `Option (Grammar _)`) is closed by `solve_by_elim` from the local context, so a
caller can add the helper's law as a hypothesis first. -/
syntax "grammar_lawful" : tactic

/-- `grammar_lawful_of h` proves `g.Lawful` from `h : o = some g`, by cases on the matches and
conditionals of `o`. -/
syntax "grammar_lawful_of " ident : tactic

macro_rules
  | `(tactic| grammar_lawful_of $h:ident) => `(tactic| (
      (repeat' split at $h:ident) <;>
      first
        | (cases $h:ident; done)
        | (cases $h:ident; grammar_lawful)
        | (obtain ⟨_, hx, he⟩ := Option.map_eq_some_iff.mp $h:ident; subst he; grammar_lawful)
        | solve_by_elim))

macro_rules
  | `(tactic| grammar_lawful) => `(tactic| first
      | exact inferInstance
      | (apply Grammar.Lawful.tagged; intro _ _ hk; grammar_lawful_of hk)
      | (refine @Grammar.lawful_map _ _ _ _ ?_; grammar_lawful)
      | (refine @Grammar.lawful_bind _ _ _ _ ?_ ?_ <;> (try intro _) <;> grammar_lawful)
      | (refine @Grammar.lawful_seq _ _ _ _ ?_ ?_ <;> grammar_lawful)
      | (refine @Grammar.lawful_then _ _ _ ?_ ?_ <;> grammar_lawful)
      | (refine @Grammar.lawful_sized _ _ _ ?_; grammar_lawful)
      | (refine @Grammar.lawful_opt _ _ _ ?_; grammar_lawful)
      | (refine @Grammar.lawful_vec _ _ _ ?_; grammar_lawful)
      | (refine @Grammar.lawful_many _ _ _ ?_; grammar_lawful)
      | (refine @Grammar.lawful_sizedItems _ _ _ ?_; grammar_lawful)
      | (refine @Grammar.lawful_sizedBy _ _ ?_; grammar_lawful)
      | (refine @Grammar.lawful_filterMap _ _ _ _ _ ?_; grammar_lawful)
      | (refine @Grammar.lawful_choice _ _ _ _ ?_ ?_ _ _ <;> grammar_lawful)
      | (refine @GrammarE.lawful_sizedBy _ _ ?_; grammar_lawful)
      | (refine @GrammarE.lawful_sized _ _ _ ?_; grammar_lawful)
      | (refine @GrammarE.lawful_map _ _ _ _ ?_; grammar_lawful)
      | (refine @GrammarE.lawful_after _ _ _ _ ?_ ?_ <;> (try intro _) <;> grammar_lawful)
      | (refine @GrammarE.lawful_items _ _ _ ?_; grammar_lawful)
      | (refine @GrammarE.lawful_ofGrammar _ _ ?_; grammar_lawful)
      | solve_by_elim)

end Silmaril.Parse.ByteParse

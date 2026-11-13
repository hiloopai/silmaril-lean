module

public import Silmaril.Wasm.Wit.Syntax.Defs

/-!
# WIT: identifiers, versions and gates

Lexical validity of the names in a WIT AST (`WIT.md`, "Identifiers"):

```
id   ::= '%'? word ('-' word)*
word ::= [a-z] [0-9a-z]* | [A-Z] [0-9A-Z]*
```

(the `%` escape is lexical and not part of `Name`), semantic versions (SemVer 2.0.0:
pre-release identifiers are non-empty, alphanumeric or `-`, and numeric ones have no
leading zero; build identifiers are non-empty alphanumeric or `-`), and feature gates
(`Gate.stability` defined, versions valid, feature names identifiers).

Every predicate here is decidable by its structure; `decide` is its checker.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit

/-- Split a character list at `-`. `splitDash [] = [[]]`, so the empty name has one
empty word. -/
def splitDash : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '-' then [] :: splitDash cs
    else match splitDash cs with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

/-- A WIT word: a lowercase letter followed by lowercase letters and digits, or the
same in uppercase. -/
def Word : List Char → Prop
  | [] => False
  | c :: cs =>
    (c.isLower ∧ ∀ d ∈ cs, d.isLower ∨ d.isDigit) ∨
    (c.isUpper ∧ ∀ d ∈ cs, d.isUpper ∨ d.isDigit)

instance : DecidablePred Word := fun w =>
  match w with
  | [] => isFalse id
  | _ :: _ => inferInstanceAs (Decidable (_ ∨ _))

/-- A valid WIT identifier (kebab case): words separated by single dashes. -/
def ValidId (s : Name) : Prop := ∀ w ∈ splitDash s.toList, Word w

instance (s : Name) : Decidable (ValidId s) := inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- A character allowed in a SemVer identifier. -/
def semverChar (c : Char) : Bool := c.isAlphanum || c == '-'

/-- A SemVer build identifier: non-empty, alphanumeric or `-`. -/
def ValidBuildId (s : String) : Prop := s.toList ≠ [] ∧ ∀ c ∈ s.toList, semverChar c

instance (s : String) : Decidable (ValidBuildId s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A SemVer pre-release identifier: a build identifier, and a numeric one has no
leading zero. -/
def ValidPreId (s : String) : Prop :=
  ValidBuildId s ∧ ((∀ c ∈ s.toList, c.isDigit) → s.toList.head? = some '0' → s = "0")

instance (s : String) : Decidable (ValidPreId s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A valid semantic version. -/
def Version.Valid (v : Version) : Prop :=
  (∀ s ∈ v.pre, ValidPreId s) ∧ ∀ s ∈ v.build, ValidBuildId s

instance (v : Version) : Decidable v.Valid := inferInstanceAs (Decidable (_ ∧ _))

/-- A valid package name `ns:name@version`. -/
def PackageName.Valid (p : PackageName) : Prop :=
  ValidId p.ns ∧ ValidId p.name ∧ ∀ v ∈ p.version, v.Valid

instance (p : PackageName) : Decidable p.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ _ ∈ p.version, _))

/-- The contents of one gate are valid. -/
def Gate.Valid : Gate → Prop
  | .since v | .deprecated v => v.Valid
  | .unstable f => ValidId f

instance (g : Gate) : Decidable g.Valid :=
  match g with
  | .since v | .deprecated v => inferInstanceAs (Decidable v.Valid)
  | .unstable f => inferInstanceAs (Decidable (ValidId f))

/-- A valid list of gates: an accepted combination (`Gate.stability`) of valid gates. -/
def GatesOk (gs : List Gate) : Prop := (Gate.stability gs).isSome ∧ ∀ g ∈ gs, g.Valid

instance (gs : List Gate) : Decidable (GatesOk gs) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Sanity checks -/

example : ValidId "wasi-http" := by decide
example : ValidId "HTTP-proxy2" := by decide
example : ¬ ValidId "Http" := by decide
example : ¬ ValidId "a--b" := by decide
example : ¬ ValidId "" := by decide
example : ¬ ValidId "1a" := by decide
example : (Version.mk 0 2 0 ["rc-2023-11-10"] []).Valid := by decide
example : ¬ (Version.mk 1 0 0 ["01"] []).Valid := by decide
example : GatesOk [.since ⟨0, 2, 1, [], []⟩, .deprecated ⟨0, 2, 2, [], []⟩] := by decide
example : ¬ GatesOk [.deprecated ⟨0, 2, 2, [], []⟩] := by decide

end Silmaril.Wasm.Wit

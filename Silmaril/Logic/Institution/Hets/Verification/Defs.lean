module

public import Silmaril.Logic.Institution.Hets.StructuredSpec
public import Silmaril.Logic.Institution.Hets.DevGraph

@[expose] public section

/-!
# The verification semantics: structured specifications as development graphs

Structured specifications are translated into development graphs, preserving model classes
(Mossakowski–Autexier–Hutter §8.1; Mossakowski's habilitation, Theorem 5.19, and Theorem 6.45 for
the heterogeneous case). The papers build the graph inductively, adding a fresh node for each
specification-building operation. Here one development graph `StrSpec.devGraph I` serves every
specification at once: its nodes are all pairs `(Σ, SP)` with `SP : StrSpec I Σ`, and

* a node `(Σ, basic Σ E)` has local axioms `E`;
* a node `(Σ, union SP₁ SP₂)` has global definition links along `id` from `(Σ, SP₁)` and
  `(Σ, SP₂)`;
* a node `(Σ', translate σ SP)` has a global definition link along `σ` from `(Σ, SP)`;
* a node `(Σ, hide σ SP')` has a hiding link along `σ` from `(Σ', SP')`.

Links only go from immediate subterms, so the link relation is well-founded.
`StrSpec.models_devGraph` is the theorem `Mod(SP) = Mod_S(N_SP)`.

## References

* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §8.1
  (PDF pages 19–21: §§8.1.1–8.1.4 and the invariant `Mod(SP) = Mod_S(O)`).
* `mossakowski-2005-habilitation-hets` in `references.bib`, §5.5, Theorem 5.19 (printed
  page 137, PDF page 139); §6.11, Theorem 6.45 (printed pages 180–181, PDF pages 182–183).
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe u v w m₁ m₂

variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w, m₁, m₂})

namespace StrSpec

/-- The nodes of the verification graph: specifications paired with their signatures. -/
abbrev Node : Type (max u v w) := Σ S : Sign, StrSpec I S

variable {I}

/-- The local axioms of a node: those of a presentation, and none otherwise.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §8.1.1
(PDF page 20). -/
def nodeAxioms : (N : Node I) → Set (I.obj N.1).Sen
  | ⟨_, basic _ E⟩ => E
  | ⟨_, union _ _⟩ => ∅
  | ⟨_, translate _ _⟩ => ∅
  | ⟨_, hide _ _⟩ => ∅

/-- The global definition links into a node: identities from the two parts of a union, and the
translating morphism from the translated specification.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`,
§§8.1.2–8.1.3 (PDF pages 20–21). -/
def nodeGlobalDef (M : Node I) : (N : Node I) → Set (M.1 ⟶ N.1)
  | ⟨_, basic _ _⟩ => ∅
  | ⟨S, union SP₁ SP₂⟩ =>
      {σ | (∃ h : M = ⟨S, SP₁⟩, σ = eqToHom (congrArg Sigma.fst h)) ∨
        (∃ h : M = ⟨S, SP₂⟩, σ = eqToHom (congrArg Sigma.fst h))}
  | ⟨_, @translate _ _ _ S₀ _ τ SP⟩ =>
      {σ | ∃ h : M = ⟨S₀, SP⟩, σ = eqToHom (congrArg Sigma.fst h) ≫ τ}
  | ⟨_, hide _ _⟩ => ∅

/-- The hiding links into a node: the hiding morphism from the specification it derives from.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §8.1.4
(PDF page 21). -/
def nodeHidingDef (M : Node I) : (N : Node I) → Set (N.1 ⟶ M.1)
  | ⟨_, basic _ _⟩ => ∅
  | ⟨_, union _ _⟩ => ∅
  | ⟨_, translate _ _⟩ => ∅
  | ⟨_, @hide _ _ _ _ S' τ SP'⟩ =>
      {σ | ∃ h : M = ⟨S', SP'⟩, σ = τ ≫ eqToHom (congrArg Sigma.fst h).symm}

/-- The number of specification-building operations in a structured specification; it
decreases along the links of the verification graph. -/
def size : {S : Sign} → StrSpec I S → ℕ
  | _, basic _ _ => 0
  | _, union SP₁ SP₂ => SP₁.size + SP₂.size + 1
  | _, translate _ SP => SP.size + 1
  | _, hide _ SP' => SP'.size + 1


end StrSpec

end Silmaril.Logic.Institution

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.Data.Set.Image

@[expose] public section

/-!
# Languages as behavioural institutions

A *language* for the category of compilers is a type of programs, each with an interface (its
signature: imports and exports), and a set of observable behaviours per program. Every language
determines an institution, its *behavioural institution*:

* signatures are interfaces (a discrete category for now; interface morphisms are future work);
* sentences over an interface are behavioural specifications, sets of observations;
* models are behaviour sets, ordered by inclusion (a model morphism `B ⟶ B'` is `B ⊆ B'`), and a
  program denotes the model `beh p`;
* satisfaction `B ⊨ φ` is `B ⊆ φ`: every behaviour meets the specification.

Specifications are trace properties, so satisfaction is closed under refinement (fewer
behaviours) automatically; hyperproperties are not covered by this institution.

The execution semantics of a language (its execution category: configurations and finite runs)
lives in `Silmaril.Compile.Category.Exec`.

## Main definitions

* `Language`: programs, interfaces, observations and behaviours.
* `Language.room`, `Language.inst`: the behavioural institution, in
  `Silmaril.Compile.Category.Institution` (it reuses `Silmaril.Logic.Institution`).
* `Language.Sat`: `p ⊨ φ`, satisfaction of a program through its behaviour model.
* `Language.Refines`, `Language.BehEquiv`: behavioural refinement and equivalence of programs.
-/

namespace Silmaril.Compile.Category

open CategoryTheory

universe u

/-- A language: programs with interfaces and observable behaviours.

Behaviours are observations of complete runs, in the style of CompCert's program behaviours
(`papers/compilers/leroy-2009-compcert-backend.pdf`, §2.1, p. 3) and CompCertO's language
interfaces (`papers/compilers/koenig-shao-2021-compcerto.pdf`, Definition 2.1, p. 3); see
`Exec.adequate` for the link with an execution semantics. -/
structure Language : Type (u + 1) where
  /-- Interfaces: the signatures of the behavioural institution. -/
  Iface : Type u
  /-- Programs (modules, compilation units). -/
  Prog : Type u
  /-- The interface of a program. -/
  iface : Prog → Iface
  /-- Observations. -/
  Obs : Type u
  /-- The observable behaviours of a program. -/
  beh : Prog → Set Obs

namespace Language

variable (L : Language.{u})

/-- Satisfaction of a specification by a program, through its behaviour model:
`p ⊨ φ ↔ beh p ⊆ φ`. This is satisfaction in the behavioural institution
(`Language.sat_iff_room`). -/
def Sat (p : L.Prog) (φ : Set L.Obs) : Prop := L.beh p ⊆ φ

theorem sat_iff (p : L.Prog) (φ : Set L.Obs) : L.Sat p φ ↔ L.beh p ⊆ φ := Iff.rfl

/-- Behavioural refinement: `L.Refines p q` says that `q` refines `p`: same interface, and every
behaviour of `q` is a behaviour of `p`. This is the identity-convention validity relation
(`Convention.valid_id_iff`). -/
def Refines (p q : L.Prog) : Prop := L.iface q = L.iface p ∧ L.beh q ⊆ L.beh p

/-- Behavioural equivalence: refinement both ways (the symmetric part of `Refines`). -/
def BehEquiv (p q : L.Prog) : Prop := L.Refines p q ∧ L.Refines q p

theorem refines_refl (p : L.Prog) : L.Refines p p := ⟨rfl, subset_rfl⟩

theorem refines_trans {p q r : L.Prog} (h₁ : L.Refines p q) (h₂ : L.Refines q r) :
    L.Refines p r :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem behEquiv_iff (p q : L.Prog) :
    L.BehEquiv p q ↔ L.iface p = L.iface q ∧ L.beh p = L.beh q :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₂.1, h₂.2.antisymm h₁.2⟩,
    fun ⟨hi, hb⟩ => ⟨⟨hi.symm, hb.symm.subset⟩, ⟨hi, hb.subset⟩⟩⟩

/-- A refinement satisfies every specification its original satisfies. -/
theorem Refines.sat {L : Language.{u}} {p q : L.Prog} (h : L.Refines p q) {φ : Set L.Obs}
    (hp : L.Sat p φ) : L.Sat q φ :=
  h.2.trans hp

end Language

end Silmaril.Compile.Category

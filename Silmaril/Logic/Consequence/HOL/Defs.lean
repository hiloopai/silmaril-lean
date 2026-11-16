module

public import Silmaril.Logic.Consequence.Institution.Defs
public import Silmaril.Logic.Institution.Metatheory.HOL

/-!
# HOL propositions as consequence systems

The HOL institution `Silmaril.Logic.Institution.Metatheory.HOL.inst` has *sequents* `H ⊢ p` as
sentences, satisfied by a model `M` when `HOLLight.Entails M H p`: **under every valuation**, if
every hypothesis holds then so does `p`. Its consequence systems (`roomSeq`, `roomMulti`,
`HOL.logic`) relate sequents. This module reads HOL at the level of **propositions**.

* `HOLProp S`: the terms of type `bool` over the signature `S` (closed under binders; free
  variables allowed). Type variables and free term variables are interpreted by a *point*
  `(M, ρ, ν)`: a model, a type valuation and a free-variable assignment (`satAt`).
* `seq S : System (List (HOLProp S)) (HOLProp S)`, **`HOLProp* ⊢ HOLProp`**: every point that
  satisfies all of `Γ` satisfies `p`. This is HOL Light's own sequent semantics: `seq S Γ p` iff
  the sequent `Γ ⊢ p` is valid in every model (`Thms`: `seq_iff_entails`), that is a valid
  sentence of the institution (`seq_iff_valid_toSeq`).
* `gentzen S : MultiSystem (HOLProp S) (HOLProp S)`, **`HOLProp* ⊢ HOLProp*`**: every point that
  satisfies all of `Γ` satisfies **some** member of `Δ`. HOL is classical and two-valued, so this
  is the LK reading: the succedent is a disjunction evaluated at one valuation. Its
  singleton-succedent part is `seq S` (`gentzen_single`).
* `globalSeq S`, `globalGentzen S`: the model-wise readings (`validIn`): `p` is *valid* in every
  model in which every member of `Γ` is valid; for `globalGentzen`, some member of `Δ` is valid.
  These are the consequences of the hypothesis-free sentences `⊢ p` in the institution. They are
  **not** the LK reading. `seq ≤ globalSeq` always (`seq_le_globalSeq`); for open formulas the
  converse fails, and `gentzen` and `globalGentzen` are incomparable (for a free boolean `x`,
  `⊢ x, ¬x` is locally but not globally valid). The abstract counterexamples are in
  `Silmaril.Logic.Consequence.Institution.Examples`.

Maps of propositions, each with a closure theorem in `Thms`:

* `HOLProp.map h`: along a signature extension `h : S ≤ T` (identity on syntax).
* `HOLProp.tySubst σ hσ`: type instantiation (the kernel's `INST_TYPE`), for well-formed `σ`.
* `HOLProp.freeSubst σ hσ`: instantiation of free term variables (the kernel's `INST`), for a
  type-respecting `σ`.
* `HOLProp.disjList Δ`: the disjunction of `Δ` (`⊥` when empty), with which `gentzen` collapses
  to `seq` (`Thms`: `gentzen_iff_seq_disjList`).
* `toSeq Γ p`: the sentence `Γ ⊢ p` of the institution; `closedSen p`: the sentence `⊢ p`.

**Derivability** is kept apart from these semantic systems:

* `kernelFrom S Δ : System (List (HOLProp S)) (HOLProp S)`: `p` has a HOL Light kernel
  derivation (`HOLLight.Derives`) from the axioms `Δ` whose hypotheses are the members of `Γ`.
  It satisfies identity (`ASSUME`), weakening and cut, which are admissible in the kernel, and
  substitution along `INST_TYPE` and `INST` (`Thms`).
* `kernel S := kernelFrom S []`: pure HOL. It is sound for `seq` (`kernel_le_seq`). With axioms
  the kernel instantiates them, so `kernelFrom S Δ` is sound only model-wise, for closed
  consequences (`derives_le_globalSeq`).
-/

@[expose] public section

namespace Silmaril.Consequence.HOL

open Silmaril.Logic.HOLLight
open Silmaril.Logic.Institution.Metatheory (HolSig)

universe u

/-- **A HOL proposition** over `S`: a term of type `bool` in the empty bound context. -/
def HOLProp (S : HolSig) : Type := {p : Tm // HasType S.sig [] p .bool}

variable {S T : HolSig}

/-- Satisfaction of a proposition at a point `(ρ, ν)` of a model `M`. -/
def satAt (M : Model.{u} S.sig) (x : Σ ρ : TypeValuation.{u}, FreeEnv M ρ) (p : HOLProp S) :
    Prop :=
  Holds M x.1 x.2 p.1

/-- **`HOLProp* ⊢ HOLProp`**: every point satisfying all of `Γ` satisfies `p`. -/
def seq (S : HolSig) : System (List (HOLProp S)) (HOLProp S) :=
  Refutation.Entails (localSat (satAt.{u} (S := S)))

/-- **`HOLProp* ⊢ HOLProp*`** (LK): every point satisfying all of `Γ` satisfies some member of
`Δ`. -/
def gentzen (S : HolSig) : MultiSystem (HOLProp S) (HOLProp S) :=
  Gentzen.Valid (localSat (satAt.{u} (S := S)))

/-- Model-wise consequence: `p` is valid in every model where all of `Γ` are valid. -/
def globalSeq (S : HolSig) : System (List (HOLProp S)) (HOLProp S) :=
  Refutation.Entails (validIn (satAt.{u} (S := S)))

/-- Model-wise multiple conclusions: some member of `Δ` is valid in every model where all of `Γ`
are valid. Not the LK reading. -/
def globalGentzen (S : HolSig) : MultiSystem (HOLProp S) (HOLProp S) :=
  Gentzen.Valid (validIn (satAt.{u} (S := S)))

namespace HOLProp

/-- Along a signature extension: the same term. -/
def map (h : S ≤ T) (p : HOLProp S) : HOLProp T :=
  ⟨p.1, Silmaril.Logic.Institution.Metatheory.HOL.hasType_of_le h p.2⟩

/-- Type instantiation by a well-formed `σ`. -/
def tySubst (σ : Nat → Ty) (hσ : ∀ i, (σ i).WellFormed S.sig.tyOps) (p : HOLProp S) :
    HOLProp S :=
  ⟨p.1.tySubst σ, by simpa [Ty.subst] using p.2.tySubst σ hσ⟩

/-- Instantiation of free term variables by a type-respecting `σ`. -/
def freeSubst (σ : Nat → Ty → Tm)
    (hσ : ∀ n B, B.WellFormed S.sig.tyOps → HasType S.sig [] (σ n B) B) (p : HOLProp S) :
    HOLProp S :=
  ⟨p.1.freeSubst σ, p.2.freeSubst σ hσ⟩

/-- `⊥` (HOL Light's defined falsity). -/
def falsity : HOLProp S := ⟨Tm.falsity, HasType.falsity⟩

/-- `p ∨ q` (HOL Light's defined disjunction). -/
def disj (p q : HOLProp S) : HOLProp S := ⟨Tm.disj p.1 q.1, HasType.disj p.2 q.2⟩

/-- The disjunction of a list: `d₀ ∨ (d₁ ∨ (… ∨ ⊥))`. -/
def disjList : List (HOLProp S) → HOLProp S
  | [] => falsity
  | p :: ps => disj p (disjList ps)

end HOLProp

/-- **The HOL Light kernel as `HOLProp* ⊢ HOLProp`** from the axioms `Δ`: a kernel derivation of
`p` whose hypotheses are the members of `Γ`. -/
def kernelFrom (S : HolSig) (Δ : Theory) : System (List (HOLProp S)) (HOLProp S) :=
  fun Γ p => Derives S.sig Δ (Γ.map Subtype.val).toFinset p.1

/-- **Pure HOL derivability**: the kernel with no axioms. -/
def kernel (S : HolSig) : System (List (HOLProp S)) (HOLProp S) := kernelFrom S []

/-- The sentence `Γ ⊢ p` of the HOL institution. -/
def toSeq (Γ : List (HOLProp S)) (p : HOLProp S) :
    Silmaril.Logic.Institution.Metatheory.HOL.Seq S :=
  ⟨(Γ.map Subtype.val).toFinset, p.1, p.2, fun q hq => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hq); exact r.2⟩

/-- The hypothesis-free sentence `⊢ p` of the HOL institution. -/
def closedSen (p : HOLProp S) : Silmaril.Logic.Institution.Metatheory.HOL.Seq S :=
  Silmaril.Logic.Institution.Metatheory.HOL.Seq.closed p.1 p.2

end Silmaril.Consequence.HOL

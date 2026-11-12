module

public import Silmaril.SSA.Isotope.Bridge.Defs
public import Silmaril.Proofs.SSA.Isotope.Bridge.Models

/-!
# Bridge between the legacy and thesis copies of let-iter

Checked results (proofs in `Silmaril.Proofs.SSA.Isotope.Bridge.*`), relating legacy
`Silmaril.Isotope.LetIter.LocallyNameless` and thesis `Silmaril.Thesis.LambdaIter.LocallyNameless`:

* Syntax: `toThesis`/`ofThesis` are mutually inverse (`ofThesis_toThesis`,
  `toThesis_ofThesis`; packaged as `Silmaril.Proofs.SSA.Isotope.Bridge.tmEquiv`) and `toThesis`
  commutes with `rename`, `lift`, `underBinder`, `underTwoBinders`, `bsubst`, `instantiate`
  and `fsubst`. Contexts translate both ways with round trips, preserving `lookup` / `get`.
* Typing, under `TypeCompat` and `InstrCompat`: `hasType_iff`.
* Purity, under `EffCompat`: `pure_iff`; axiom schemes: `coreAxiom_iff`.
* Typed equivalence, under all three: `equiv_iff` (and `eqv_iff` from the thesis side).
* Completeness, closed terms: `semantic_iff_semantic` — legacy model validity iff thesis
  algebra validity, obtained from *both* completeness theorems plus `equiv_iff`; no model
  translation is constructed.

Status table: `docs/projects/ssa.md`.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.Bridge

local notation "LTm" => Silmaril.Isotope.LetIter.LocallyNameless.Tm
local notation "TTm" => Silmaril.Thesis.LambdaIter.LocallyNameless.Tm

/-! ## Syntax -/

section Syntax

variable {ν : Type w} {Φ : Type v}

theorem ofThesis_toThesis {n : Nat} (t : LTm ν Φ n) : ofThesis (toThesis t) = t :=
  Silmaril.Proofs.SSA.Isotope.Bridge.ofThesis_toThesis t

theorem toThesis_ofThesis {n : Nat} (t : TTm ν Φ n) : toThesis (ofThesis t) = t :=
  Silmaril.Proofs.SSA.Isotope.Bridge.toThesis_ofThesis t

theorem toThesis_rename {n m : Nat} (ρ : Fin n → Fin m) (t : LTm ν Φ n) :
    toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.rename ρ t) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.rename ρ (toThesis t) :=
  Silmaril.Proofs.SSA.Isotope.Bridge.toThesis_rename ρ t

theorem toThesis_bsubst {n m : Nat} (σ : Fin n → LTm ν Φ m) (t : LTm ν Φ n) :
    toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.bsubst σ t) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.bsubst (fun i => toThesis (σ i))
        (toThesis t) :=
  Silmaril.Proofs.SSA.Isotope.Bridge.toThesis_bsubst σ t

theorem toThesis_instantiate {n : Nat} (b : LTm ν Φ (n + 1)) (a : LTm ν Φ n) :
    toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.instantiate b a) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.instantiate (toThesis b) (toThesis a) :=
  Silmaril.Proofs.SSA.Isotope.Bridge.toThesis_instantiate b a

theorem toThesis_fsubst [DecidableEq ν] {n : Nat} (x : ν) (s t : LTm ν Φ n) :
    toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst x s t) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.fsubst x (toThesis s) (toThesis t) :=
  Silmaril.Proofs.SSA.Isotope.Bridge.toThesis_fsubst x s t

end Syntax

/-! ## Typing and equivalence -/

section Theory

variable {τ : Type u} [Silmaril.TypeFormers τ] [Silmaril.Thesis.LambdaIter.TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [Silmaril.HasTy Φ τ] [Silmaril.Thesis.LambdaIter.HasTy Φ τ]
variable {ε : Type r} [Silmaril.HasEff Φ ε] [Silmaril.Thesis.LambdaIter.HasEff Φ ε]

/-- Legacy exact typing is inhabitation of thesis exact typing after translation. -/
theorem hasType_iff (hT : TypeCompat τ) (hI : InstrCompat Φ τ)
    {Γ : Silmaril.Isotope.Ctx ν τ} {n : Nat} {β : Silmaril.Isotope.BoundCtx τ n}
    {t : LTm ν Φ n} {A : τ} :
    Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ Γ β t A ↔
      Nonempty (Silmaril.Thesis.LambdaIter.LocallyNameless.HasType Φ (Ctx.toThesis Γ)
        (BoundCtx.toThesis β) (toThesis t) A) :=
  Silmaril.Proofs.SSA.Isotope.Bridge.hasType_iff hT hI

omit [DecidableEq ν] in
/-- Syntactic purity is preserved and reflected. -/
theorem pure_iff (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {t : LTm ν Φ n} :
    Silmaril.Isotope.LetIter.LocallyNameless.Pure pe t ↔
      Silmaril.Thesis.LambdaIter.LocallyNameless.Pure pe (toThesis t) :=
  Silmaril.Proofs.SSA.Isotope.Bridge.pure_iff hE pe

omit [DecidableEq ν] in
/-- The raw axiom schemes correspond one to one. -/
theorem coreAxiom_iff (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {a b : LTm ν Φ n} :
    Silmaril.Isotope.LetIter.LocallyNameless.CoreAxiom pe a b ↔
      Silmaril.Thesis.LambdaIter.LocallyNameless.CoreAxiom pe (toThesis a) (toThesis b) :=
  Silmaril.Proofs.SSA.Isotope.Bridge.coreAxiom_iff hE pe

/-- **Equivalence bridge.** -/
theorem equiv_iff (hT : TypeCompat τ) (hI : InstrCompat Φ τ) (hE : EffCompat Φ ε)
    (pe : ε) {Γ : Silmaril.Isotope.Ctx ν τ} {n : Nat} {β : Silmaril.Isotope.BoundCtx τ n}
    {a b : LTm ν Φ n} {A : τ} :
    Silmaril.Isotope.LetIter.LocallyNameless.Equiv pe Γ β a b A ↔
      Silmaril.Thesis.LambdaIter.LocallyNameless.Eqv pe (Ctx.toThesis Γ) (BoundCtx.toThesis β)
        (toThesis a) (toThesis b) A :=
  Silmaril.Proofs.SSA.Isotope.Bridge.equiv_iff hT hI hE pe

/-- The equivalence bridge read from the thesis side. -/
theorem eqv_iff (hT : TypeCompat τ) (hI : InstrCompat Φ τ) (hE : EffCompat Φ ε)
    (pe : ε) {Γ : Silmaril.Thesis.LambdaIter.Ctx ν τ} {n : Nat}
    {β : Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx τ n} {a b : TTm ν Φ n} {A : τ} :
    Silmaril.Thesis.LambdaIter.LocallyNameless.Eqv pe Γ β a b A ↔
      Silmaril.Isotope.LetIter.LocallyNameless.Equiv pe (Ctx.ofThesis Γ) (BoundCtx.ofThesis β)
        (ofThesis a) (ofThesis b) A :=
  Silmaril.Proofs.SSA.Isotope.Bridge.eqv_iff hT hI hE pe

end Theory

/-! ## Completeness -/

section Models

variable {τ Φ ε : Type u}
variable [Silmaril.TypeFormers τ] [Silmaril.Thesis.LambdaIter.TypeFormers τ]
variable [Silmaril.HasTy Φ τ] [Silmaril.Thesis.LambdaIter.HasTy Φ τ]
variable [Silmaril.HasEff Φ ε] [Silmaril.Thesis.LambdaIter.HasEff Φ ε]

/-- **Semantic validity agrees** on closed typable terms (via both completeness theorems). -/
theorem semantic_iff_semantic (hT : TypeCompat τ) (hI : InstrCompat Φ τ)
    (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {β : Silmaril.Isotope.BoundCtx τ n}
    {a b : LTm Empty Φ n} {A : τ}
    (ha : Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ
      (Silmaril.Isotope.Ctx.nil : Silmaril.Isotope.Ctx Empty τ) β a A)
    (hb : Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ
      (Silmaril.Isotope.Ctx.nil : Silmaril.Isotope.Ctx Empty τ) β b A)
    (da : Silmaril.Thesis.LambdaIter.LocallyNameless.HasType (thesisSig τ Φ ε pe).Instr
      Silmaril.Thesis.LambdaIter.Ctx.nil (BoundCtx.toThesis β) (toThesis a) A)
    (db : Silmaril.Thesis.LambdaIter.LocallyNameless.HasType (thesisSig τ Φ ε pe).Instr
      Silmaril.Thesis.LambdaIter.Ctx.nil (BoundCtx.toThesis β) (toThesis b) A) :
    (∀ M : Silmaril.Isotope.LetIter.LocallyNameless.Models.EquationalModels (Φ := Φ) pe
        (Silmaril.Isotope.Ctx.nil : Silmaril.Isotope.Ctx Empty τ),
      Silmaril.Isotope.LetIter.LocallyNameless.Models.interpret M ha =
        Silmaril.Isotope.LetIter.LocallyNameless.Models.interpret M hb) ↔
      ∀ X : Silmaril.Thesis.LambdaIter.Alg.{u, u} (thesisSig τ Φ ε pe),
        X.denote da = X.denote db :=
  Silmaril.Proofs.SSA.Isotope.Bridge.semantic_iff_semantic hT hI hE pe ha hb da db

end Models

end Silmaril.Isotope.Bridge

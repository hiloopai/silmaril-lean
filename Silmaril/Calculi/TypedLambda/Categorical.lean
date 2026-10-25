module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Silmaril.Calculi.TypedLambda.Context
public import Silmaril.Calculi.TypedLambda.Morphism

/-! # Categorical semantics of typed λ-calculi

The interpretation of a typed λ-calculus over a signature (`Term S Γ τ`) in any
cartesian closed category `C`. Cartesian closure is stated with Mathlib's
non-deprecated classes: a `CartesianMonoidalCategory` (chosen finite products,
with `⊗` the product and `𝟙_ C` terminal) that is `MonoidalClosed`.

A `CatModel S C` assigns an object to each base type and a morphism to each
operator. Then:

* a type denotes an object: `σ ⤳ τ` denotes the internal hom
  `(ihom ⟦σ⟧).obj ⟦τ⟧`;
* a context `a :: Γ` denotes `⟦a⟧ ⊗ ⟦Γ⟧`, and `[]` the unit `𝟙_ C`. The newest
  variable is the *left* factor because Mathlib's currying
  `curry : (A ⊗ Y ⟶ X) → (Y ⟶ (ihom A).obj X)` closes the left factor;
* a term `Γ ⊢ t : τ` denotes a morphism `⟦Γ⟧ ⟶ ⟦τ⟧`: variables are
  projections, abstraction is `curry`, application pairs the argument with the
  function and evaluates, and an operator is precomposed with the tuple of its
  arguments.

Renamings and substitutions denote morphisms between context objects
(`renMor`, `substMor`), and the interpretation commutes with them
(`interp_rename`, `interp_subst`). Consequently β and η hold
(`interp_beta`, `interp_eta`) and the interpretation is compositional
(`interp_plug_eq`). Finally, the interpretation is stable under signature
morphisms: translating operators to derived operators corresponds to the
pulled-back model (`interp_translate`, `interp_mapOp`).

The construction is independent of a particular domain model. The typed syntax
and substitution vocabulary follows `lennonbertrand2024lecture` in `references.bib`;
the interpretation here is parameterized by a cartesian closed category.
-/

@[expose] public section

namespace Silmaril.Calculi.TypedLambda

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open Cslib.LambdaCalculus.LocallyNameless.Stlc

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- The object denoted by a type, given objects for the base types: function
types denote internal homs. -/
@[reducible] def Ty.obj {B : Type} (base : B → C) : Ty B → C
  | .base b => base b
  | .arrow σ τ => (ihom (Ty.obj base σ)).obj (Ty.obj base τ)

/-- The object denoted by a context: the product of its types, newest variable
on the left, with the unit for the empty context. -/
@[reducible] def Ctx.obj {B : Type} (base : B → C) : List (Ty B) → C
  | [] => 𝟙_ C
  | a :: Γ => Ty.obj base a ⊗ Ctx.obj base Γ

/-- The projection of a context object onto a variable. -/
def Ctx.proj {B : Type} (base : B → C) :
    {Γ : List (Ty B)} → {a : Ty B} → Var Γ a → (Ctx.obj base Γ ⟶ Ty.obj base a)
  | _, _, .zero => fst _ _
  | _, _, .succ x => snd _ _ ≫ Ctx.proj base x

/-- The morphism into a context object with the given components. -/
def Ctx.tuple {B : Type} (base : B → C) {X : C} :
    {as : List (Ty B)} → (∀ a, Var as a → (X ⟶ Ty.obj base a)) → (X ⟶ Ctx.obj base as)
  | [], _ => toUnit X
  | _ :: _, f => CartesianMonoidalCategory.lift (f _ .zero) (Ctx.tuple base fun a x => f a x.succ)

/-- A model of a signature in a cartesian closed category: an object for each
base type and a morphism from the product of its arguments for each
operator. -/
structure CatModel (S : Signature) (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]
    [MonoidalClosed C] where
  /-- The object denoted by each base type. -/
  base : S.Base → C
  /-- The morphism denoted by each operator. -/
  op : {as : List (Ty S.Base)} → {τ : Ty S.Base} → S.Op as τ →
    (Ctx.obj base as ⟶ Ty.obj base τ)

namespace CatModel

variable {S : Signature} (M : CatModel S C)

/-- The object `⟦τ⟧`. -/
abbrev ty (τ : Ty S.Base) : C := Ty.obj M.base τ

/-- The object `⟦Γ⟧`. -/
abbrev ctx (Γ : Ctx S.Base) : C := Ctx.obj M.base Γ

variable {M}

@[simp] theorem ty_arrow (σ τ : Ty S.Base) : M.ty (σ ⤳ τ) = (ihom (M.ty σ)).obj (M.ty τ) :=
  rfl

@[simp] theorem ctx_cons (a : Ty S.Base) (Γ : Ctx S.Base) : M.ctx (a :: Γ) = M.ty a ⊗ M.ctx Γ :=
  rfl

@[simp] theorem ctx_nil : M.ctx [] = 𝟙_ C := rfl

variable (M)

/-- The projection of a context onto a variable. -/
def varMor {Γ : Ctx S.Base} {a : Ty S.Base} (x : Var Γ a) : M.ctx Γ ⟶ M.ty a :=
  Ctx.proj M.base x

/-- The morphism into a context object with the given components. -/
def tupleMor {X : C} {as : List (Ty S.Base)} (f : ∀ a, Var as a → (X ⟶ M.ty a)) :
    X ⟶ M.ctx as :=
  Ctx.tuple M.base f

/-- The interpretation of a term `Γ ⊢ t : τ` as a morphism `⟦Γ⟧ ⟶ ⟦τ⟧`. -/
def interp : {Γ : Ctx S.Base} → {τ : Ty S.Base} → Term S Γ τ → (M.ctx Γ ⟶ M.ty τ)
  | _, _, .var x => M.varMor x
  | _, _, .lam t => curry (interp t)
  | _, _, .app t u => CartesianMonoidalCategory.lift (interp u) (interp t) ≫ (ihom.ev _).app _
  | _, _, .op o args => M.tupleMor (fun a x => interp (args a x)) ≫ M.op o

/-- The morphism `⟦Δ⟧ ⟶ ⟦Γ⟧` denoted by a renaming `Γ → Δ`. -/
def renMor {Γ Δ : Ctx S.Base} (ρ : Ren Γ Δ) : M.ctx Δ ⟶ M.ctx Γ :=
  M.tupleMor fun a x => M.varMor (ρ a x)

/-- The morphism `⟦Δ⟧ ⟶ ⟦Γ⟧` denoted by a substitution `Γ → Δ`. -/
def substMor {Γ Δ : Ctx S.Base} (s : Subst S Γ Δ) : M.ctx Δ ⟶ M.ctx Γ :=
  M.tupleMor fun a x => M.interp (s a x)

variable {M}

variable {Γ Δ : Ctx S.Base} {σ τ : Ty S.Base}

@[simp] theorem varMor_zero : M.varMor (.zero : Var (σ :: Γ) σ) = fst _ _ := rfl

@[simp] theorem varMor_succ (x : Var Γ τ) :
    M.varMor (.succ x : Var (σ :: Γ) τ) = snd _ _ ≫ M.varMor x := rfl

@[simp] theorem tupleMor_nil {X : C} (f : ∀ a, Var [] a → (X ⟶ M.ty a)) :
    M.tupleMor f = toUnit X := rfl

@[simp] theorem tupleMor_cons {X : C} {as : List (Ty S.Base)}
    (f : ∀ a, Var (σ :: as) a → (X ⟶ M.ty a)) :
    M.tupleMor f = CartesianMonoidalCategory.lift (f _ .zero) (M.tupleMor fun a x => f a x.succ) :=
  rfl

@[simp] theorem interp_var (x : Var Γ τ) : M.interp (.var x) = M.varMor x := rfl

@[simp] theorem interp_lam (t : Term S (σ :: Γ) τ) : M.interp (.lam t) = curry (M.interp t) :=
  rfl

@[simp] theorem interp_app (t : Term S Γ (σ ⤳ τ)) (u : Term S Γ σ) :
    M.interp (.app t u) =
      CartesianMonoidalCategory.lift (M.interp u) (M.interp t) ≫ (ihom.ev _).app _ := rfl

@[simp] theorem interp_op {as : List (Ty S.Base)} (o : S.Op as τ) (args : Tuple (Term S Γ) as) :
    M.interp (.op o args) = M.tupleMor (fun a x => M.interp (args a x)) ≫ M.op o := rfl

/-! ### Tuples of morphisms -/

/-- Projecting a tuple of morphisms onto a variable gives its component. -/
@[simp] theorem tupleMor_comp_varMor {X : C} {as : List (Ty S.Base)} {a : Ty S.Base}
    (f : ∀ a, Var as a → (X ⟶ M.ty a)) (x : Var as a) : M.tupleMor f ≫ M.varMor x = f _ x := by
  induction x with
  | zero => exact lift_fst _ _
  | succ x ih =>
      rw [varMor_succ, tupleMor_cons, ← Category.assoc, lift_snd]
      exact ih _

/-- Precomposition distributes over the components of a tuple. -/
theorem comp_tupleMor {X Y : C} {as : List (Ty S.Base)} (g : Y ⟶ X)
    (f : ∀ a, Var as a → (X ⟶ M.ty a)) :
    g ≫ M.tupleMor f = M.tupleMor fun a x => g ≫ f a x := by
  induction as with
  | nil => exact toUnit_unique _ _
  | cons b as ih => rw [tupleMor_cons, tupleMor_cons, comp_lift, ih]

/-- Every morphism into a context object is the tuple of its projections. -/
theorem tupleMor_eta {X : C} {as : List (Ty S.Base)} (g : X ⟶ M.ctx as) :
    M.tupleMor (fun _ x => g ≫ M.varMor x) = g := by
  induction as with
  | nil => exact toUnit_unique _ _
  | cons b as ih =>
      rw [tupleMor_cons]
      refine hom_ext _ _ (by rw [lift_fst]; rfl) ?_
      rw [lift_snd]
      simp only [varMor_succ, ← Category.assoc]
      exact ih _

/-- Morphisms into a context object with the same projections are equal. -/
theorem tupleMor_ext {X : C} {as : List (Ty S.Base)} {g h : X ⟶ M.ctx as}
    (H : ∀ a (x : Var as a), g ≫ M.varMor x = h ≫ M.varMor x) : g = h := by
  rw [← tupleMor_eta g, ← tupleMor_eta h]
  congr 1
  funext a x
  exact H a x

/-- The tuple of all projections is the identity. -/
@[simp] theorem tupleMor_varMor {as : List (Ty S.Base)} :
    M.tupleMor (fun _ x => M.varMor x) = 𝟙 (M.ctx as) := by
  simpa using tupleMor_eta (M := M) (𝟙 (M.ctx as))

/-! ### Renaming -/

/-- Weakening denotes the second projection. -/
@[simp] theorem renMor_weak : M.renMor (Ren.weak (σ := σ) (Γ := Γ)) = snd _ _ := by
  refine tupleMor_ext fun a x => ?_
  rw [renMor, tupleMor_comp_varMor]
  rfl

/-- Lifting a renaming under a binder denotes whiskering. -/
theorem renMor_lift (ρ : Ren Γ Δ) : M.renMor (Ren.lift (σ := σ) ρ) = M.ty σ ◁ M.renMor ρ := by
  refine tupleMor_ext fun a x => ?_
  rw [renMor, tupleMor_comp_varMor]
  cases x with
  | zero => exact (whiskerLeft_fst _ _).symm
  | succ x =>
      rw [Ren.lift_succ, varMor_succ, varMor_succ, whiskerLeft_snd_assoc, renMor,
        tupleMor_comp_varMor]

/-- The interpretation commutes with renaming. -/
theorem interp_rename (ρ : Ren Γ Δ) (t : Term S Γ τ) :
    M.interp (t.rename ρ) = M.renMor ρ ≫ M.interp t := by
  induction t generalizing Δ with
  | var x => rw [Term.rename, interp_var, interp_var, renMor, tupleMor_comp_varMor]
  | lam t ih =>
      rw [Term.rename, interp_lam, interp_lam, ih, renMor_lift, curry_natural_left]
  | app t u iht ihu =>
      rw [Term.rename, interp_app, interp_app, iht, ihu, ← comp_lift_assoc]
  | op o args ih =>
      rw [Term.rename, interp_op, interp_op, ← Category.assoc, comp_tupleMor]
      simp only [ih]

/-- Weakening a term precomposes its interpretation with the second
projection. -/
@[simp] theorem interp_weaken (t : Term S Γ τ) :
    M.interp (t.weaken (σ := σ)) = snd _ _ ≫ M.interp t := by
  rw [Term.weaken, interp_rename, renMor_weak]

/-! ### Substitution -/

/-- Lifting a substitution under a binder denotes whiskering. -/
theorem substMor_lift (s : Subst S Γ Δ) :
    M.substMor (Subst.lift (σ := σ) s) = M.ty σ ◁ M.substMor s := by
  refine tupleMor_ext fun a x => ?_
  rw [substMor, tupleMor_comp_varMor]
  cases x with
  | zero => exact (whiskerLeft_fst _ _).symm
  | succ x =>
      rw [Subst.lift_succ, interp_weaken, varMor_succ, whiskerLeft_snd_assoc, substMor,
        tupleMor_comp_varMor]

/-- The interpretation commutes with substitution. -/
theorem interp_subst (s : Subst S Γ Δ) (t : Term S Γ τ) :
    M.interp (t.subst s) = M.substMor s ≫ M.interp t := by
  induction t generalizing Δ with
  | var x => rw [Term.subst, interp_var, substMor, tupleMor_comp_varMor]
  | lam t ih =>
      rw [Term.subst, interp_lam, interp_lam, ih, substMor_lift, curry_natural_left]
  | app t u iht ihu =>
      rw [Term.subst, interp_app, interp_app, iht, ihu, ← comp_lift_assoc]
  | op o args ih =>
      rw [Term.subst, interp_op, interp_op, ← Category.assoc, comp_tupleMor]
      simp only [ih]

/-- Single substitution denotes pairing with the identity. -/
theorem substMor_single (u : Term S Γ σ) :
    M.substMor (Subst.single u) = CartesianMonoidalCategory.lift (M.interp u) (𝟙 _) := by
  refine tupleMor_ext fun a x => ?_
  rw [substMor, tupleMor_comp_varMor]
  cases x with
  | zero => exact (lift_fst _ _).symm
  | succ x =>
      rw [varMor_succ, lift_snd_assoc, Category.id_comp]
      rfl

/-- The substitution lemma: `⟦t[u/x]⟧ = ⟨⟦u⟧, id⟩ ≫ ⟦t⟧`. -/
theorem interp_subst1 (t : Term S (σ :: Γ) τ) (u : Term S Γ σ) :
    M.interp (t.subst1 u) = CartesianMonoidalCategory.lift (M.interp u) (𝟙 _) ≫ M.interp t := by
  rw [Term.subst1, interp_subst, substMor_single]

/-! ### β, η and compositionality -/

/-- The interpretation validates β-conversion. -/
theorem interp_beta (t : Term S (σ :: Γ) τ) (u : Term S Γ σ) :
    M.interp (.app (.lam t) u) = M.interp (t.subst1 u) := by
  rw [interp_subst1, interp_app, interp_lam]
  have h : CartesianMonoidalCategory.lift (M.interp u) (curry (M.interp t)) =
      CartesianMonoidalCategory.lift (M.interp u) (𝟙 _) ≫ (M.ty σ ◁ curry (M.interp t)) := by
    rw [lift_whiskerLeft, Category.id_comp]
  rw [h, Category.assoc, whiskerLeft_curry_ihom_ev_app]

/-- The interpretation validates η-conversion. -/
theorem interp_eta (t : Term S Γ (σ ⤳ τ)) :
    M.interp (.lam (.app t.weaken (.var .zero))) = M.interp t := by
  rw [interp_lam, interp_app, interp_weaken, interp_var, varMor_zero,
    ← Category.comp_id (fst _ _), lift_fst_comp_snd_comp, id_tensorHom, ← uncurry_eq,
    curry_uncurry]

/-- Compositionality: terms with equal interpretations have equal
interpretations in every context. -/
theorem interp_plug_eq {t u : Term S Δ σ} (h : M.interp t = M.interp u)
    (K : Context S Δ σ Γ τ) : M.interp (K.plug t) = M.interp (K.plug u) := by
  induction K with
  | hole => exact h
  | lam K ih => rw [Context.plug, Context.plug, interp_lam, interp_lam, ih]
  | appL K v ih => rw [Context.plug, Context.plug, interp_app, interp_app, ih]
  | appR g K ih => rw [Context.plug, Context.plug, interp_app, interp_app, ih]
  | op o args x K ih =>
      rw [Context.plug, Context.plug, interp_op, interp_op]
      have e : ∀ w : Term S _ _, (fun a y => M.interp (args.set x w a y)) =
          (Tuple.map (fun _ r => M.interp r) args).set x (M.interp w) := fun w =>
        Tuple.map_set (fun _ r => M.interp r) args x w
      rw [e, e, ih]

/-! ### Signature morphisms -/

section Translate

variable {Op' : List (Ty S.Base) → Ty S.Base → Type}

/-- The model of `S` induced by a model of `S.withOps Op'` and an
interpretation of each operator of `S` as a derived operator. -/
def comapTranslate (M' : CatModel (S.withOps Op') C)
    (F : ∀ {as : List (Ty S.Base)} {τ : Ty S.Base}, S.Op as τ → Term (S.withOps Op') as τ) :
    CatModel S C where
  base := M'.base
  op o := M'.interp (F o)

/-- The model of `S` induced by a model of `S.withOps Op'` along an operator
translation. -/
def comapOp (M' : CatModel (S.withOps Op') C) (f : OpMap S Op') : CatModel S C where
  base := M'.base
  op o := M'.op (f o)

/-- Interpreting a translated term in `M'` is interpreting the original term in
the induced model. -/
theorem interp_translate (M' : CatModel (S.withOps Op') C)
    (F : ∀ {as : List (Ty S.Base)} {τ : Ty S.Base}, S.Op as τ → Term (S.withOps Op') as τ)
    (t : Term S Γ τ) : M'.interp (t.translate F) = (M'.comapTranslate F).interp t := by
  induction t with
  | var x => rfl
  | lam t ih => rw [Term.translate, interp_lam, interp_lam, ih]; rfl
  | app t u iht ihu => rw [Term.translate, interp_app, interp_app, iht, ihu]; rfl
  | op o args ih =>
      rw [Term.translate, interp_subst, interp_op]
      simp only [substMor, ih]
      rfl

/-- Interpreting a term with translated operators in `M'` is interpreting the
original term in the induced model. -/
theorem interp_mapOp (M' : CatModel (S.withOps Op') C) (f : OpMap S Op') (t : Term S Γ τ) :
    M'.interp (t.mapOp f) = (M'.comapOp f).interp t := by
  induction t with
  | var x => rfl
  | lam t ih => rw [Term.mapOp, interp_lam, interp_lam, ih]; rfl
  | app t u iht ihu => rw [Term.mapOp, interp_app, interp_app, iht, ihu]; rfl
  | op o args ih =>
      rw [Term.mapOp, interp_op, interp_op]
      simp only [ih]
      rfl

end Translate

end CatModel

end Silmaril.Calculi.TypedLambda

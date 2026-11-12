module

public import Silmaril.Logic.Institution.Borrowing

@[expose] public section

/-!
# Observational semantics as institutions

A generic construction turning a *refinement relation on semantic objects over interfaces* into
an institution (a functor `Sign ⥤ Room`, `Silmaril.Logic.Institution.Inst`). It is shared by
the Wasm session logics (`Silmaril.Wasm.Institution.Session`), the single-invocation logics
(`Silmaril.Wasm.Institution.Entry`) and, in phase 2, component and game-semantic logics
(`Silmaril.Wasm.Institution.Hooks`).

## Input: `ObsSemantics Iface`

* an interface category `Iface` (for Wasm: sets of export names under inclusion);
* semantic objects `Sem X` of each interface `X`, with a contravariant, strictly functorial
  *reduct* `restrict : (X ⟶ Y) → Sem Y → Sem X` (for Wasm: hide the exports outside `X`);
* concrete programs `Prog` with a denotation `den X : Prog → Sem X` at every interface;
* unary semantic operators `Op` (for Wasm: closure of a behaviour set under a behaviour
  relation, used to express one refinement notion inside another);
* the refinement relation `Le X : Sem X → Sem X → Prop` at each interface. No preorder laws are
  required by the construction.

## The institution `S.inst`

* **Signatures** `Sig Iface`: a type `V` of *program variables* (unknown components) and an
  interface `X`. A morphism renames variables and includes/renames interfaces.
* **Models** at `(V, X)`: assignments `V → Sem X` of semantic objects to the program variables.
  Models are *semantic interpretations*, not programs: a model may assign any semantic object
  of the interface, whether or not some program denotes it (loose semantics, as for
  specifications of unknown components). Concrete programs are not interpreted by models; they
  occur as constants with their fixed denotation. Model morphisms are equalities (a discrete
  category, with `PLift` homs so that reducts are functors by `rfl`). The model reduct along
  `(f, σ)` renames the variables along `f` and restricts every value along `σ`.
* **Sentences** at `(V, X)`: a formula `φ` over terms `x | ⟨p⟩ | o(t)` together with an
  *observation scope* `τ : Z ⟶ X`. Sentence translation renames variables and composes the
  scope with `σ`. The scope is part of the sentence because refinement is not invariant under
  enlarging the interface: two programs indistinguishable through `Z` may be distinguished
  through `X ⊇ Z`. A sentence observed through `Z` keeps meaning "observed through `Z`" in every
  larger signature; this is the usual treatment of observers in observational logics.
* **Satisfaction**: `β ⊨ (τ, φ)` iff `φ` holds when each variable denotes the `τ`-reduct of its
  value, each program its denotation at `Z`, and `t ⊑ u` means `Le Z ⟦t⟧ ⟦u⟧`; `t ≐ u` means
  both refinements; `∧` is conjunction.

The satisfaction condition (`ObsSemantics.sat_map_iff`) holds by the strict functoriality of
`restrict` alone; it needs no naturality of `den`, `op` or monotonicity of `Le`.

## Translations

`ObsSemantics.Translation F A B` (over an interface functor `F : I ⥤ J`) maps `B`-semantic
objects to `A`-semantic objects naturally, `A`-programs and operators to `B`-ones, and each
`A`-atom `t ⊑ u` to a `B`-formula with the same meaning. It yields an institution comorphism
`A.inst → B.inst` (`Translation.coHom`), which is model-expansive when each semantic map is
surjective, so that entailment is *borrowed* (`Translation.entails_iff`).
-/

namespace Silmaril.Wasm.Institution

open CategoryTheory Silmaril.Logic.Institution

/-! ## Terms and formulas -/

/-- Terms over programs `P`, operators `O` and variables `V`. -/
inductive Term (P O V : Type) : Type where
  /-- A program variable (an unknown component). -/
  | var (x : V)
  /-- A concrete program. -/
  | prog (p : P)
  /-- A semantic operator applied to a term. -/
  | app (o : O) (t : Term P O V)

namespace Term

variable {P O V W U : Type}

/-- Rename the variables of a term. -/
def mapVars (f : V → W) : Term P O V → Term P O W
  | var x => var (f x)
  | prog p => prog p
  | app o t => app o (mapVars f t)

@[simp] theorem mapVars_id (t : Term P O V) : t.mapVars id = t := by
  induction t with
  | var x => rfl
  | prog p => rfl
  | app o t ih => exact congrArg (app o) ih

theorem mapVars_mapVars (f : V → W) (g : W → U) (t : Term P O V) :
    (t.mapVars f).mapVars g = t.mapVars (g ∘ f) := by
  induction t with
  | var x => rfl
  | prog p => rfl
  | app o t ih => exact congrArg (app o) ih

end Term

/-- Formulas over atomic terms `T`: refinements, equations (refinement both ways) and
conjunctions. -/
inductive Formula (T : Type) : Type where
  /-- `a ⊑ b`: `a` refines (implements) `b`. -/
  | le (a b : T)
  /-- `a ≐ b`: `a ⊑ b` and `b ⊑ a`. -/
  | eq (a b : T)
  /-- Conjunction. -/
  | and (φ ψ : Formula T)

namespace Formula

variable {T T' T'' : Type}

/-- Translate the atomic terms of a formula. -/
def map (f : T → T') : Formula T → Formula T'
  | le a b => le (f a) (f b)
  | eq a b => eq (f a) (f b)
  | and φ ψ => and (map f φ) (map f ψ)

/-- Replace every refinement atom `a ⊑ b` by a formula `atom a b` (an equation `a ≐ b` becomes
`atom a b ∧ atom b a`). -/
def bindLe (atom : T → T → Formula T') : Formula T → Formula T'
  | le a b => atom a b
  | eq a b => and (atom a b) (atom b a)
  | and φ ψ => and (bindLe atom φ) (bindLe atom ψ)

/-- Truth of a formula, given the meaning of refinement atoms. -/
def Holds (r : T → T → Prop) : Formula T → Prop
  | le a b => r a b
  | eq a b => r a b ∧ r b a
  | and φ ψ => Holds r φ ∧ Holds r ψ

@[simp] theorem map_id (φ : Formula T) : φ.map id = φ := by
  induction φ with
  | le => rfl
  | eq => rfl
  | and φ ψ ih₁ ih₂ => exact congrArg₂ and ih₁ ih₂

theorem map_map (f : T → T') (g : T' → T'') (φ : Formula T) :
    (φ.map f).map g = φ.map (g ∘ f) := by
  induction φ with
  | le => rfl
  | eq => rfl
  | and φ ψ ih₁ ih₂ => exact congrArg₂ and ih₁ ih₂

theorem map_congr {f g : T → T'} (h : ∀ a, f a = g a) (φ : Formula T) : φ.map f = φ.map g := by
  rw [funext h]

theorem holds_congr {r r' : T → T → Prop} (h : ∀ a b, r a b ↔ r' a b) (φ : Formula T) :
    φ.Holds r ↔ φ.Holds r' := by
  induction φ with
  | le a b => exact h a b
  | eq a b => exact and_congr (h a b) (h b a)
  | and φ ψ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem holds_map (r : T' → T' → Prop) (f : T → T') (φ : Formula T) :
    (φ.map f).Holds r ↔ φ.Holds (fun a b => r (f a) (f b)) := by
  induction φ with
  | le => exact Iff.rfl
  | eq => exact Iff.rfl
  | and φ ψ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem holds_bindLe (r : T' → T' → Prop) (atom : T → T → Formula T') (φ : Formula T) :
    (φ.bindLe atom).Holds r ↔ φ.Holds (fun a b => (atom a b).Holds r) := by
  induction φ with
  | le => exact Iff.rfl
  | eq => exact Iff.rfl
  | and φ ψ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem map_bindLe (atom : T → T → Formula T') (g : T' → T'') (φ : Formula T) :
    (φ.bindLe atom).map g = φ.bindLe (fun a b => (atom a b).map g) := by
  induction φ with
  | le => rfl
  | eq => rfl
  | and φ ψ ih₁ ih₂ => exact congrArg₂ and ih₁ ih₂

theorem bindLe_map (atom : T' → T' → Formula T'') (f : T → T') (φ : Formula T) :
    (φ.map f).bindLe atom = φ.bindLe (fun a b => atom (f a) (f b)) := by
  induction φ with
  | le => rfl
  | eq => rfl
  | and φ ψ ih₁ ih₂ => exact congrArg₂ and ih₁ ih₂

theorem bindLe_congr {atom atom' : T → T → Formula T'} (h : ∀ a b, atom a b = atom' a b)
    (φ : Formula T) : φ.bindLe atom = φ.bindLe atom' := by
  induction φ with
  | le a b => exact h a b
  | eq a b => exact congrArg₂ and (h a b) (h b a)
  | and φ ψ ih₁ ih₂ => exact congrArg₂ and ih₁ ih₂

end Formula

/-! ## Signatures -/

/-- A signature: program variables and an interface. -/
structure Sig (Iface : Type) where
  /-- Program variables (names of unknown components). -/
  V : Type
  /-- The interface through which programs are observed. -/
  iface : Iface

/-- A signature morphism: a renaming of variables and a morphism of interfaces. -/
@[ext] structure Sig.Hom {Iface : Type} [Category.{0} Iface] (A B : Sig Iface) where
  /-- Variable renaming. -/
  ren : A.V → B.V
  /-- Interface morphism (for Wasm: an inclusion of export sets). -/
  sub : A.iface ⟶ B.iface

instance Sig.category {Iface : Type} [Category.{0} Iface] : Category.{0} (Sig Iface) where
  Hom := Sig.Hom
  id A := ⟨id, 𝟙 A.iface⟩
  comp f g := ⟨g.ren ∘ f.ren, f.sub ≫ g.sub⟩
  id_comp f := Sig.Hom.ext rfl (Category.id_comp f.sub)
  comp_id f := Sig.Hom.ext rfl (Category.comp_id f.sub)
  assoc f g h := Sig.Hom.ext rfl (Category.assoc f.sub g.sub h.sub)

namespace Sig

variable {I J : Type} [Category.{0} I] [Category.{0} J]

@[simp] theorem id_ren (A : Sig I) : (𝟙 A : A ⟶ A).ren = id := rfl
@[simp] theorem id_sub (A : Sig I) : (𝟙 A : A ⟶ A).sub = 𝟙 A.iface := rfl
@[simp] theorem comp_ren {A B C : Sig I} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).ren = g.ren ∘ f.ren := rfl
@[simp] theorem comp_sub {A B C : Sig I} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).sub = f.sub ≫ g.sub := rfl

/-- An interface functor acts on signatures, leaving the variables alone. -/
def map (F : I ⥤ J) : Sig I ⥤ Sig J where
  obj A := ⟨A.V, F.obj A.iface⟩
  map f := ⟨f.ren, F.map f.sub⟩
  map_id A := Sig.Hom.ext rfl (F.map_id A.iface)
  map_comp f g := Sig.Hom.ext rfl (F.map_comp f.sub g.sub)

/-- The signature with no variables at interface `X` (concrete programs only). -/
abbrev closed (X : I) : Sig I := ⟨PEmpty, X⟩

end Sig

/-! ## Observational semantics -/

/-- An observational semantics over the interface category `Iface`: semantic objects with
strictly functorial reducts, concrete programs with denotations, semantic operators, and a
refinement relation at each interface. -/
structure ObsSemantics (Iface : Type) [Category.{0} Iface] where
  /-- Semantic objects of an interface (the values of program variables in models). -/
  Sem : Iface → Type
  /-- The reduct of a semantic object along an interface morphism (hiding/renaming). -/
  restrict : ∀ {X Y : Iface}, (X ⟶ Y) → Sem Y → Sem X
  restrict_id : ∀ {X : Iface} (a : Sem X), restrict (𝟙 X) a = a
  restrict_comp : ∀ {X Y Z : Iface} (f : X ⟶ Y) (g : Y ⟶ Z) (a : Sem Z),
    restrict (f ≫ g) a = restrict f (restrict g a)
  /-- Concrete programs. -/
  Prog : Type
  /-- The denotation of a program at an interface. -/
  den : (X : Iface) → Prog → Sem X
  /-- Semantic operators. -/
  Op : Type
  /-- The meaning of an operator at an interface. -/
  op : (X : Iface) → Op → Sem X → Sem X
  /-- Refinement at an interface: `Le X a b` reads "`a` implements `b`". -/
  Le : (X : Iface) → Sem X → Sem X → Prop

namespace ObsSemantics

variable {Iface : Type} [Category.{0} Iface] (S : ObsSemantics Iface)

/-- The terms of `S` over variables `V`. -/
abbrev Tm (V : Type) : Type := Term S.Prog S.Op V

/-- The formulas of `S` over variables `V`. -/
abbrev Fm (V : Type) : Type := Formula (S.Tm V)

/-- Evaluate a term at interface `Z` under a variable assignment. -/
def eval (Z : Iface) {V : Type} (ρ : V → S.Sem Z) : S.Tm V → S.Sem Z
  | .var x => ρ x
  | .prog p => S.den Z p
  | .app o t => S.op Z o (eval Z ρ t)

/-- The meaning of refinement atoms at `Z` under `ρ`. -/
def LeAt (Z : Iface) {V : Type} (ρ : V → S.Sem Z) (t u : S.Tm V) : Prop :=
  S.Le Z (S.eval Z ρ t) (S.eval Z ρ u)

theorem eval_mapVars (Z : Iface) {V W : Type} (ρ : W → S.Sem Z) (f : V → W) (t : S.Tm V) :
    S.eval Z ρ (t.mapVars f) = S.eval Z (ρ ∘ f) t := by
  induction t with
  | var x => rfl
  | prog p => rfl
  | app o t ih => exact congrArg (S.op Z o) ih

/-- A sentence at signature `A`: an observation scope `obs : scope ⟶ A.iface` and a formula
over the variables of `A`. -/
structure Sen (A : Sig Iface) where
  /-- The interface through which the formula observes. -/
  scope : Iface
  /-- How the scope sits in the signature's interface. -/
  obs : scope ⟶ A.iface
  /-- The formula. -/
  φ : S.Fm A.V

/-- Sentence translation along a signature morphism. -/
def Sen.map {S} {A B : Sig Iface} (f : A ⟶ B) (s : Sen S A) : Sen S B :=
  ⟨s.scope, s.obs ≫ f.sub, s.φ.map (Term.mapVars f.ren)⟩

theorem Sen.map_id {A : Sig Iface} (s : Sen S A) : s.map (𝟙 A) = s := by
  obtain ⟨Z, τ, φ⟩ := s
  simp only [Sen.map, Sig.id_sub, Category.comp_id, Sig.id_ren]
  congr 1
  rw [Formula.map_congr (fun t => Term.mapVars_id t)]
  exact Formula.map_id φ

theorem Sen.map_comp {A B C : Sig Iface} (f : A ⟶ B) (g : B ⟶ C) (s : Sen S A) :
    s.map (f ≫ g) = (s.map f).map g := by
  obtain ⟨Z, τ, φ⟩ := s
  simp only [Sen.map, Sig.comp_sub, Sig.comp_ren, Category.assoc, Formula.map_map]
  congr 1
  exact Formula.map_congr (fun t => (Term.mapVars_mapVars _ _ t).symm) φ

/-- Models at a signature: assignments of semantic objects to the program variables. -/
def Model (A : Sig Iface) : Type := A.V → S.Sem A.iface

/-- The discrete category of models (homs are equalities, wrapped in `PLift`). -/
instance Model.category (A : Sig Iface) : Category.{0} (S.Model A) where
  Hom β β' := PLift (β = β')
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

/-- The model reduct along a signature morphism: rename the variables and restrict values. -/
def reduct {A B : Sig Iface} (f : A ⟶ B) : S.Model B ⥤ S.Model A where
  obj β := fun x => S.restrict f.sub (β (f.ren x))
  map h := ⟨congrArg (fun β : S.Model B => fun x => S.restrict f.sub (β (f.ren x))) h.down⟩

/-- Satisfaction: the formula holds at the scope, with variables denoting the reducts of
their values. -/
def Sat (A : Sig Iface) (β : S.Model A) (s : Sen S A) : Prop :=
  s.φ.Holds (S.LeAt s.scope (fun x => S.restrict s.obs (β x)))

/-- **The satisfaction condition.** -/
theorem sat_map_iff {A B : Sig Iface} (f : A ⟶ B) (β : S.Model B) (s : Sen S A) :
    S.Sat B β (s.map f) ↔ S.Sat A ((S.reduct f).obj β) s := by
  obtain ⟨Z, τ, φ⟩ := s
  simp only [Sat, Sen.map, Formula.holds_map]
  refine Formula.holds_congr (fun t u => ?_) φ
  simp only [LeAt, eval_mapVars]
  have : ((fun y => S.restrict (τ ≫ f.sub) (β y)) ∘ f.ren) =
      (fun x => S.restrict τ (((S.reduct f).obj β) x)) := by
    funext x
    exact S.restrict_comp τ f.sub (β (f.ren x))
  rw [this]

/-- The room of a signature. -/
def room (A : Sig Iface) : Room.{0, 0, 0} :=
  ⟨Sen S A, Cat.of (S.Model A), S.Sat A⟩

/-- The corridor of a signature morphism. -/
def corridor {A B : Sig Iface} (f : A ⟶ B) : S.room A ⟶ S.room B :=
  ⟨Sen.map f, S.reduct f, fun β s => S.sat_map_iff f β s⟩

theorem reduct_id (A : Sig Iface) : S.reduct (𝟙 A) = 𝟭 _ :=
  Functor.ext (fun β => funext fun x => S.restrict_id (β x)) (fun _ _ _ => rfl)

theorem reduct_comp {A B C : Sig Iface} (f : A ⟶ B) (g : B ⟶ C) :
    S.reduct (f ≫ g) = S.reduct g ⋙ S.reduct f :=
  Functor.ext (fun β => funext fun x => S.restrict_comp f.sub g.sub (β (g.ren (f.ren x))))
    (fun _ _ _ => rfl)

/-- **The observational institution of `S`**, as a functor into rooms. -/
def institution : Sig Iface ⥤ Room.{0, 0, 0} where
  obj := S.room
  map := S.corridor
  map_id A := Room.hom_ext (funext fun s => Sen.map_id S s) (S.reduct_id A)
  map_comp f g := Room.hom_ext (funext fun s => Sen.map_comp S f g s) (S.reduct_comp f g)

/-- The observational institution of `S`, bundled. -/
def inst : Inst.{1, 0, 0, 0, 0} := ⟨Sig Iface, S.institution⟩

/-! ### Concrete sentences and validity -/

/-- Validity of a sentence: it holds in every model (consequence of no hypotheses). -/
def Valid {A : Sig Iface} (s : Sen S A) : Prop := (S.room A).Entails ∅ s

theorem valid_iff {A : Sig Iface} (s : Sen S A) : S.Valid s ↔ ∀ β : S.Model A, S.Sat A β s :=
  ⟨fun h β => h β (fun _ h => False.elim h), fun h β _ => h β⟩

/-- A sentence over no variables, observed through the whole interface `X`. -/
def closedSen (X : Iface) (φ : S.Fm PEmpty) : Sen S (Sig.closed X) := ⟨X, 𝟙 X, φ⟩

/-- The concrete refinement `p ⊑ q` at interface `X`. -/
def leSen (X : Iface) (p q : S.Prog) : Sen S (Sig.closed X) :=
  S.closedSen X (.le (.prog p) (.prog q))

/-- The concrete equation `p ≐ q` at interface `X`. -/
def eqSen (X : Iface) (p q : S.Prog) : Sen S (Sig.closed X) :=
  S.closedSen X (.eq (.prog p) (.prog q))

/-- The unique model of a closed signature. -/
def closedModel (X : Iface) : S.Model (Sig.closed X) := fun x => x.elim

theorem valid_closedSen_iff (X : Iface) (φ : S.Fm PEmpty) :
    S.Valid (S.closedSen X φ) ↔ φ.Holds (S.LeAt X (fun x => x.elim)) := by
  rw [valid_iff]
  have key : ∀ β : S.Model (Sig.closed X),
      S.Sat _ β (S.closedSen X φ) ↔ φ.Holds (S.LeAt X (fun x => x.elim)) := by
    intro β
    have : (fun x => S.restrict (𝟙 X) (β x)) = (fun x : PEmpty => x.elim) :=
      funext fun x => x.elim
    simp only [Sat, closedSen, this]
  exact ⟨fun h => (key _).1 (h (S.closedModel X)), fun h β => (key β).2 h⟩

/-- **Validity of a concrete refinement is refinement of denotations.** -/
theorem valid_leSen_iff (X : Iface) (p q : S.Prog) :
    S.Valid (S.leSen X p q) ↔ S.Le X (S.den X p) (S.den X q) :=
  S.valid_closedSen_iff X _

/-- Validity of a concrete equation is two-sided refinement of denotations. -/
theorem valid_eqSen_iff (X : Iface) (p q : S.Prog) :
    S.Valid (S.eqSen X p q) ↔
      S.Le X (S.den X p) (S.den X q) ∧ S.Le X (S.den X q) (S.den X p) :=
  S.valid_closedSen_iff X _

/-! ## Translations and comorphisms -/

variable {I J : Type} [Category.{0} I] [Category.{0} J]

/-- A translation of observational semantics along an interface functor `F : I ⥤ J`:
`B`-semantic objects map naturally to `A`-semantic objects, `A`-programs and operators map to
`B`-ones compatibly with denotations, and each `A`-refinement atom becomes a `B`-formula
(`atom`) whose truth is the `A`-refinement of the mapped values. -/
structure Translation (F : I ⥤ J) (A : ObsSemantics I) (B : ObsSemantics J) where
  /-- Semantic objects map backwards. -/
  sem : ∀ X : I, B.Sem (F.obj X) → A.Sem X
  sem_restrict : ∀ {X Y : I} (f : X ⟶ Y) (b : B.Sem (F.obj Y)),
    sem X (B.restrict (F.map f) b) = A.restrict f (sem Y b)
  /-- Programs map forwards. -/
  prog : A.Prog → B.Prog
  sem_den : ∀ (X : I) (p : A.Prog), sem X (B.den (F.obj X) (prog p)) = A.den X p
  /-- Operators map forwards. -/
  op : A.Op → B.Op
  sem_op : ∀ (X : I) (o : A.Op) (b : B.Sem (F.obj X)),
    sem X (B.op (F.obj X) (op o) b) = A.op X o (sem X b)
  /-- The `B`-formula expressing an `A`-refinement atom. -/
  atom : ∀ {V : Type}, B.Tm V → B.Tm V → B.Fm V
  atom_mapVars : ∀ {V W : Type} (f : V → W) (t u : B.Tm V),
    (atom t u).map (Term.mapVars f) = atom (t.mapVars f) (u.mapVars f)
  atom_holds : ∀ (X : I) {V : Type} (ρ : V → B.Sem (F.obj X)) (t u : B.Tm V),
    (atom t u).Holds (B.LeAt (F.obj X) ρ) ↔
      A.Le X (sem X (B.eval (F.obj X) ρ t)) (sem X (B.eval (F.obj X) ρ u))

namespace Translation

variable {F : I ⥤ J} {A : ObsSemantics I} {B : ObsSemantics J} (T : Translation F A B)

/-- Term translation. -/
def term {V : Type} : A.Tm V → B.Tm V
  | .var x => .var x
  | .prog p => .prog (T.prog p)
  | .app o t => .app (T.op o) (term t)

theorem term_mapVars {V W : Type} (f : V → W) (t : A.Tm V) :
    (T.term t).mapVars f = T.term (t.mapVars f) := by
  induction t with
  | var x => rfl
  | prog p => rfl
  | app o t ih => exact congrArg (Term.app (T.op o)) ih

theorem sem_eval (X : I) {V : Type} (ρ : V → B.Sem (F.obj X)) (t : A.Tm V) :
    T.sem X (B.eval (F.obj X) ρ (T.term t)) = A.eval X (fun x => T.sem X (ρ x)) t := by
  induction t with
  | var x => rfl
  | prog p => exact T.sem_den X p
  | app o t ih =>
    show T.sem X (B.op (F.obj X) (T.op o) (B.eval (F.obj X) ρ (T.term t))) = _
    rw [T.sem_op, ih]
    rfl

/-- Formula translation. -/
def formula {V : Type} (φ : A.Fm V) : B.Fm V :=
  φ.bindLe (fun t u => T.atom (T.term t) (T.term u))

theorem formula_mapVars {V W : Type} (f : V → W) (φ : A.Fm V) :
    (T.formula φ).map (Term.mapVars f) = T.formula (φ.map (Term.mapVars f)) := by
  simp only [formula, Formula.map_bindLe, Formula.bindLe_map]
  refine Formula.bindLe_congr (fun t u => ?_) φ
  rw [T.atom_mapVars, T.term_mapVars, T.term_mapVars]

theorem holds_formula (X : I) {V : Type} (ρ : V → B.Sem (F.obj X)) (φ : A.Fm V) :
    (T.formula φ).Holds (B.LeAt (F.obj X) ρ) ↔
      φ.Holds (A.LeAt X (fun x => T.sem X (ρ x))) := by
  rw [formula, Formula.holds_bindLe]
  refine Formula.holds_congr (fun t u => ?_) φ
  rw [T.atom_holds, T.sem_eval, T.sem_eval]
  rfl

/-- Sentence translation at a signature. -/
def sen {K : Sig I} (s : Sen A K) : Sen B ((Sig.map F).obj K) :=
  ⟨F.obj s.scope, F.map s.obs, T.formula s.φ⟩

/-- Model translation at a signature. -/
def modFun (K : Sig I) : B.Model ((Sig.map F).obj K) ⥤ A.Model K where
  obj β := fun x => T.sem K.iface (β x)
  map h := ⟨congrArg (fun β : B.Model ((Sig.map F).obj K) => fun x => T.sem K.iface (β x))
    h.down⟩

/-- **The satisfaction condition of a translation.** -/
theorem sat_sen_iff (K : Sig I) (β : B.Model ((Sig.map F).obj K)) (s : Sen A K) :
    B.Sat _ β (T.sen s) ↔ A.Sat K ((T.modFun K).obj β) s := by
  obtain ⟨Z, τ, φ⟩ := s
  have hρ : (fun x => T.sem Z (B.restrict (F.map τ) (β x))) =
      (fun x => A.restrict τ (((T.modFun K).obj β) x)) :=
    funext fun x => T.sem_restrict τ (β x)
  refine (T.holds_formula Z (fun x => B.restrict (F.map τ) (β x)) φ).trans ?_
  show φ.Holds (A.LeAt Z (fun x => T.sem Z (B.restrict (F.map τ) (β x)))) ↔
    φ.Holds (A.LeAt Z (fun x => A.restrict τ (((T.modFun K).obj β) x)))
  rw [hρ]
  exact Iff.rfl

/-- The corridor of a translation at a signature. -/
def corridor (K : Sig I) : A.room K ⟶ B.room ((Sig.map F).obj K) :=
  ⟨T.sen, T.modFun K, fun β s => T.sat_sen_iff K β s⟩

theorem sen_map {K₁ K₂ : Sig I} (f : K₁ ⟶ K₂) (s : Sen A K₁) :
    T.sen (s.map f) = (T.sen s).map ((Sig.map F).map f) := by
  obtain ⟨Z, τ, φ⟩ := s
  simp only [sen, Sen.map, Sig.map]
  rw [F.map_comp, T.formula_mapVars]

/-- **The comorphism of a translation**: signatures along `Sig.map F`, sentences forwards,
models backwards, with the satisfaction condition `sat_sen_iff`. -/
def coHom : Inst.CoHom A.inst B.inst where
  Φ := Sig.map F
  ρ :=
    { app := fun K => T.corridor K
      naturality := fun {K₁ K₂} f => by
        apply Room.hom_ext
        · funext s
          exact T.sen_map f s
        · exact Functor.ext (fun β => funext fun x => (T.sem_restrict f.sub (β (f.ren x))).symm)
            (fun _ _ _ => rfl) }

@[simp] theorem coHom_sen (K : Sig I) (s : Sen A K) :
    (T.coHom.ρ.app K).sen s = T.sen s := rfl

/-- A translation whose semantic maps are surjective is model-expansive. -/
theorem coHom_modelExpansive (h : ∀ X, Function.Surjective (T.sem X)) :
    T.coHom.ModelExpansive := by
  intro K α
  exact ⟨fun x => (h K.iface (α x)).choose, funext fun x => (h K.iface (α x)).choose_spec⟩

/-- **Borrowing along a translation**: consequence in `A` is consequence of the translated
sentences in `B`. -/
theorem entails_iff (h : ∀ X, Function.Surjective (T.sem X)) (K : Sig I)
    (Γ : Set (Sen A K)) (s : Sen A K) :
    (A.room K).Entails Γ s ↔ (B.room ((Sig.map F).obj K)).Entails (T.sen '' Γ) (T.sen s) :=
  T.coHom.entails_iff (T.coHom_modelExpansive h) K Γ s

/-- Validity is preserved and reflected along a model-expansive translation. -/
theorem valid_iff (h : ∀ X, Function.Surjective (T.sem X)) {K : Sig I} (s : Sen A K) :
    A.Valid s ↔ B.Valid (T.sen s) := by
  rw [A.valid_iff, B.valid_iff]
  constructor
  · intro hA β
    exact (T.sat_sen_iff K β s).2 (hA _)
  · intro hB α
    obtain ⟨β, hβ⟩ := T.coHom_modelExpansive h K α
    have := (T.sat_sen_iff K β s).1 (hB β)
    rw [show (T.modFun K).obj β = α from hβ] at this
    exact this

end Translation

/-! ### Atom templates -/

/-- The plain template: an `A`-refinement atom becomes the same `B`-refinement atom. -/
def atomLe {S : ObsSemantics J} {V : Type} (t u : S.Tm V) : S.Fm V := .le t u

/-- The equation template: an `A`-refinement atom becomes a `B`-equation (for a logic of
equivalences mapped into a logic of refinements). -/
def atomEq {S : ObsSemantics J} {V : Type} (t u : S.Tm V) : S.Fm V := .eq t u

/-- The closure template: `t ⊑ u` becomes `t ⊑ o(u)`. -/
def atomClose {S : ObsSemantics J} (o : S.Op) {V : Type} (t u : S.Tm V) : S.Fm V :=
  .le t (.app o u)

/-! ### Translations over the identity interface functor as institution morphisms -/

/-- A translation `A → B` over the identity interface functor is also an institution *morphism*
`B → A` (Goguen–Burstall direction): the same corridors, read as projecting `B`-models to
`A`-models and expressing `A`-sentences in `B`. For the contract closure this is the projection
of the `Eq`-refinement logic onto a coarser contract. -/
def Translation.toHom {A B : ObsSemantics I} (T : Translation (𝟭 I) A B) :
    Inst.Hom B.inst A.inst where
  Φ := Sig.map (𝟭 I)
  η :=
    { app := fun K => T.corridor K
      naturality := fun {_ _} f => T.coHom.ρ.naturality f }

/-- The morphism of a translation with surjective semantic maps is sound (its model
translations are surjective), so it also borrows entailment (`Inst.Hom.entails_iff`). -/
theorem Translation.toHom_sound {A B : ObsSemantics I} (T : Translation (𝟭 I) A B)
    (h : ∀ X, Function.Surjective (T.sem X)) : T.toHom.Sound :=
  T.coHom_modelExpansive h

end ObsSemantics

end Silmaril.Wasm.Institution

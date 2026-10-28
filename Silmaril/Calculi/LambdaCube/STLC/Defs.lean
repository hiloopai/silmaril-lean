module

public import Silmaril.Logic.Institution.Basic
public import Silmaril.Calculi.TypedLambda.Raw
public import Silmaril.Calculi.TypedLambda.Categorical
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

set_option autoImplicit true

/-! # STLC with signature changes and set semantics

Reuse `TypedLambda.Signature`, `TypedLambda.Term`, `TypedLambda.Raw` and substitution.
Models have arbitrary small carriers, full function spaces and interpretations
of the signature's operators (in particular, nullary typed constants).
The model category is discrete; no preservation of higher-order functions by
arbitrary carrier maps is asserted.
-/

namespace Silmaril.Calculi.LambdaCube.STLC

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Calculi.TypedLambda
open Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- Rename base types, preserving arrows. -/
def mapTy (f : B → D) : Ty B → Ty D
  | .base b => .base (f b)
  | .arrow a b => .arrow (mapTy f a) (mapTy f b)

@[simp] theorem mapTy_id : mapTy (id : B → B) = id := by
  funext a
  induction a <;> simp_all [mapTy]

@[simp] theorem mapTy_comp (f : B → D) (g : D → E) :
    mapTy (g ∘ f) = mapTy g ∘ mapTy f := by
  funext a
  induction a <;> simp_all [mapTy]

/-- Signature morphisms rename base types and preserve operator types/arities. -/
structure SigMap (S T : Signature) where
  base : S.Base → T.Base
  injective : Function.Injective base
  op : ∀ {as τ}, S.Op as τ → T.Op (as.map (mapTy base)) (mapTy base τ)

theorem mapTy_injective {f : B → D} (hf : Function.Injective f) :
    Function.Injective (mapTy f) := by
  intro a b h
  induction a generalizing b with
  | base a =>
      cases b with
      | base b => exact congrArg Ty.base (hf (Ty.base.inj h))
      | arrow b c => cases h
  | arrow a c ia ic =>
      cases b with
      | base b => cases h
      | arrow b d =>
          obtain ⟨h₁, h₂⟩ := Ty.arrow.inj h
          exact congrArg₂ Ty.arrow (ia h₁) (ic h₂)

/-- Identity signature translation. -/
def SigMap.identity (S : Signature) : SigMap S S where
  base := id
  injective := Function.injective_id
  op := by
    intro as τ o
    simpa only [mapTy_id, List.map_id, id_eq] using o

/-- Composition of signature translations. -/
def SigMap.comp {S T U : Signature} (f : SigMap S T) (g : SigMap T U) : SigMap S U where
  base := g.base ∘ f.base
  injective := g.injective.comp f.injective
  op := by
    intro as τ o
    simpa only [mapTy_comp, List.map_map, Function.comp_apply] using g.op (f.op o)

/-- Base maps and the dependent operator maps determine a signature map. -/
theorem SigMap.ext {S T : Signature} {f g : SigMap S T}
    (hb : f.base = g.base) (ho : HEq (@f.op) (@g.op)) : f = g := by
  cases f
  cases g
  cases hb
  cases ho
  rfl

/-- Operator translation respects transport of its dependent indices. -/
theorem SigMap.op_heq {S T : Signature} (f : SigMap S T)
    {as bs : List (Ty S.Base)} {τ υ : Ty S.Base}
    (ha : as = bs) (ht : τ = υ) {o : S.Op as τ} {p : S.Op bs υ}
    (ho : HEq o p) : HEq (f.op o) (f.op p) := by
  subst bs
  subst υ
  cases ho
  rfl

instance : Category Signature where
  Hom := SigMap
  id := SigMap.identity
  comp := SigMap.comp
  id_comp := by
    intro S T f
    refine SigMap.ext (f := _) (g := _) ?_ ?_
    · rfl
    · simp [SigMap.comp, SigMap.identity]
      funext as τ o
      apply eq_of_heq
      exact (cast_heq _ _).trans (f.op_heq (by simp) (by simp) (cast_heq _ _))
  comp_id := by
    intro S T f
    refine SigMap.ext (f := _) (g := _) ?_ ?_
    · rfl
    · simp [SigMap.comp, SigMap.identity]
  assoc := by
    intro S T U V f g h
    refine SigMap.ext (f := _) (g := _) ?_ ?_
    · rfl
    · simp [SigMap.comp, Function.comp_def]
      funext as τ o
      apply eq_of_heq
      exact (cast_heq _ _).trans
        ((h.op_heq
          (as := as.map (mapTy (g.base ∘ f.base)))
          (bs := (as.map (mapTy f.base)).map (mapTy g.base))
          (τ := mapTy (g.base ∘ f.base) τ)
          (υ := mapTy g.base (mapTy f.base τ))
          (p := g.op (f.op o))
          (by simp [List.map_map]) (by simp) (cast_heq _ _)).trans (cast_heq _ _).symm)

/-- Reindex a tuple along a map of its list of sorts. -/
def reindexTuple {α β : Type} {X : β → Type} (f : α → β) :
    {as : List α} → (∀ a, Var as a → X (f a)) → Tuple X (as.map f)
  | [], _ => Tuple.nil
  | _ :: _, args => Tuple.cons (args _ .zero)
      (reindexTuple f (fun _ x => args _ (.succ x)))

theorem reindexTuple_apply {α β : Type} {X : β → Type} (f : α → β)
    {as : List α} (args : ∀ a, Var as a → X (f a)) {a : α} (x : Var as a) :
    reindexTuple f args _ (x.map f) = args _ x := by
  induction x with
  | zero => rfl
  | succ x ih => exact ih (fun _ y => args _ (.succ y))

theorem reindexTuple_natural {α β : Type} {X Y : β → Type} (f : α → β)
    (g : ∀ b, X b → Y b) {as : List α} (args : ∀ a, Var as a → X (f a)) :
    Tuple.map g (reindexTuple f args) =
      reindexTuple f (fun a x => g (f a) (args a x)) := by
  induction as with
  | nil => exact Tuple.ext fun _ x => nomatch x
  | cons a as ih =>
      apply Tuple.ext
      intro b x
      cases x with
      | zero => rfl
      | succ x => exact congrFun (congrFun (ih (fun _ y => args _ (.succ y))) _) x

/-- Intrinsic signature translation, including changes of base types. -/
def mapTerm {S T : Signature} (f : SigMap S T) :
    {Γ : Ctx S.Base} → {τ : Ty S.Base} → Term S Γ τ →
      Term T (Γ.map (mapTy f.base)) (mapTy f.base τ)
  | _, _, .var x => .var (x.map (mapTy f.base))
  | _, _, .lam t => .lam (mapTerm f t)
  | _, _, .app t u => .app (mapTerm f t) (mapTerm f u)
  | _, _, .op o args => .op (f.op o)
      (reindexTuple (mapTy f.base) (fun _ x => mapTerm f (args _ x)))

/-- Set interpretation of simple types; arrows are full function sets. -/
def carrier (base : B → Type) : Ty B → Type
  | .base b => base b
  | .arrow a b => carrier base a → carrier base b

/-- A set-theoretic model with no nonemptiness assumption. -/
structure SetModel (S : Signature) where
  base : S.Base → Type
  op : ∀ {as τ}, S.Op as τ → Tuple (carrier base) as → carrier base τ

/-- Structural evaluation using the existing intrinsic syntax. -/
def eval {S : Signature} (M : SetModel S) : {Γ : Ctx S.Base} → {τ : Ty S.Base} →
    Term S Γ τ → Tuple (carrier M.base) Γ → carrier M.base τ
  | _, _, .var x, ρ => ρ _ x
  | _, _, .lam t, ρ => fun d => eval M t (Tuple.cons d ρ)
  | _, _, .app f a, ρ => eval M f ρ (eval M a ρ)
  | _, _, .op o args, ρ => M.op o (fun _ x => eval M (args _ x) ρ)

/-- The canonical equivalence used to transport values under a base renaming. -/
def carrierMap (f : B → D) (base : D → Type) : (a : Ty B) →
    carrier (base ∘ f) a ≃ carrier base (mapTy f a)
  | .base _ => Equiv.refl _
  | .arrow a b => Equiv.arrowCongr (carrierMap f base a) (carrierMap f base b)

/-- Transport a tuple of values to a renamed context. -/
def envMap (f : B → D) (base : D → Type) : {Γ : List (Ty B)} →
    Tuple (carrier (base ∘ f)) Γ → Tuple (carrier base) (Γ.map (mapTy f))
  | [], _ => Tuple.nil
  | _ :: _, ρ => Tuple.cons (carrierMap f base _ (ρ _ .zero))
      (envMap f base (fun _ x => ρ _ (.succ x)))

theorem envMap_eq_reindex (f : B → D) (base : D → Type) {Γ : List (Ty B)}
    (ρ : Tuple (carrier (base ∘ f)) Γ) :
    envMap f base ρ = reindexTuple (mapTy f) (fun a x => carrierMap f base a (ρ a x)) := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih =>
      apply Tuple.ext
      intro b x
      cases x with
      | zero => rfl
      | succ x => exact congrFun (congrFun (ih (fun _ y => ρ _ (.succ y))) _) x

/-- Models move backwards by restricting base carriers and operators. -/
def reduct {S T : Signature} (f : SigMap S T) (M : SetModel T) : SetModel S where
  base := M.base ∘ f.base
  op o args := (carrierMap f.base M.base _).symm (M.op (f.op o) (envMap f.base M.base args))

/-- Evaluation commutes with signature translation. -/
theorem eval_map {S T : Signature} (f : SigMap S T) (M : SetModel T)
    {Γ τ} (t : Term S Γ τ) (ρ : Tuple (carrier (M.base ∘ f.base)) Γ) :
    eval M (mapTerm f t) (envMap f.base M.base ρ) =
      carrierMap f.base M.base τ (eval (reduct f M) t ρ) := by
  induction t with
  | var x =>
      simp only [mapTerm, eval, envMap_eq_reindex, reindexTuple_apply]
  | lam t ih =>
      funext d
      change eval M (mapTerm f t) (Tuple.cons d (envMap f.base M.base ρ)) =
        carrierMap f.base M.base _ (eval (reduct f M) t
          (Tuple.cons ((carrierMap f.base M.base _).symm d) ρ))
      have h := ih (Tuple.cons ((carrierMap f.base M.base _).symm d) ρ)
      simp only [envMap, Tuple.cons_zero, Tuple.cons_succ, Equiv.apply_symm_apply] at h
      convert h using 1; rfl
  | app t u iht ihu =>
      simp only [mapTerm, eval]
      erw [iht, ihu]
      change carrierMap f.base M.base _ (eval (reduct f M) t ρ
        ((carrierMap f.base M.base _).symm (carrierMap f.base M.base _ (eval (reduct f M) u ρ)))) = _
      exact congrArg (carrierMap f.base M.base _) (congrArg (eval (reduct f M) t ρ)
        ((carrierMap f.base M.base _).symm_apply_apply _))
  | op o args ih =>
      simp only [mapTerm, eval, reduct, Equiv.apply_symm_apply]
      apply congrArg (M.op (f.op o))
      change Tuple.map (fun a (v : Term T _ a) => eval M v (envMap f.base M.base ρ))
        (reindexTuple (mapTy f.base) (fun _ x => mapTerm f (args _ x))) = _
      rw [reindexTuple_natural]
      simp only [envMap_eq_reindex]
      apply congrArg (reindexTuple (mapTy f.base))
      funext a x
      have h := ih a x ρ
      simp only [envMap_eq_reindex] at h
      convert h using 1; rfl

/-- Sentences include raw typing assertions and equations in explicit contexts.
Ill-typed raw assertions are allowed and interpreted as false. -/
inductive Sentence (S : Signature) where
  | typing (Γ : Ctx S.Base) (t : Raw S) (τ : Ty S.Base)
  | equation {Γ : Ctx S.Base} {τ : Ty S.Base} (t u : Term S Γ τ)

/-- Rename raw syntax, using the existing intrinsically typed operators. -/
def mapRaw {S T : Signature} (f : SigMap S T) : Raw S → Raw T
  | .var n => .var n
  | .lam a t => .lam (mapTy f.base a) (mapRaw f t)
  | .app t u => .app (mapRaw f t) (mapRaw f u)
  | .op o args => .op (f.op o) (fun i => mapRaw f (args ⟨i.val, by simpa using i.isLt⟩))

/-- Sentence translation. -/
def mapSentence {S T : Signature} (f : SigMap S T) : Sentence S → Sentence T
  | .typing Γ t τ => .typing (Γ.map (mapTy f.base)) (mapRaw f t) (mapTy f.base τ)
  | .equation t u => .equation (mapTerm f t) (mapTerm f u)

/-- Satisfaction: typability, or equality at every environment. -/
def Sat {S : Signature} (M : SetModel S) : Sentence S → Prop
  | .typing Γ t τ => Raw.HasType Γ t τ
  | .equation t u => ∀ ρ, eval M t ρ = eval M u ρ

/-- Institution sentences include raw typing judgments, including failed ones. -/
abbrev Judgment := Sentence

abbrev translate := @mapSentence
abbrev Holds := @Sat

/-- Injectivity of base renaming is essential to reflection of raw typing. -/
theorem typing_map_iff {S T : Signature} (f : SigMap S T) (Γ : Ctx S.Base)
    (t : Raw S) (τ : Ty S.Base) :
    Raw.HasType (Γ.map (mapTy f.base)) (mapRaw f t) (mapTy f.base τ) ↔
      Raw.HasType Γ t τ := by
  classical
  have hinj := mapTy_injective f.injective
  have hc : ∀ (Γ : Ctx S.Base) (t : Raw S),
      Raw.infer (Γ.map (mapTy f.base)) (mapRaw f t) =
        (Raw.infer Γ t).map (mapTy f.base) := by
    intro Γ t
    induction t generalizing Γ with
    | var n => simp [mapRaw, Raw.infer]
    | lam a t ih =>
        change Option.map (Ty.arrow (mapTy f.base a))
          (Raw.infer ((a :: Γ).map (mapTy f.base)) (mapRaw f t)) = _
        rw [ih]
        simp only [Raw.infer, Option.map_map, mapTy, Function.comp_def]
    | app t u iht ihu =>
        cases ht : Raw.infer Γ t with
        | none => simp [mapRaw, Raw.infer, iht, ht]
        | some a =>
            cases a with
            | base b => simp [mapRaw, Raw.infer, iht, ht, mapTy]
            | arrow a b =>
                cases hu : Raw.infer Γ u with
                | none => simp [mapRaw, Raw.infer, iht, ihu, ht, hu, mapTy]
                | some c =>
                    by_cases he : a = c
                    · subst c
                      simp [mapRaw, Raw.infer, iht, ihu, ht, hu, mapTy]
                    · have hne : mapTy f.base a ≠ mapTy f.base c := fun h => he (hinj h)
                      simp [mapRaw, Raw.infer, iht, ihu, ht, hu, mapTy, he, hne]
    | @op as τ o args ih =>
        have hp : (∀ i : Fin (as.map (mapTy f.base)).length,
            Raw.infer (Γ.map (mapTy f.base)) (mapRaw f (args ⟨i.val, by simpa using i.isLt⟩)) =
              some ((as.map (mapTy f.base)).get i)) ↔
            (∀ i : Fin as.length, Raw.infer Γ (args i) = some (as.get i)) := by
          simp only [ih, List.get_eq_getElem, List.getElem_map, Option.map_eq_some_iff]
          constructor
          · intro h i
            obtain ⟨a, ha, he⟩ := h ⟨i.val, by simp only [List.length_map]; exact i.isLt⟩
            exact ha.trans (congrArg some (hinj he))
          · intro h i
            exact ⟨_, h ⟨i.val, by simpa using i.isLt⟩, rfl⟩
        simp only [mapRaw, Raw.infer]
        simp only [hp]
        split_ifs <;> rfl

  rw [← Raw.infer_eq_some, hc, ← Raw.infer_eq_some]
  simp [Option.map_eq_some_iff, hinj.eq_iff]

/-- Transport values back from a renamed context. -/
def envUnmap (f : B → D) (base : D → Type) : {Γ : List (Ty B)} →
    Tuple (carrier base) (Γ.map (mapTy f)) → Tuple (carrier (base ∘ f)) Γ
  | [], _ => Tuple.nil
  | _ :: _, ρ => Tuple.cons ((carrierMap f base _).symm (ρ _ .zero))
      (envUnmap f base (fun _ x => ρ _ (.succ x)))

/-- Every target environment has a source environment. -/
theorem envMap_surjective (f : B → D) (base : D → Type) (Γ : List (Ty B)) :
    Function.Surjective (envMap f base (Γ := Γ)) := by
  intro ρ
  refine ⟨envUnmap f base ρ, ?_⟩
  induction Γ with
  | nil => exact (Tuple.eq_nil _).trans (Tuple.eq_nil ρ).symm
  | cons a Γ ih =>
      apply Tuple.ext
      intro b x
      cases x with
      | zero => exact (carrierMap f base a).apply_symm_apply _
      | succ x => exact congrFun (congrFun (ih (fun _ x => ρ _ (.succ x))) _) x

/-- The satisfaction condition, with both directions of equation transport. -/
theorem satisfaction {S T : Signature} (f : SigMap S T) (M : SetModel T) (j : Judgment S) :
    Holds M (translate f j) ↔ Holds (reduct f M) j := by
  cases j with
  | typing Γ t τ => exact typing_map_iff f Γ t τ
  | equation t u =>
    constructor
    · intro h ρ
      apply (carrierMap f.base M.base _).injective
      exact (eval_map f M t ρ).symm.trans ((h _).trans (eval_map f M u ρ))
    · intro h η
      obtain ⟨ρ, rfl⟩ := envMap_surjective f.base M.base _ η
      rw [eval_map, eval_map, h ρ]

/-- The model category is discrete, including all small set models. -/
def room (S : Signature) : Room.{0, 1, 1} :=
  ⟨Judgment S, Cat.of (Discrete (SetModel S)), fun M => Holds M.as⟩

/-- Reducts as functors on discrete model categories. -/
def reductFunctor {S T : Signature} (f : SigMap S T) :
    Discrete (SetModel T) ⥤ Discrete (SetModel S) :=
  Discrete.functor (fun M => Discrete.mk (reduct f M))

/-- A signature change as a corridor. -/
def corridor {S T : Signature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨translate f, reductFunctor f, fun M j => satisfaction f M.as j⟩

/-! ### Non-vacuity of satisfaction -/

/-- One base type and no operators. -/
def unitSig : Signature := ⟨Unit, fun _ _ => Empty⟩

/-- The set model with Booleans at the base type. -/
def boolModel : SetModel unitSig := ⟨fun _ => Bool, fun o _ => (o : Empty).elim⟩

/-- The set model with one point at the base type. -/
def unitModel : SetModel unitSig := ⟨fun _ => Unit, fun o _ => (o : Empty).elim⟩

/-- `x = y` for two distinct variables of the base type. -/
def varEq : Sentence unitSig :=
  .equation (Γ := [.base (), .base ()]) (τ := .base ()) (.var .zero) (.var (.succ .zero))

/-- Reflexive equations hold in every model, in particular the Boolean one. -/
theorem boolModel_sat_refl :
    Holds boolModel (.equation (Γ := [.base ()]) (τ := .base ()) (.var .zero) (.var .zero)) :=
  fun _ => rfl

/-- The Boolean model does not satisfy `x = y`. -/
theorem boolModel_not_sat_var_eq : ¬ Holds boolModel varEq := by
  intro h
  exact Bool.noConfusion
    (h (Tuple.cons (true : Bool) (Tuple.cons (false : Bool) Tuple.nil)) : true = false)

/-- The one-point model satisfies `x = y`, so satisfaction depends on the model. -/
theorem unitModel_sat_var_eq : Holds unitModel varEq :=
  fun _ => Subsingleton.elim (α := Unit) _ _

/-- Identity reindexing preserves each typed variable, up to its context transport. -/
theorem var_map_id {as : List (Ty B)} {a : Ty B} (x : Var as a) : HEq (x.map id) x := by
  induction x with
  | zero => simp only [Var.map]; congr 1; simp
  | succ x ih => simp only [Var.map]; congr 1; simp_all

/-- Identity reindexing preserves tuples whose entries agree heterogeneously. -/
theorem reindexTuple_heq_id {α : Type} {X Y : α → Type} (hX : X = Y)
    {f : α → α} (hf : f = id) {as : List α}
    (args : ∀ a, Var as a → X (f a)) (ys : Tuple Y as)
    (h : ∀ a x, HEq (args a x) (ys a x)) : HEq (reindexTuple f args) ys := by
  subst f
  subst Y
  induction as with
  | nil => exact heq_of_eq ((Tuple.eq_nil _).trans (Tuple.eq_nil ys).symm)
  | cons a as ih =>
      have hc : HEq (reindexTuple id args)
          (Tuple.cons (ys _ .zero) (fun _ x => ys _ (.succ x))) := by
        simp only [reindexTuple]
        congr 1
        · simp
        · exact eq_of_heq (h _ .zero)
        · exact ih _ _ (fun _ x => h _ (.succ x))
      exact hc.trans (heq_of_eq (Tuple.cons_head_tail ys))

/-- Identity signature translation preserves intrinsic terms. -/
theorem mapTerm_identity {S : Signature} {Γ τ} (t : Term S Γ τ) :
    HEq (mapTerm (SigMap.identity S) t) t := by
  induction t with
  | var x =>
      simp [mapTerm, SigMap.identity]
      congr 1 <;> try simp
      erw [mapTy_id]
      exact var_map_id x
  | lam t ih => simp [mapTerm, SigMap.identity]; congr 1 <;> simp
  | app t u iht ihu => simp [mapTerm, SigMap.identity]; congr 1 <;> simp
  | op o args ih =>
      simp [mapTerm, SigMap.identity]
      congr 1 <;> try simp
      exact reindexTuple_heq_id (by simp) mapTy_id _ args ih

/-- Arrow transport along identity equivalences is the identity. -/
theorem arrowCongr_heq {A A' B B' : Type} (ha : A' = A) (hb : B' = B)
    (ea : A ≃ A') (eb : B ≃ B') (he : HEq ea (Equiv.refl A))
    (hf : HEq eb (Equiv.refl B)) :
    HEq (Equiv.arrowCongr ea eb) (Equiv.refl (A → B)) := by
  subst A'
  subst B'
  cases he
  cases hf
  rfl

/-- The carrier equivalence for the identity base map is the identity. -/
theorem carrierMap_identity (base : B → Type) (a : Ty B) :
    HEq (carrierMap id base a) (Equiv.refl (carrier base a)) := by
  induction a with
  | base b => rfl
  | arrow a b ia ib =>
      exact arrowCongr_heq
        (congrArg (carrier base) (congrFun mapTy_id a))
        (congrArg (carrier base) (congrFun mapTy_id b)) _ _ ia ib

/-- An identity equivalence preserves values across its codomain transport. -/
theorem equiv_apply_heq_refl {A B : Type} (hb : B = A) (e : A ≃ B)
    (he : HEq e (Equiv.refl A)) (a : A) : HEq (e a) a := by
  subst B
  cases he
  rfl

/-- The inverse of an identity equivalence preserves transported values. -/
theorem equiv_symm_apply_heq_refl {A B : Type} (hb : B = A) (e : A ≃ B)
    (he : HEq e (Equiv.refl A)) {a : B} {b : A} (hab : HEq a b) : HEq (e.symm a) b := by
  subst B
  cases he
  cases hab
  rfl

/-- Identity environment transport preserves every value. -/
theorem envMap_identity {B : Type} (base : B → Type) {Γ : List (Ty B)}
    (ρ : Tuple (carrier base) Γ) : HEq (envMap id base ρ) ρ := by
  erw [envMap_eq_reindex]
  exact reindexTuple_heq_id rfl mapTy_id _ ρ (fun a x =>
    equiv_apply_heq_refl (by simp) _ (carrierMap_identity base a) (ρ a x))

/-- Base carriers and dependent operator interpretations determine a set model. -/
theorem SetModel.ext {S : Signature} {M N : SetModel S}
    (hb : M.base = N.base) (ho : HEq (@M.op) (@N.op)) : M = N := by
  cases M
  cases N
  cases hb
  cases ho
  rfl

/-- Operator interpretation respects transport of arities, types, and arguments. -/
theorem SetModel.op_heq {S : Signature} (M : SetModel S)
    {as bs : List (Ty S.Base)} {τ υ : Ty S.Base} (ha : as = bs) (ht : τ = υ)
    {o : S.Op as τ} {p : S.Op bs υ} (ho : HEq o p)
    {args : Tuple (carrier M.base) as} {ys : Tuple (carrier M.base) bs}
    (hargs : HEq args ys) : HEq (M.op o args) (M.op p ys) := by
  subst bs
  subst υ
  cases ho
  cases hargs
  rfl

/-- Restricting a set model along the identity signature map preserves it. -/
theorem reduct_identity {S : Signature} (M : SetModel S) : reduct (SigMap.identity S) M = M := by
  refine SetModel.ext rfl ?_
  apply heq_of_eq
  funext as τ o args
  change (carrierMap id M.base τ).symm
    (M.op ((SigMap.identity S).op o) (envMap id M.base args)) = M.op o args
  apply eq_of_heq
  apply equiv_symm_apply_heq_refl (by simp) _ (carrierMap_identity M.base τ)
  exact M.op_heq (as := as.map (mapTy id)) (bs := as)
    (τ := mapTy id τ) (υ := τ) (o := (SigMap.identity S).op o) (p := o)
    (by simp) (by simp) (by simp [SigMap.identity]) (envMap_identity M.base args)

/-- Functions on propositionally equal finite index types agree pointwise. -/
theorem fin_fun_heq {A : Type} {m n : Nat} (h : m = n)
    (f : Fin m → A) (g : Fin n → A)
    (he : ∀ i, f i = g (Fin.cast h i)) : HEq f g := by
  subst n
  exact heq_of_eq (funext he)

/-- Identity signature translation preserves raw terms. -/
theorem mapRaw_identity {S : Signature} (t : Raw S) : mapRaw (SigMap.identity S) t = t := by
  induction t with
  | var n => rfl
  | lam a t ih => simpa [mapRaw, SigMap.identity] using congrArg (Raw.lam a) ih
  | app t u iht ihu => simp only [mapRaw, iht, ihu]
  | @op as τ o args ih =>
      simp [mapRaw, SigMap.identity]
      apply fin_fun_heq (m := (as.map (mapTy id)).length) (n := as.length) (by simp)
      intro i
      exact ih ⟨i.val, by simpa using i.isLt⟩

/-- Identity signature translation preserves both kinds of sentences. -/
theorem mapSentence_identity {S : Signature} (j : Sentence S) : mapSentence (SigMap.identity S) j = j := by
  cases j with
  | typing Γ t τ =>
      simp only [mapSentence]
      congr 1 <;> try simp [SigMap.identity]
      exact mapRaw_identity t
  | equation t u =>
      simp only [mapSentence]
      congr 1 <;> try simp [SigMap.identity]
      all_goals exact mapTerm_identity _

/-- Composition acts by ordinary composition on base types. -/
@[simp] theorem SigMap.comp_base {S T U : Signature} (f : SigMap S T) (g : SigMap T U) :
    (f.comp g).base = g.base ∘ f.base := rfl

/-- The composite operator map agrees with successive translation up to transport. -/
@[simp] theorem SigMap.comp_op {S T U : Signature} (f : SigMap S T) (g : SigMap T U)
    {as τ} (o : S.Op as τ) : HEq ((f.comp g).op o) (g.op (f.op o)) := by
  simp [SigMap.comp]

/-- Reindexing variables respects composition. -/
theorem var_map_comp (f : A → B) (g : B → D) {as : List A} {a : A}
    (x : Var as a) : HEq (x.map (g ∘ f)) ((x.map f).map g) := by
  induction x with
  | zero => simp only [Var.map]; congr 1; simp [List.map_map]
  | succ x ih => simp only [Var.map]; congr 1; simp_all [List.map_map]

/-- Reindexing a tuple twice is reindexing along the composite. -/
theorem reindexTuple_comp {A B D : Type} {X : D → Type}
    (f : A → B) (g : B → D) {as : List A}
    (args : ∀ a, Var as a → X (g (f a))) :
    HEq (reindexTuple (g ∘ f) args)
      (reindexTuple g (fun _ x => reindexTuple (X := fun b => X (g b)) f args _ x)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [reindexTuple]
      congr 1 <;> simp_all [List.map_map]

/-- Reindexed tuples agree when the reindexing and entries agree. -/
theorem reindexTuple_congr {A B : Type} {X Y : B → Type}
    (hX : X = Y) {f g : A → B} (hf : f = g) {as : List A}
    (args : ∀ a, Var as a → X (f a)) (ys : ∀ a, Var as a → Y (g a))
    (h : ∀ a x, HEq (args a x) (ys a x)) :
    HEq (reindexTuple f args) (reindexTuple g ys) := by
  subst Y
  subst g
  have he : args = ys := by funext a x; exact eq_of_heq (h a x)
  cases he
  rfl

/-- Intrinsic signature translation respects composition. -/
theorem mapTerm_comp {S T U : Signature} (f : SigMap S T) (g : SigMap T U)
    {Γ τ} (t : Term S Γ τ) :
    HEq (mapTerm (f.comp g) t) (mapTerm g (mapTerm f t)) := by
  induction t with
  | var x =>
      simp only [mapTerm]
      congr 1 <;> try simp [List.map_map]
      exact (by rw [mapTy_comp]; exact var_map_comp _ _ x)
  | lam t ih => simp only [mapTerm]; congr 1 <;> simp_all [List.map_map]
  | app t u iht ihu => simp only [mapTerm]; congr 1 <;> simp_all [List.map_map]
  | op o args ih =>
      simp only [mapTerm]
      congr 1 <;> try simp [List.map_map]
      · exact SigMap.comp_op f g o
      · change HEq
          (reindexTuple (mapTy (f.comp g).base) (fun _ x => mapTerm (f.comp g) (args _ x)))
          (reindexTuple (mapTy g.base) (Tuple.map (fun a (v : Term T _ a) => mapTerm g v)
            (reindexTuple (mapTy f.base) (fun _ x => mapTerm f (args _ x)))))
        rw [reindexTuple_natural]
        exact (reindexTuple_congr (by simp [List.map_map])
          (by simp only [SigMap.comp_base, mapTy_comp]; rfl) _ _ ih).trans
          (reindexTuple_comp _ _ _)

/-- Raw signature translation respects composition. -/
theorem mapRaw_comp {S T U : Signature} (f : SigMap S T) (g : SigMap T U)
    (t : Raw S) : mapRaw (f.comp g) t = mapRaw g (mapRaw f t) := by
  induction t with
  | var n => rfl
  | lam a t ih => simp only [mapRaw, SigMap.comp_base, mapTy_comp, Function.comp_apply, ih]
  | app t u iht ihu => simp only [mapRaw, iht, ihu]
  | @op as τ o args ih =>
      simp only [mapRaw]
      congr 1 <;> try simp [List.map_map]
      · exact SigMap.comp_op f g o
      · apply fin_fun_heq (by simp)
        intro i
        exact ih _

/-- Sentence translation respects composition. -/
theorem mapSentence_comp {S T U : Signature} (f : SigMap S T) (g : SigMap T U)
    (j : Sentence S) : mapSentence (f.comp g) j = mapSentence g (mapSentence f j) := by
  cases j with
  | typing Γ t τ =>
      simp only [mapSentence]
      congr 1 <;> try simp [List.map_map]
      exact mapRaw_comp f g t
  | equation t u =>
      simp only [mapSentence]
      congr 1 <;> try simp [List.map_map]
      all_goals exact mapTerm_comp f g _

/-- Composition of arrow equivalences respects transport of codomain types. -/
theorem arrowCongr_trans_heq {A B C C' D E F F' : Type}
    (hc : C = C') (hf : F = F')
    (a : A ≃ C) (a₁ : A ≃ B) (a₂ : B ≃ C')
    (b : D ≃ F) (b₁ : D ≃ E) (b₂ : E ≃ F')
    (ha : HEq a (a₁.trans a₂)) (hb : HEq b (b₁.trans b₂)) :
    HEq (Equiv.arrowCongr a b)
      ((Equiv.arrowCongr a₁ b₁).trans (Equiv.arrowCongr a₂ b₂)) := by
  subst C'
  subst F'
  cases ha
  cases hb
  rfl

/-- Carrier equivalences compose, including their dependent codomain transport. -/
theorem carrierMap_comp (f : A → B) (g : B → D) (base : D → Type) (a : Ty A) :
    HEq (carrierMap (g ∘ f) base a)
      ((carrierMap f (base ∘ g) a).trans (carrierMap g base (mapTy f a))) := by
  induction a with
  | base a => rfl
  | arrow a b ia ib =>
      exact arrowCongr_trans_heq (by simp) (by simp) _ _ _ _ _ _ ia ib

/-- Apply heterogeneously equal equivalences to equal values. -/
theorem equiv_apply_heq {A B C : Type} (hb : B = C) (e : A ≃ B) (d : A ≃ C)
    (he : HEq e d) (a : A) : HEq (e a) (d a) := by
  subst C
  cases he
  rfl

/-- Environment transport respects composition. -/
theorem envMap_comp (f : A → B) (g : B → D) (base : D → Type)
    {Γ : List (Ty A)} (ρ : Tuple (carrier (base ∘ (g ∘ f))) Γ) :
    HEq (envMap (g ∘ f) base ρ) (envMap g base (envMap f (base ∘ g) ρ)) := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih =>
      simp only [envMap]
      congr 1 <;> try simp [List.map_map]
      · exact equiv_apply_heq (by simp) _ _ (carrierMap_comp f g base a) _
      · exact ih _

/-- Inverses of composable equivalences respect heterogeneous value equality. -/
theorem equiv_symm_trans_heq {A B C D : Type} (hc : C = D)
    (e : A ≃ C) (f : A ≃ B) (g : B ≃ D) (he : HEq e (f.trans g))
    {x : C} {y : D} (hxy : HEq x y) : HEq (e.symm x) (f.symm (g.symm y)) := by
  subst D
  cases he
  cases hxy
  rfl

/-- Restriction along a composite is successive restriction. -/
theorem reduct_comp {S T U : Signature} (f : SigMap S T) (g : SigMap T U)
    (M : SetModel U) : reduct (f.comp g) M = reduct f (reduct g M) := by
  refine SetModel.ext rfl ?_
  apply heq_of_eq
  funext as τ o args
  change (carrierMap (g.base ∘ f.base) M.base τ).symm
    (M.op ((f.comp g).op o) (envMap (g.base ∘ f.base) M.base args)) =
    (carrierMap f.base (M.base ∘ g.base) τ).symm
      ((carrierMap g.base M.base (mapTy f.base τ)).symm
        (M.op (g.op (f.op o)) (envMap g.base M.base (envMap f.base (M.base ∘ g.base) args))))
  apply eq_of_heq
  apply equiv_symm_trans_heq (by simp) _ _ _ (carrierMap_comp _ _ _ _)
  exact M.op_heq (by simp [List.map_map]) (by simp)
    (SigMap.comp_op f g o) (envMap_comp _ _ _ _)

/-- The STLC institution, with strict identity and composition laws. -/
def institution : Signature ⥤ Room.{0, 1, 1} where
  obj := room
  map := corridor
  map_id := by
    intro S
    apply Room.hom_ext
    · change mapSentence (SigMap.identity S) = id
      exact funext mapSentence_identity
    · change reductFunctor (SigMap.identity S) = 𝟭 (Discrete (SetModel S))
      apply Discrete.functor_ext
      intro M
      exact congrArg Discrete.mk (reduct_identity M)
  map_comp := by
    intro S T U f g
    apply Room.hom_ext
    · change mapSentence (f.comp g) = mapSentence g ∘ mapSentence f
      exact funext (mapSentence_comp f g)
    · change reductFunctor (f.comp g) = reductFunctor g ⋙ reductFunctor f
      apply Discrete.functor_ext
      intro M
      exact congrArg Discrete.mk (reduct_comp f g M)

/-- βη equational derivations, using existing substitution and weakening. -/
inductive Equates {S : Signature} : {Γ : Ctx S.Base} → {τ : Ty S.Base} →
    Term S Γ τ → Term S Γ τ → Prop where
  | refl (t) : Equates t t
  | symm : Equates t u → Equates u t
  | trans : Equates t u → Equates u v → Equates t v
  | beta (t : Term S (σ :: Γ) τ) (u : Term S Γ σ) :
      Equates (.app (.lam t) u) (t.subst1 u)
  | eta (t : Term S Γ (.arrow σ τ)) :
      Equates (.lam (.app t.weaken (.var .zero))) t
  | context (C : Context S Δ σ Γ τ) : Equates t u → Equates (C.plug t) (C.plug u)

end Silmaril.Calculi.LambdaCube.STLC

module

public import Silmaril.Calculi.TypedLambda.Finite
public import Silmaril.Calculi.PCF.Adequacy

/-! # The boolean fragment PCF_bool

§8.2 of the notes ("Undecidability of contextual equivalence", pp. 68–69).
PCF_bool is the fragment of PCF involving only `bool` and the function types
formed from it, `true`, `false`, conditionals, variables, abstraction,
application, and a primitive divergent term `Ω_bool : bool`.

## Two presentations

The fragment is built in two steps.

* `boolSig` is a signature over the base types of PCF whose operators
  `BoolOp` are `true`, `false`, `if` at PCF_bool types (`Ty.IsBool`) and
  `Ω_bool`. Its inclusion into PCF is a derived-operator translation
  (`TypedLambda.Term.translate`, see `Silmaril.Calculi.TypedLambda.Morphism`): `Ω_bool` becomes
  PCF's `Ω_bool = fix(fun x:bool. x)` and the other operators become
  themselves. The fragment is observed through PCF: a program `t : bool`
  evaluates to `v` when its inclusion does (`boolObs`), and its model
  `boolModel` interprets each operator by the denotation of its translation, so
  the inclusion preserves denotations (`denote_toPCF`). Soundness and adequacy
  transfer along the inclusion (`boolObs_soundAdequate`). Since abstraction is
  generic in `Silmaril.Calculi.TypedLambda.Term`, the terms `BoolTerm` of this signature may
  still bind variables of types mentioning `nat`, and so may its contexts: it
  is a superset of the notes' fragment.
* `pcfBoolSig` is the notes' fragment exactly: its only base type is `Unit`,
  standing for `bool`, so its types (`BoolTy`) are exactly the PCF_bool types
  (`BoolTy.toTy`, `Ty.isBool_iff`), and so are the types of all variables of
  its terms (`PCFBoolTerm`) and of its contexts. `Silmaril.Calculi.TypedLambda.Morphism`
  only translates between signatures with the same base types, so the
  inclusion `PCFBoolTerm.embed` into `boolSig` is defined directly. It
  preserves denotations up to the logical relation `PCFBool.Corr` between the
  two models, which is equality at `bool` (`denoteClosed_embed`). The
  observation `pcfBoolObs` evaluates the inclusion in PCF, and soundness and
  adequacy transfer again (`pcfBoolObs_soundAdequate`), giving Theorem 24 for
  the notes' contextual equivalence of PCF_bool
  (`pcfBool_ctxEquiv_of_denote_eq`).

## Finiteness

The notes' finiteness remarks are then:

* `⟦τ⟧` is finite for every PCF_bool type `τ` (`finite_ty_of_isBool`, and an
  instance under `Fact (Ty.IsBool τ)`; for the exact fragment, the instance
  `pcfBool_finite_ty` at every type): `𝔹⊥` is finite and function domains
  between finite domains are finite (`Silmaril.Calculi.TypedLambda.Ty.finite_denote`).
* On these domains every monotone map is continuous
  (`ωScottContinuous_of_monotone_of_isBool`), so `⟦σ -> τ⟧` is the finite
  poset of monotone "truth tables" (`arrowOrderIsoOfIsBool`).
* There are finitely many PCF_bool terms up to contextual equivalence at each
  type, in each context (`pcfBool_finite_ctxQuot`), and at most as many as
  there are elements of `⟦Γ⟧ →𝒄 ⟦τ⟧` (`pcfBool_card_ctxQuot_le`). This is
  `Silmaril.Calculi.TypedLambda.Observation.SoundAdequate.finite_ctxQuot` for the fragment.
  The same holds for the larger `boolSig`, at PCF_bool types and contexts
  (`finite_boolCtxQuot`, `card_boolCtxQuot_le`).

Loader's theorem, that definability of elements of `⟦τ⟧` by PCF_bool terms and
contextual equivalence of PCF_bool terms are undecidable (uniformly in `τ`),
is cited background and is not formalized.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

/-! ### PCF_bool types -/

/-- The PCF_bool types: `bool` and the function types formed from it. -/
abbrev Ty.IsBool (τ : Ty) : Prop := TypedLambda.Ty.AllBase (· = Base.bool) τ

/-- `bool` is a PCF_bool type. -/
theorem Ty.isBool_bool : Ty.IsBool Ty.bool := rfl

/-- `nat` is not a PCF_bool type. -/
theorem Ty.not_isBool_nat : ¬ Ty.IsBool Ty.nat := nofun

/-- A function type is a PCF_bool type iff its domain and codomain are. -/
theorem Ty.isBool_arrow {σ τ : Ty} : Ty.IsBool (σ ⤳ τ) ↔ Ty.IsBool σ ∧ Ty.IsBool τ :=
  Iff.rfl

instance Ty.fact_isBool_bool : Fact (Ty.IsBool Ty.bool) := ⟨rfl⟩

instance Ty.fact_isBool_arrow {σ τ : Ty} [Fact (Ty.IsBool σ)] [Fact (Ty.IsBool τ)] :
    Fact (Ty.IsBool (σ ⤳ τ)) :=
  ⟨⟨Fact.out, Fact.out⟩⟩

variable {p : Bool}

/-! ### Finiteness of the PCF_bool domains -/

/-- The base domain of the PCF_bool types, `𝔹⊥`, is finite. -/
theorem finite_base_of_isBool : ∀ b : Base, b = Base.bool → Finite (baseDom b)
  | _, rfl => Flat.finite (X := Bool)

/-- `⟦τ⟧` is finite for every PCF_bool type `τ`. -/
theorem finite_ty_of_isBool {τ : Ty} (hτ : Ty.IsBool τ) : Finite ((model p).ty τ) :=
  (model p).finite_ty finite_base_of_isBool hτ

/-- `⟦τ⟧` is finite for every PCF_bool type `τ`, as an instance. -/
instance finite_ty {τ : Ty} [h : Fact (Ty.IsBool τ)] : Finite ((model p).ty τ) :=
  finite_ty_of_isBool h.out

/-- `⟦Γ⟧` is finite for every context `Γ` of PCF_bool types. -/
theorem finite_env_of_isBool {Γ : Ctx Base} (hΓ : ∀ a ∈ Γ, Ty.IsBool a) :
    Finite ((model p).Env Γ) :=
  (model p).finite_env finite_base_of_isBool hΓ

/-- `𝔹⊥` has three elements. -/
theorem card_ty_bool : Nat.card ((model p).ty Ty.bool) = 3 := by
  change Nat.card (Part Bool) = 3
  rw [Flat.card, Nat.card_eq_fintype_card, Fintype.card_bool]

/-- On the domain of a PCF_bool type, every monotone map is continuous: chains
in a finite domain are eventually constant. -/
theorem ωScottContinuous_of_monotone_of_isBool {σ : Ty} (hσ : Ty.IsBool σ) {E : Type*}
    [OmegaCompletePartialOrder E] {f : (model p).ty σ → E} (hf : Monotone f) :
    ωScottContinuous f :=
  haveI := finite_ty_of_isBool (p := p) hσ
  ωScottContinuous_of_monotone_of_finite hf

/-- For a PCF_bool type `σ`, `⟦σ -> τ⟧` is the poset of all monotone maps
`⟦σ⟧ → ⟦τ⟧` (the notes' "truth tables"). -/
noncomputable def arrowOrderIsoOfIsBool {σ : Ty} (hσ : Ty.IsBool σ) (τ : Ty) :
    (model p).ty (σ ⤳ τ) ≃o ((model p).ty σ →o (model p).ty τ) :=
  haveI := finite_ty_of_isBool (p := p) hσ
  continuousHomOrderIso

/-! ### The fragment -/

/-- The operators of PCF_bool: `true`, `false`, `if` at PCF_bool types, and the
primitive divergent term `Ω_bool`. -/
inductive BoolOp : List Ty → Ty → Type
  /-- `true`. -/
  | tt : BoolOp [] .bool
  /-- `false`. -/
  | ff : BoolOp [] .bool
  /-- `if b then t else t'` at a PCF_bool type. -/
  | ite (τ : Ty) (hτ : Ty.IsBool τ) : BoolOp [.bool, τ, τ] τ
  /-- The primitive divergent term `Ω_bool`. -/
  | omega : BoolOp [] .bool

/-- The signature of the PCF_bool operators, over all base types of PCF. Its
terms may bind variables of types mentioning `nat`; the notes' fragment proper
is `pcfBoolSig`. -/
abbrev boolSig : Signature := ⟨Base, BoolOp⟩

/-- Terms over the PCF_bool operators. They may bind variables of any PCF type,
so they form a superset of the notes' PCF_bool terms (`PCFBoolTerm`). -/
abbrev BoolTerm (Γ : Ctx Base) (τ : Ty) : Type := TypedLambda.Term boolSig Γ τ

namespace BoolTerm

variable {Γ : Ctx Base} {τ : Ty}

/-- `true`. -/
abbrev tt : BoolTerm Γ .bool := .op .tt .nil

/-- `false`. -/
abbrev ff : BoolTerm Γ .bool := .op .ff .nil

/-- `if b then t else t'`, at a PCF_bool type. -/
abbrev ite (hτ : Ty.IsBool τ) (b : BoolTerm Γ .bool) (t t' : BoolTerm Γ τ) : BoolTerm Γ τ :=
  .op (.ite τ hτ) (b ::ₜ t ::ₜ t' ::ₜ .nil)

/-- `Ω_bool`. -/
abbrev omega : BoolTerm Γ .bool := .op .omega .nil

end BoolTerm

/-- Each PCF_bool operator as a PCF term over its argument variables; `Ω_bool`
is `fix(fun x:bool. x)`. -/
def BoolOp.toPCF : {as : List Ty} → {τ : Ty} → BoolOp as τ → Term false as τ
  | _, _, .tt => Term.tt
  | _, _, .ff => Term.ff
  | _, _, .ite _ _ => Term.ite (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))
  | _, _, .omega => Term.omega .bool

/-- The inclusion of PCF_bool into PCF, a derived-operator translation. -/
abbrev BoolTerm.toPCF {Γ : Ctx Base} {τ : Ty} (t : BoolTerm Γ τ) : Term false Γ τ :=
  TypedLambda.Term.translate BoolOp.toPCF t

namespace BoolTerm

variable {Γ : Ctx Base} {τ : Ty}

/-- `true` is included as PCF's `true`. -/
@[simp] theorem toPCF_tt : toPCF (tt : BoolTerm Γ .bool) = Term.tt := Term.subst_tt _

/-- `false` is included as PCF's `false`. -/
@[simp] theorem toPCF_ff : toPCF (ff : BoolTerm Γ .bool) = Term.ff := Term.subst_ff _

/-- `Ω_bool` is included as PCF's `Ω_bool = fix(fun x:bool. x)`. -/
@[simp] theorem toPCF_omega : toPCF (omega : BoolTerm Γ .bool) = Term.omega .bool := by
  change (Term.omega .bool : Term false [] _).subst _ = _
  rw [Term.subst_fix]
  rfl

@[simp] theorem toPCF_ite (hτ : Ty.IsBool τ) (b : BoolTerm Γ .bool) (t t' : BoolTerm Γ τ) :
    toPCF (ite hτ b t t') = Term.ite (toPCF b) (toPCF t) (toPCF t') := by
  change (Term.ite _ _ _ : Term false [_, _, _] _).subst _ = _
  rw [Term.subst_ite]
  rfl

end BoolTerm

/-- The denotation of a PCF_bool operator: that of its translation into PCF. -/
noncomputable def BoolOp.denote {as : List Ty} {τ : Ty} (o : BoolOp as τ) :
    TyEnv baseDom as →𝒄 Ty.denote baseDom τ :=
  (model false).denote o.toPCF

/-- The domain model of PCF_bool, the restriction of that of PCF. -/
@[reducible] noncomputable def boolModel : Model boolSig := ⟨baseDom, BoolOp.denote⟩

section Denotation

variable {Γ : Ctx Base} {τ : Ty}

/-- The inclusion of PCF_bool into PCF preserves denotations. -/
theorem denote_toPCF (t : BoolTerm Γ τ) : denote t.toPCF = boolModel.denote t :=
  Model.denote_translate (M := boolModel) (op' := Op.denote) (fun _ => rfl) t

variable (ρ : boolModel.Env Γ)

@[simp] theorem boolModel_denote_tt :
    boolModel.denote (BoolTerm.tt : BoolTerm Γ .bool) ρ = (Part.some true : Part Bool) := rfl

@[simp] theorem boolModel_denote_ff :
    boolModel.denote (BoolTerm.ff : BoolTerm Γ .bool) ρ = (Part.some false : Part Bool) := rfl

/-- `⟦Ω_bool⟧ = ⊥`. -/
@[simp] theorem boolModel_denote_omega :
    boolModel.denote (BoolTerm.omega : BoolTerm Γ .bool) ρ = (⊥ : Part Bool) := by
  change (model false).denote (Term.omega .bool : Term false [] .bool) _ = _
  exact denote_omega _

/-- `⟦if b then t else t'⟧ = if(⟦b⟧, ⟦t⟧, ⟦t'⟧)`. -/
theorem boolModel_denote_ite (hτ : Ty.IsBool τ) (b : BoolTerm Γ .bool) (t t' : BoolTerm Γ τ) :
    boolModel.denote (BoolTerm.ite hτ b t t') ρ =
      condFun (boolModel.denote b ρ : Part Bool) (boolModel.denote t ρ)
        (boolModel.denote t' ρ) :=
  rfl

end Denotation

/-! ### Contextual equivalence over the PCF_bool operators -/

/-- The observation of `boolSig`: programs of type `bool`, evaluated through
their inclusion into PCF. -/
def boolObs : Observation boolSig :=
  ⟨fun γ => γ = Ty.bool, fun t v => BoolTerm.toPCF t ⇓ BoolTerm.toPCF v⟩

/-- `Ω_bool` diverges. -/
theorem boolObs_omega_diverges (v : BoolTerm [] .bool) : ¬ boolObs.Eval BoolTerm.omega v := by
  change ¬ BoolTerm.toPCF BoolTerm.omega ⇓ _
  rw [BoolTerm.toPCF_omega]
  exact omega_diverges _

/-- Soundness for PCF_bool, from soundness for PCF. -/
theorem boolObs_sound {γ : Ty} (_ : boolObs.Ground γ) {t v : BoolTerm [] γ}
    (h : boolObs.Eval t v) : boolModel.denoteClosed t = boolModel.denoteClosed v := by
  change boolModel.denote t Tuple.nil = boolModel.denote v Tuple.nil
  rw [← denote_toPCF, ← denote_toPCF]
  exact Eval.denoteClosed_eq (show BoolTerm.toPCF t ⇓ BoolTerm.toPCF v from h)

/-- Adequacy for PCF_bool, from adequacy for PCF. -/
theorem boolObs_adequate {γ : Ty} (hγ : boolObs.Ground γ) {t t' v : BoolTerm [] γ}
    (h : boolObs.Eval t' v) (hle : boolModel.denoteClosed v ≤ boolModel.denoteClosed t) :
    boolObs.Eval t v := by
  change boolModel.denote v Tuple.nil ≤ boolModel.denote t Tuple.nil at hle
  rw [← denote_toPCF, ← denote_toPCF] at hle
  change γ = Ty.bool at hγ
  subst hγ
  exact adequacy_of_eval (γ := Ty.bool) (t' := BoolTerm.toPCF t') trivial h hle

variable {Γ : Ctx Base} {τ : Ty}

/-- Evaluation of `boolSig` programs is sound and adequate for `boolModel`. -/
theorem boolObs_soundAdequate : boolObs.SoundAdequate boolModel :=
  ⟨boolObs_sound, boolObs_adequate⟩

/-- Theorem 24 for `boolSig`: terms over the PCF_bool operators with equal
denotations are contextually equivalent for the contexts of `boolSig`. -/
theorem boolCtxEquiv_of_denote_eq {t u : BoolTerm Γ τ}
    (h : boolModel.denote t = boolModel.denote u) : boolObs.CtxEquiv t u :=
  boolObs_soundAdequate.ctxEquiv_of_denote_eq h

/-- There are at most as many `boolSig` terms `Γ ⊢ t : τ` up to contextual
equivalence as elements of the finite domain `⟦Γ⟧ →𝒄 ⟦τ⟧`, for a PCF_bool type
`τ` and context `Γ` of PCF_bool types. -/
theorem card_boolCtxQuot_le (hΓ : ∀ a ∈ Γ, Ty.IsBool a) (hτ : Ty.IsBool τ) :
    Nat.card (boolObs.CtxQuot Γ τ) ≤
      Nat.card ((model false).Env Γ →𝒄 (model false).ty τ) :=
  haveI := boolModel.finite_denoteHom finite_base_of_isBool hΓ hτ
  boolObs_soundAdequate.card_ctxQuot_le

/-- There are finitely many `boolSig` terms `Γ ⊢ t : τ` up to contextual
equivalence, for every PCF_bool type `τ` and context `Γ` of PCF_bool types. -/
theorem finite_boolCtxQuot (hΓ : ∀ a ∈ Γ, Ty.IsBool a) (hτ : Ty.IsBool τ) :
    Finite (boolObs.CtxQuot Γ τ) :=
  haveI := boolModel.finite_denoteHom finite_base_of_isBool hΓ hτ
  boolObs_soundAdequate.finite_ctxQuot

/-! ### The notes' fragment -/

/-- The types of PCF_bool proper: simple types over the single base type
`bool`, here `Unit`. -/
abbrev BoolTy : Type := TypedLambda.Ty Unit

/-- A PCF_bool type as a PCF type. -/
def BoolTy.toTy : BoolTy → Ty
  | .base _ => Ty.bool
  | .arrow σ τ => BoolTy.toTy σ ⤳ BoolTy.toTy τ

/-- Every `BoolTy` is a PCF_bool type. -/
theorem BoolTy.isBool_toTy : ∀ τ : BoolTy, Ty.IsBool τ.toTy
  | .base _ => rfl
  | .arrow σ τ => ⟨isBool_toTy σ, isBool_toTy τ⟩

/-- `BoolTy.toTy` is injective. -/
theorem BoolTy.toTy_injective : Function.Injective BoolTy.toTy
  | .base _, .base _, _ => rfl
  | .arrow _ _, .arrow _ _, h => by
      injection h with h₁ h₂
      rw [toTy_injective h₁, toTy_injective h₂]

/-- The PCF_bool types are exactly the images of `BoolTy.toTy`. -/
theorem Ty.isBool_iff {τ : Ty} : Ty.IsBool τ ↔ ∃ σ : BoolTy, σ.toTy = τ := by
  refine ⟨fun h => ?_, fun ⟨σ, hσ⟩ => hσ ▸ σ.isBool_toTy⟩
  induction τ with
  | base b => exact ⟨.base (), by cases h; rfl⟩
  | arrow σ τ ihσ ihτ =>
      obtain ⟨σ', rfl⟩ := ihσ h.1
      obtain ⟨τ', rfl⟩ := ihτ h.2
      exact ⟨σ' ⤳ τ', rfl⟩

/-- The operators of PCF_bool proper: `true`, `false`, `if` at every PCF_bool
type, and `Ω_bool`. -/
inductive PCFBoolOp : List BoolTy → BoolTy → Type
  /-- `true`. -/
  | tt : PCFBoolOp [] (.base ())
  /-- `false`. -/
  | ff : PCFBoolOp [] (.base ())
  /-- `if b then t else t'`. -/
  | ite (τ : BoolTy) : PCFBoolOp [.base (), τ, τ] τ
  /-- The primitive divergent term `Ω_bool`. -/
  | omega : PCFBoolOp [] (.base ())

/-- The signature of PCF_bool proper, with the single base type `bool`. -/
abbrev pcfBoolSig : Signature := ⟨Unit, PCFBoolOp⟩

/-- The terms of PCF_bool, as in the notes: every variable, subterm and context
has a PCF_bool type. -/
abbrev PCFBoolTerm (Γ : Ctx Unit) (τ : BoolTy) : Type := TypedLambda.Term pcfBoolSig Γ τ

/-- `Ω_bool` in PCF_bool. -/
abbrev PCFBoolTerm.omega {Γ : Ctx Unit} : PCFBoolTerm Γ (.base ()) := .op .omega Tuple.nil

/-- The inclusion of PCF_bool into `boolSig`, translating the types along
`BoolTy.toTy`. -/
def PCFBoolTerm.embed : {Γ : Ctx Unit} → {τ : BoolTy} → PCFBoolTerm Γ τ →
    BoolTerm (Γ.map BoolTy.toTy) τ.toTy
  | _, _, .var x => .var (x.map BoolTy.toTy)
  | _, _, .lam t => .lam (embed t)
  | _, _, .app t u => .app (embed t) (embed u)
  | _, _, .op .tt _ => BoolTerm.tt
  | _, _, .op .ff _ => BoolTerm.ff
  | _, _, .op .omega _ => BoolTerm.omega
  | _, _, .op (.ite τ) args =>
      BoolTerm.ite τ.isBool_toTy (embed (args _ .zero)) (embed (args _ (.succ .zero)))
        (embed (args _ (.succ (.succ .zero))))

/-- The inclusion of PCF_bool into PCF. -/
abbrev PCFBoolTerm.toPCF {Γ : Ctx Unit} {τ : BoolTy} (t : PCFBoolTerm Γ τ) :
    Term false (Γ.map BoolTy.toTy) τ.toTy :=
  BoolTerm.toPCF (PCFBoolTerm.embed t)

/-- The denotations of the PCF_bool operators, on `𝔹⊥` and the function domains
built from it. -/
noncomputable def PCFBoolOp.denote {as : List BoolTy} {τ : BoolTy} :
    PCFBoolOp as τ → (TyEnv (fun _ => baseDom .bool) as →𝒄
      TypedLambda.Ty.denote (fun _ => baseDom .bool) τ)
  | .tt => ContinuousHom.const (Part.some true : Part Bool)
  | .ff => ContinuousHom.const (Part.some false : Part Bool)
  | .omega => ContinuousHom.const (⊥ : Part Bool)
  | .ite _ => cond.comp (pairHom (projHom _ .zero)
      (pairHom (projHom _ (.succ .zero)) (projHom _ (.succ (.succ .zero)))))

/-- The domain model of PCF_bool: `bool` denotes `𝔹⊥`. -/
@[reducible] noncomputable def pcfBoolModel : Model pcfBoolSig :=
  ⟨fun _ => baseDom .bool, PCFBoolOp.denote⟩

/-- Every domain of the model of PCF_bool is finite. -/
instance pcfBool_finite_ty (τ : BoolTy) : Finite (pcfBoolModel.ty τ) :=
  pcfBoolModel.finite_ty (P := fun _ => True) (fun _ _ => Flat.finite (X := Bool))
    (TypedLambda.Ty.allBase_of_forall (fun _ => trivial) τ)

/-- The possible denotations `⟦Γ⟧ →𝒄 ⟦τ⟧` of PCF_bool terms form a finite
set. -/
instance pcfBool_finite_denoteHom (Γ : Ctx Unit) (τ : BoolTy) :
    Finite (pcfBoolModel.Env Γ →𝒄 pcfBoolModel.ty τ) :=
  pcfBoolModel.finite_denoteHom (P := fun _ => True) (fun _ _ => Flat.finite (X := Bool))
    (fun a _ => TypedLambda.Ty.allBase_of_forall (fun _ => trivial) a)
    (TypedLambda.Ty.allBase_of_forall (fun _ => trivial) τ)

namespace PCFBool

/-- The logical relation between the models of PCF_bool and of `boolSig`, along
`BoolTy.toTy`: equality at `bool`, and related arguments to related results at
function types. -/
def Corr : (τ : BoolTy) → pcfBoolModel.ty τ → boolModel.ty τ.toTy → Prop
  | .base _, d, d' => (d : Part Bool) = d'
  | .arrow σ τ, f, f' => ∀ d d', Corr σ d d' →
      Corr τ (Model.app f d) (Model.app (M := boolModel) (σ := BoolTy.toTy σ) f' d')

/-- `⊥` is related to `⊥` at every type. -/
theorem corr_bot : (τ : BoolTy) → Corr τ ⊥ ⊥
  | .base _ => rfl
  | .arrow _ τ => fun _ _ _ => corr_bot τ

/-- The conditional preserves the relation. -/
theorem corr_condFun {τ : BoolTy} {c : Part Bool} {x y : pcfBoolModel.ty τ}
    {x' y' : boolModel.ty τ.toTy} (hx : Corr τ x x') (hy : Corr τ y y') :
    Corr τ (condFun c x y) (condFun c x' y') := by
  rcases Flat.bool_cases c with rfl | rfl | rfl
  · simp only [condFun_none]
    exact corr_bot τ
  · simpa only [condFun_true] using hx
  · simpa only [condFun_false] using hy

/-- Related environments: the value of each variable is related to the value of
its image under the inclusion. -/
def EnvCorr {Γ : Ctx Unit} (ρ : pcfBoolModel.Env Γ)
    (ρ' : boolModel.Env (Γ.map BoolTy.toTy)) : Prop :=
  ∀ a (x : Var Γ a), Corr a (ρ a x) (ρ' _ (x.map BoolTy.toTy))

/-- The fundamental lemma: the inclusion preserves denotations up to `Corr`. -/
theorem corr_denote : {Γ : Ctx Unit} → {τ : BoolTy} → (t : PCFBoolTerm Γ τ) →
    (ρ : pcfBoolModel.Env Γ) → (ρ' : boolModel.Env (Γ.map BoolTy.toTy)) → EnvCorr ρ ρ' →
      Corr τ (pcfBoolModel.denote t ρ) (boolModel.denote (PCFBoolTerm.embed t) ρ')
  | _, _, .var x, _, _, h => h _ x
  | _, _, .lam t, ρ, ρ', h => fun d d' hd => corr_denote t (d ::ₜ ρ) (d' ::ₜ ρ') fun
      | _, .zero => hd
      | a, .succ x => h a x
  | _, _, .app t u, ρ, ρ', h => corr_denote t ρ ρ' h _ _ (corr_denote u ρ ρ' h)
  | _, _, .op .tt _, _, _, _ => rfl
  | _, _, .op .ff _, _, _, _ => rfl
  | _, _, .op .omega _, _, ρ', _ => (boolModel_denote_omega ρ').symm
  | _, _, .op (.ite τ) args, ρ, ρ', h => by
      have hc : (pcfBoolModel.denote (args _ .zero) ρ : Part Bool) =
          boolModel.denote (PCFBoolTerm.embed (args _ .zero)) ρ' :=
        corr_denote (args _ .zero) ρ ρ' h
      change Corr τ (condFun _ _ _)
        (condFun (boolModel.denote (PCFBoolTerm.embed (args _ .zero)) ρ' : Part Bool) _ _)
      rw [← hc]
      exact corr_condFun (corr_denote (args _ (.succ .zero)) ρ ρ' h)
        (corr_denote (args _ (.succ (.succ .zero))) ρ ρ' h)

end PCFBool

/-- On closed programs of type `bool`, the inclusion of PCF_bool into `boolSig`
preserves denotations. -/
theorem denoteClosed_embed (t : PCFBoolTerm [] (.base ())) :
    (pcfBoolModel.denoteClosed t : Part Bool) =
      boolModel.denoteClosed (PCFBoolTerm.embed t) :=
  PCFBool.corr_denote t Tuple.nil Tuple.nil fun _ x => x.elim

/-- The observation of PCF_bool: programs of type `bool`, evaluated through
their inclusion into PCF. -/
def pcfBoolObs : Observation pcfBoolSig :=
  ⟨fun γ => γ = .base (), fun t v => boolObs.Eval (PCFBoolTerm.embed t) (PCFBoolTerm.embed v)⟩

/-- Evaluation of PCF_bool programs is sound and adequate for its model. -/
theorem pcfBoolObs_soundAdequate : pcfBoolObs.SoundAdequate pcfBoolModel := by
  refine ⟨fun {γ} hγ t v h => ?_, fun {γ} hγ t t' v h hle => ?_⟩
  · obtain rfl : γ = .base () := hγ
    have := boolObs_sound (γ := Ty.bool) rfl (t := PCFBoolTerm.embed t)
      (v := PCFBoolTerm.embed v) h
    change (pcfBoolModel.denoteClosed t : Part Bool) = pcfBoolModel.denoteClosed v
    rw [denoteClosed_embed, denoteClosed_embed]
    exact this
  · obtain rfl : γ = .base () := hγ
    change (pcfBoolModel.denoteClosed v : Part Bool) ≤ pcfBoolModel.denoteClosed t at hle
    rw [denoteClosed_embed, denoteClosed_embed] at hle
    exact boolObs_adequate (γ := Ty.bool) rfl (t' := PCFBoolTerm.embed t') h hle

/-- `Ω_bool` diverges in PCF_bool. -/
theorem pcfBoolObs_omega_diverges (v : PCFBoolTerm [] (.base ())) :
    ¬ pcfBoolObs.Eval PCFBoolTerm.omega v :=
  boolObs_omega_diverges _

section PCFBoolCtx

variable {Γ : Ctx Unit} {τ : BoolTy}

/-- Theorem 24 for PCF_bool: PCF_bool terms with equal denotations are
contextually equivalent for the contexts of PCF_bool. -/
theorem pcfBool_ctxEquiv_of_denote_eq {t u : PCFBoolTerm Γ τ}
    (h : pcfBoolModel.denote t = pcfBoolModel.denote u) : pcfBoolObs.CtxEquiv t u :=
  pcfBoolObs_soundAdequate.ctxEquiv_of_denote_eq h

/-- There are at most as many PCF_bool terms `Γ ⊢ t : τ` up to contextual
equivalence as elements of the finite domain `⟦Γ⟧ →𝒄 ⟦τ⟧`. -/
theorem pcfBool_card_ctxQuot_le :
    Nat.card (pcfBoolObs.CtxQuot Γ τ) ≤
      Nat.card (pcfBoolModel.Env Γ →𝒄 pcfBoolModel.ty τ) :=
  pcfBoolObs_soundAdequate.card_ctxQuot_le

/-- There are finitely many PCF_bool terms `Γ ⊢ t : τ` up to contextual
equivalence, at every type and in every context. -/
theorem pcfBool_finite_ctxQuot : Finite (pcfBoolObs.CtxQuot Γ τ) :=
  pcfBoolObs_soundAdequate.finite_ctxQuot

end PCFBoolCtx

end Silmaril.Calculi.PCF

module

public import Silmaril.Logic.Metamath.SetMM.Axioms
public import Silmaril.Logic.Metamath.Model.PredCalc
public import Silmaril.Logic.SetTheory.ZFSetModel

@[expose] public section

/-!
# The ZFSet model of set.mm's ZFC

The standard environment model (`Silmaril.Logic.Metamath.EnvModel`, Carneiro,
*Models for Metamath*, §3.3) of `SetMM.grammar` over a membership structure
`D` and an infinite type of names `N` (`SetMM.envModel`, `SetMM.model`):

* `setvar` denotes names, `wff` finitely supported predicates of environments
  `Env D N → Prop`, and `class` finitely supported functions `Env D N → Set D`
  (class terms; for `D = ZFSet` these are Mathlib's `Class`);
* the connectives, quantifiers, `cv`, `=` and `e.` are those of
  `Silmaril.Logic.Metamath.Model.SetMM`;
* `|- ph` holds when `ph` is valid.

Every axiom of `PropCalc` holds in every such model, every axiom of
`PredCalc` and the definitions `df-bi`, `df-an`, `df-or`, `df-ex` over an
extensional `D` (`isModel_predCalc`, `sat_defs`), and every axiom of `ZF` and
`ZFC` for `D = ZFSet.{u}` (`isModel_zf`, `isModel_zfc`), by the semantic
facts of `Silmaril.Logic.SetTheory.PredicateCalculus` and
`Silmaril.Logic.SetTheory.ZFSetModel`. A disjoint-variable condition between
two set variables makes their names distinct (`name_ne`), and one between a
set variable and a formula variable makes the formula ignore the name
(`notFree_of_dv`).
-/

namespace Silmaril.Logic.Metamath.SetMM

open Silmaril.Logic.Metamath Grammar Grammar.TAssertion Silmaril.Logic.SetTheory Function Env
open Silmaril.Logic.Metamath.Model.SetMM (opNot opImp opIff opAnd opOr opAll opEx opCv opEq opEl
  termEq termMem Extensional opEq_cv opEl_cv)

universe u w

variable (D : Type w) [Membership D D] (N : Type w) [DecidableEq N]

/-- The kinds of the typecodes: set variables are names, formulas are
formulas, classes are functions into `Set D`. -/
abbrev kind : String → Kind.{w}
  | "setvar" => .name
  | "wff" => .formula
  | "class" => .term (Set D) ∅
  | _ => .term PUnit PUnit.unit

/-- The truth predicate: a formula is true when it is valid. -/
def truth : (s : String) → (kind D s).Carrier D N → Prop
  | "wff", (φ : Term D N Prop) => Valid φ.1
  | _, _ => False

/-- The standard environment model of `SetMM.grammar`. -/
abbrev envModel : EnvModel grammar D N where
  kind := kind D
  op {s} o a := match s, o, a with
    | _, ⟨.wn, rfl⟩, a => opNot (a ⟨0, by decide⟩)
    | _, ⟨.wi, rfl⟩, a => opImp (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wb, rfl⟩, a => opIff (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wa, rfl⟩, a => opAnd (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wo, rfl⟩, a => opOr (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wal, rfl⟩, a => opAll (a ⟨1, by decide⟩) (a ⟨0, by decide⟩)
    | _, ⟨.wex, rfl⟩, a => opEx (a ⟨1, by decide⟩) (a ⟨0, by decide⟩)
    | _, ⟨.cv, rfl⟩, a => opCv (a ⟨0, by decide⟩)
    | _, ⟨.wceq, rfl⟩, a => opEq (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wcel, rfl⟩, a => opEl (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
  fresh_op {s t} a o args h := by
    obtain ⟨l, rfl⟩ := o
    refine Kind.fresh_of_ignores (by cases l <;> rfl) fun x hx => ?_
    have hj := fun j => (h j).of_name hx
    cases l with
    | wn => exact Term.notFree_map (hj ⟨0, Nat.zero_lt_one⟩).2
    | wi => exact Term.notFree_map₂ (hj ⟨0, Nat.two_pos⟩).2 (hj ⟨1, Nat.one_lt_two⟩).2
    | wb => exact Term.notFree_map₂ (hj ⟨0, Nat.two_pos⟩).2 (hj ⟨1, Nat.one_lt_two⟩).2
    | wa => exact Term.notFree_map₂ (hj ⟨0, Nat.two_pos⟩).2 (hj ⟨1, Nat.one_lt_two⟩).2
    | wo => exact Term.notFree_map₂ (hj ⟨0, Nat.two_pos⟩).2 (hj ⟨1, Nat.one_lt_two⟩).2
    | wal => exact Term.notFree_bind ((hj ⟨1, Nat.one_lt_two⟩).1 _ rfl) (hj ⟨0, Nat.two_pos⟩).2
    | wex => exact Term.notFree_bind ((hj ⟨1, Nat.one_lt_two⟩).1 _ rfl) (hj ⟨0, Nat.two_pos⟩).2
    | cv => exact Term.notFree_name ((hj ⟨0, Nat.zero_lt_one⟩).1 _ rfl)
    | wceq => exact Term.notFree_map₂ (hj ⟨0, Nat.two_pos⟩).2 (hj ⟨1, Nat.one_lt_two⟩).2
    | wcel => exact Term.notFree_map₂ (hj ⟨0, Nat.two_pos⟩).2 (hj ⟨1, Nat.one_lt_two⟩).2
  IsTrue {_ s} _ a := truth D N s a

variable [Infinite N]

/-- The standard environment model, as a model of the grammar. -/
abbrev model : Model grammar := (envModel D N).toModel

variable {D N}

/-! ## Computing values -/

section Values

variable {ctx : String → String → Prop} (ρ : (model D N).Valuation ctx)

/-- The sorting context of values. -/
local notation "HS" t:max s:max => grammar.HasSort (grammar.synCtx ctx) t s

theorem wn_0 {a : Tree L String} (h : HS (.node .wn [a]) "wff") : HS a "wff" :=
  h.child ⟨0, by decide⟩
theorem wi_0 {a b : Tree L String} (h : HS (.node .wi [a, b]) "wff") : HS a "wff" :=
  h.child ⟨0, by decide⟩
theorem wi_1 {a b : Tree L String} (h : HS (.node .wi [a, b]) "wff") : HS b "wff" :=
  h.child ⟨1, by decide⟩
theorem wb_0 {a b : Tree L String} (h : HS (.node .wb [a, b]) "wff") : HS a "wff" :=
  h.child ⟨0, by decide⟩
theorem wb_1 {a b : Tree L String} (h : HS (.node .wb [a, b]) "wff") : HS b "wff" :=
  h.child ⟨1, by decide⟩
theorem wa_0 {a b : Tree L String} (h : HS (.node .wa [a, b]) "wff") : HS a "wff" :=
  h.child ⟨0, by decide⟩
theorem wa_1 {a b : Tree L String} (h : HS (.node .wa [a, b]) "wff") : HS b "wff" :=
  h.child ⟨1, by decide⟩
theorem wo_0 {a b : Tree L String} (h : HS (.node .wo [a, b]) "wff") : HS a "wff" :=
  h.child ⟨0, by decide⟩
theorem wo_1 {a b : Tree L String} (h : HS (.node .wo [a, b]) "wff") : HS b "wff" :=
  h.child ⟨1, by decide⟩
theorem wal_0 {a b : Tree L String} (h : HS (.node .wal [a, b]) "wff") : HS a "wff" :=
  h.child ⟨0, by decide⟩
theorem wal_1 {a b : Tree L String} (h : HS (.node .wal [a, b]) "wff") : HS b "setvar" :=
  h.child ⟨1, by decide⟩
theorem wex_0 {a b : Tree L String} (h : HS (.node .wex [a, b]) "wff") : HS a "wff" :=
  h.child ⟨0, by decide⟩
theorem wex_1 {a b : Tree L String} (h : HS (.node .wex [a, b]) "wff") : HS b "setvar" :=
  h.child ⟨1, by decide⟩
theorem cv_0 {a : Tree L String} (h : HS (.node .cv [a]) "class") : HS a "setvar" :=
  h.child ⟨0, by decide⟩
theorem wceq_0 {a b : Tree L String} (h : HS (.node .wceq [a, b]) "wff") : HS a "class" :=
  h.child ⟨0, by decide⟩
theorem wceq_1 {a b : Tree L String} (h : HS (.node .wceq [a, b]) "wff") : HS b "class" :=
  h.child ⟨1, by decide⟩
theorem wcel_0 {a b : Tree L String} (h : HS (.node .wcel [a, b]) "wff") : HS a "class" :=
  h.child ⟨0, by decide⟩
theorem wcel_1 {a b : Tree L String} (h : HS (.node .wcel [a, b]) "wff") : HS b "class" :=
  h.child ⟨1, by decide⟩

theorem value_wn {a : Tree L String} (h : HS (.node .wn [a]) "wff") :
    (model D N).value ρ _ h = opNot (D := D) (N := N) ((model D N).value ρ a (wn_0 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wi {a b : Tree L String} (h : HS (.node .wi [a, b]) "wff") :
    (model D N).value ρ _ h = opImp (D := D) (N := N) ((model D N).value ρ a (wi_0 h))
      ((model D N).value ρ b (wi_1 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wb {a b : Tree L String} (h : HS (.node .wb [a, b]) "wff") :
    (model D N).value ρ _ h = opIff (D := D) (N := N) ((model D N).value ρ a (wb_0 h))
      ((model D N).value ρ b (wb_1 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wa {a b : Tree L String} (h : HS (.node .wa [a, b]) "wff") :
    (model D N).value ρ _ h = opAnd (D := D) (N := N) ((model D N).value ρ a (wa_0 h))
      ((model D N).value ρ b (wa_1 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wo {a b : Tree L String} (h : HS (.node .wo [a, b]) "wff") :
    (model D N).value ρ _ h = opOr (D := D) (N := N) ((model D N).value ρ a (wo_0 h))
      ((model D N).value ρ b (wo_1 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wal {a b : Tree L String} (h : HS (.node .wal [a, b]) "wff") :
    (model D N).value ρ _ h = opAll (D := D) (N := N) ((model D N).value ρ b (wal_1 h))
      ((model D N).value ρ a (wal_0 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wex {a b : Tree L String} (h : HS (.node .wex [a, b]) "wff") :
    (model D N).value ρ _ h = opEx (D := D) (N := N) ((model D N).value ρ b (wex_1 h))
      ((model D N).value ρ a (wex_0 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_cv {a : Tree L String} (h : HS (.node .cv [a]) "class") :
    (model D N).value ρ _ h = opCv (D := D) (N := N) ((model D N).value ρ a (cv_0 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wceq {a b : Tree L String} (h : HS (.node .wceq [a, b]) "wff") :
    (model D N).value ρ _ h = opEq (D := D) (N := N) ((model D N).value ρ a (wceq_0 h))
      ((model D N).value ρ b (wceq_1 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wcel {a b : Tree L String} (h : HS (.node .wcel [a, b]) "wff") :
    (model D N).value ρ _ h = opEl (D := D) (N := N) ((model D N).value ρ a (wcel_0 h))
      ((model D N).value ρ b (wcel_1 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

end Values

theorem holds_iff {ctx : String → String → Prop} (ρ : (model D N).Valuation ctx)
    (t : Tree L String) :
    (model D N).Holds ρ (pf t) ↔ ∃ h : grammar.HasSort (grammar.synCtx ctx) t "wff",
      Valid ((model D N).value ρ t h : Term D N Prop).1 := by
  constructor
  · rintro ⟨s, hs, ht, htrue⟩
    obtain rfl : "wff" = s := Option.some.inj hs
    exact ⟨ht, htrue⟩
  · rintro ⟨ht, htrue⟩
    exact ⟨"wff", rfl, ht, htrue⟩

/-- A well-formed assertion at `|-` holds when the value of its conclusion is
valid under every valuation satisfying its hypotheses. -/
theorem satisfies_of_valid {A : TAssertion L String String} {t : Tree L String}
    (hA : A.WellFormed grammar) (hc : A.concl = pf t)
    (h : ∀ ρ : (model D N).Valuation A.ctx, (model D N).DVHolds ρ A.dv →
      (∀ e ∈ A.essentials, (model D N).Holds ρ e) →
      ∀ ht : grammar.HasSort (grammar.synCtx A.ctx) t "wff",
        Valid ((model D N).value ρ t ht : Term D N Prop).1) :
    (model D N).Satisfies A := by
  intro ρ hdv hess
  obtain ⟨s, hs, ht⟩ := hA.concl_wellTyped
  rw [hc] at hs ht ⊢
  obtain rfl : "wff" = s := Option.some.inj hs
  exact (holds_iff ρ _).2 ⟨ht.synCtx rfl, h ρ hdv hess _⟩

/-! ## Disjoint-variable conditions -/

/-- A variable declared by the floating hypothesis found by `sortOf`. -/
theorem synCtx_of_sortOf {A : TAssertion L String String} {x s : String}
    (h : A.sortOf x = some s) (hs : IsSort s = true) : grammar.synCtx A.ctx x s :=
  ⟨ctx_of_sortOf h, hs⟩

/-- Set variables declared disjoint denote distinct names. -/
theorem name_ne {A : TAssertion L String String} {ρ : (model D N).Valuation A.ctx}
    (hdv : (model D N).DVHolds ρ A.dv) {x y : String} (hxy : (x, y) ∈ A.dv ∨ (y, x) ∈ A.dv)
    (hne : x ≠ y) (hx : grammar.synCtx A.ctx x "setvar") (hy : grammar.synCtx A.ctx y "setvar") :
    (ρ x "setvar" hx : N) ≠ ρ y "setvar" hy := by
  rcases hxy with hxy | hyx
  · exact Kind.fresh_name_name.1 (hdv x y hxy hne "setvar" "setvar" hx hy)
  · exact (Kind.fresh_name_name.1 (hdv y x hyx (Ne.symm hne) "setvar" "setvar" hy hx)).symm

/-- A formula variable declared disjoint from a set variable ignores its name. -/
theorem notFree_of_dv {A : TAssertion L String String} {ρ : (model D N).Valuation A.ctx}
    (hdv : (model D N).DVHolds ρ A.dv) {x ph : String} (hxy : (x, ph) ∈ A.dv)
    (hne : x ≠ ph) (hx : grammar.synCtx A.ctx x "setvar") (hph : grammar.synCtx A.ctx ph "wff") :
    Wff.NotFree (ρ x "setvar" hx : N) (ρ ph "wff" hph : Term D N Prop).1 :=
  notFree_iff.1 (Kind.fresh_name_formula.1 (hdv x ph hxy hne "setvar" "wff" hx hph))

/-- The name of the set variable `x` under `ρ`, or an arbitrary name when `x`
is not a declared set variable. -/
noncomputable def setName {ctx : String → String → Prop} (ρ : (model D N).Valuation ctx)
    (x : String) : N :=
  have := Classical.propDecidable
  if h : grammar.synCtx ctx x "setvar" then ρ x "setvar" h else Classical.arbitrary N

theorem setName_eq {ctx : String → String → Prop} (ρ : (model D N).Valuation ctx) {x : String}
    (h : grammar.synCtx ctx x "setvar") : ρ x "setvar" h = setName ρ x :=
  by simp [setName, h]

/-- Set variables declared disjoint have distinct names. -/
theorem setName_ne {A : TAssertion L String String} {ρ : (model D N).Valuation A.ctx}
    (hdv : (model D N).DVHolds ρ A.dv) {x y : String} (hxy : (x, y) ∈ A.dv ∨ (y, x) ∈ A.dv)
    (hne : x ≠ y) (hx : grammar.synCtx A.ctx x "setvar") (hy : grammar.synCtx A.ctx y "setvar") :
    setName ρ x ≠ setName ρ y := by
  rw [← setName_eq ρ hx, ← setName_eq ρ hy]
  exact name_ne hdv hxy hne hx hy

/-- Distinct members of a list form a pair of `dvAll`, in some order. -/
theorem mem_dvAll {l : List String} {x y : String} (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) :
    (x, y) ∈ dvAll l ∨ (y, x) ∈ dvAll l := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [dvAll, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.1 hx with hxa | hx' <;> rcases List.mem_cons.1 hy with hya | hy'
    · exact absurd (hxa.trans hya.symm) hne
    · exact Or.inl (Or.inl ⟨y, hy', by rw [hxa], rfl⟩)
    · exact Or.inr (Or.inl ⟨x, hx', by rw [hya], rfl⟩)
    · rcases ih hx' hy' with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

/-! ## Propositional calculus and definitions -/

theorem sat_axMp : (model D N).Satisfies axMp := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ hess ht => ?_
  obtain ⟨h₁, v₁⟩ := (holds_iff ρ _).1 (hess (pf (wv "ph")) (by simp [axMp, essentials]))
  obtain ⟨h₂, v₂⟩ := (holds_iff ρ _).1
    (hess (pf (wi (wv "ph") (wv "ps"))) (by simp [axMp, essentials]))
  simp only [value_wi, Model.value_var] at v₁ v₂ ⊢
  exact PredicateCalculus.valid_mp v₁ v₂

theorem sat_ax1 : (model D N).Satisfies ax1 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, Model.value_var]
  exact PredicateCalculus.valid_ax1 _ _

theorem sat_ax2 : (model D N).Satisfies ax2 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, Model.value_var]
  exact PredicateCalculus.valid_ax2 _ _ _

theorem sat_ax3 : (model D N).Satisfies ax3 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wn, Model.value_var]
  exact PredicateCalculus.valid_ax3 _ _

/-- Every environment model is a model of propositional calculus. -/
theorem isModel_propCalc : (model D N).IsModel propCalc := by
  rintro B ⟨p, hp, rfl⟩
  simp only [propCalcList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  exacts [sat_axMp, sat_ax1, sat_ax2, sat_ax3]

theorem sat_dfBi : (model D N).Satisfies dfBi := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wn, value_wb, Model.value_var]
  intro _
  dsimp only [opNot, opImp, opIff, opAnd, opOr, Term.map, Term.map₂]
  tauto

theorem sat_dfAn : (model D N).Satisfies dfAn := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wn, value_wb, value_wa, Model.value_var]
  intro _
  dsimp only [opNot, opImp, opIff, opAnd, opOr, Term.map, Term.map₂]
  tauto

theorem sat_dfOr : (model D N).Satisfies dfOr := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wn, value_wb, value_wo, Model.value_var]
  intro _
  dsimp only [opNot, opImp, opIff, opAnd, opOr, Term.map, Term.map₂]
  tauto

theorem sat_dfEx : (model D N).Satisfies dfEx := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wn, value_wb, value_wal, value_wex, Model.value_var]
  exact PredicateCalculus.valid_dfEx _ _

/-- Every environment model satisfies `df-bi`, `df-an`, `df-or` and `df-ex`. -/
theorem isModel_defs : (model D N).IsModel (ofList defsList) := by
  rintro B ⟨p, hp, rfl⟩
  simp only [defsList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  exacts [sat_dfBi, sat_dfAn, sat_dfOr, sat_dfEx]

/-! ## Predicate calculus -/

section PredCalc

open PredicateCalculus

theorem sat_axGen : (model D N).Satisfies axGen := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ hess ht => ?_
  obtain ⟨h₁, v₁⟩ := (holds_iff ρ _).1 (hess (pf (wv "ph")) (by simp [axGen, essentials]))
  simp only [value_wal, Model.value_var] at v₁ ⊢
  exact valid_gen _ v₁

theorem sat_ax4 : (model D N).Satisfies ax4 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wal, Model.value_var]
  exact valid_ax4 _ _ _

theorem sat_ax5 : (model D N).Satisfies ax5 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ ht => ?_
  simp only [value_wi, value_wal, Model.value_var]
  exact valid_ax5 (notFree_of_dv hdv (by decide) (by decide)
    (synCtx_of_sortOf (by decide) rfl) (synCtx_of_sortOf (by decide) rfl))

variable (hext : Extensional D)
include hext

theorem sat_ax6 : (model D N).Satisfies ax6 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wn, value_wal, value_wceq, value_cv, Model.value_var, opEq_cv (N := N) hext]
  exact valid_ax6 _ _

theorem sat_ax7 : (model D N).Satisfies ax7 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wceq, value_cv, Model.value_var, opEq_cv (N := N) hext]
  exact valid_ax7 _ _ _

theorem sat_ax8 : (model D N).Satisfies ax8 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wceq, value_wcel, value_cv, Model.value_var, opEq_cv (N := N) hext,
    opEl_cv (N := N) hext]
  exact valid_ax8 _ _ _

theorem sat_ax9 : (model D N).Satisfies ax9 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wceq, value_wcel, value_cv, Model.value_var, opEq_cv (N := N) hext,
    opEl_cv (N := N) hext]
  exact valid_ax9 _ _ _

omit hext in
theorem sat_ax10 : (model D N).Satisfies ax10 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wn, value_wal, Model.value_var]
  exact valid_ax10 _ _

omit hext in
theorem sat_ax11 : (model D N).Satisfies ax11 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wal, Model.value_var]
  exact valid_ax11 _ _ _

theorem sat_ax12 : (model D N).Satisfies ax12 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wal, value_wceq, value_cv, Model.value_var, opEq_cv (N := N) hext]
  exact valid_ax12 _ _ _

theorem sat_ax13 : (model D N).Satisfies ax13 := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wn, value_wal, value_wceq, value_cv, Model.value_var,
    opEq_cv (N := N) hext]
  exact valid_ax13 _ _ _

/-- Every environment model over an extensional membership structure is a
model of set.mm's predicate calculus. -/
theorem isModel_predCalc : (model D N).IsModel predCalc := by
  rintro B ⟨p, hp, rfl⟩
  simp only [predCalcList, propCalcList, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  exacts [sat_axMp, sat_ax1, sat_ax2, sat_ax3, sat_axGen, sat_ax4, sat_ax5, sat_ax6 hext,
    sat_ax7 hext, sat_ax8 hext, sat_ax9 hext, sat_ax10, sat_ax11, sat_ax12 hext, sat_ax13 hext]

end PredCalc

/-! ## Set theory in `ZFSet` -/

section ZF

open ZFSetModel

variable {N : Type (u + 1)} [DecidableEq N] [Infinite N]

/-- Membership in `ZFSet` is extensional. -/
theorem extensional_zfset : Extensional ZFSet.{u} := fun _ _ => ZFSet.ext

/-- The declared set variable `x` of `A`. -/
local macro "sv" : term => `(synCtx_of_sortOf (by decide) rfl)

/-- Distinct names of set variables declared disjoint. -/
local macro "nn" : term => `(name_ne ‹_› (by decide) (by decide) sv sv)

theorem sat_axExt : (model ZFSet.{u} N).Satisfies axExt := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ ht => ?_
  simp only [value_wi, value_wb, value_wal, value_wceq, value_wcel, value_cv, Model.value_var,
    opEq_cv (N := N) extensional_zfset, opEl_cv (N := N) extensional_zfset]
  exact valid_ext nn nn

theorem sat_axRep : (model ZFSet.{u} N).Satisfies axRep := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ ht => ?_
  simp only [value_wi, value_wb, value_wa, value_wal, value_wex, value_wceq, value_wcel, value_cv,
    Model.value_var, opEq_cv (N := N) extensional_zfset, opEl_cv (N := N) extensional_zfset]
  refine valid_rep ?_ ?_ ?_ ?_ ?_ ?_ _ <;> exact nn

theorem sat_axSep : (model ZFSet.{u} N).Satisfies axSep := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ ht => ?_
  simp only [value_wb, value_wa, value_wal, value_wex, value_wcel, value_cv, Model.value_var,
    opEl_cv (N := N) extensional_zfset]
  refine valid_sep ?_ ?_ ?_ _ (notFree_of_dv hdv ?_ ?_ sv sv)
  all_goals first | exact nn | decide

theorem sat_axNul : (model ZFSet.{u} N).Satisfies axNul := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ ht => ?_
  simp only [value_wn, value_wal, value_wex, value_wcel, value_cv, Model.value_var,
    opEl_cv (N := N) extensional_zfset]
  exact valid_nul _ _

theorem sat_axPow : (model ZFSet.{u} N).Satisfies axPow := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ ht => ?_
  simp only [value_wi, value_wal, value_wex, value_wcel, value_cv, Model.value_var,
    opEl_cv (N := N) extensional_zfset]
  exact valid_pow nn nn nn nn nn nn

theorem sat_axPr : (model ZFSet.{u} N).Satisfies axPr := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ ht => ?_
  simp only [value_wi, value_wo, value_wal, value_wex, value_wceq, value_wcel, value_cv,
    Model.value_var, opEq_cv (N := N) extensional_zfset, opEl_cv (N := N) extensional_zfset]
  exact valid_pr nn nn nn nn nn

theorem sat_axUn : (model ZFSet.{u} N).Satisfies axUn := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ ht => ?_
  simp only [value_wi, value_wa, value_wal, value_wex, value_wcel, value_cv, Model.value_var,
    opEl_cv (N := N) extensional_zfset]
  exact valid_un nn nn nn nn nn nn

theorem sat_axReg : (model ZFSet.{u} N).Satisfies axReg := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ ht => ?_
  simp only [value_wi, value_wn, value_wa, value_wal, value_wex, value_wcel, value_cv,
    Model.value_var, opEl_cv (N := N) extensional_zfset]
  exact valid_reg nn nn nn

theorem sat_axInf : (model ZFSet.{u} N).Satisfies axInf := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ ht => ?_
  simp only [value_wi, value_wa, value_wal, value_wex, value_wcel, value_cv, Model.value_var,
    opEl_cv (N := N) extensional_zfset]
  exact valid_inf nn nn nn nn

theorem sat_axAc : (model ZFSet.{u} N).Satisfies axAc := by
  refine satisfies_of_valid (.of_checkWF (by decide)) rfl fun ρ hdv _ ht => ?_
  simp only [value_wi, value_wb, value_wa, value_wal, value_wex, value_wceq, value_wcel, value_cv,
    Model.value_var, opEq_cv (N := N) extensional_zfset, opEl_cv (N := N) extensional_zfset]
  exact valid_ac nn nn nn nn nn nn nn nn nn nn nn nn nn nn nn nn nn nn

/-- The set-theoretic axioms of `ZF` hold in the `ZFSet` model. -/
theorem isModel_zfAx : (model ZFSet.{u} N).IsModel (ofList zfAxList) := by
  rintro B ⟨p, hp, rfl⟩
  simp only [zfAxList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [sat_axExt, sat_axRep, sat_axSep, sat_axNul, sat_axPow, sat_axPr, sat_axUn, sat_axReg,
    sat_axInf]

theorem ofList_append (l l' : LList) : ofList (l ++ l') = ofList l ∪ ofList l' := by
  ext A
  simp only [ofList, List.mem_append, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨p, hp | hp, e⟩
    exacts [Or.inl ⟨p, hp, e⟩, Or.inr ⟨p, hp, e⟩]
  · rintro (⟨p, hp, e⟩ | ⟨p, hp, e⟩)
    exacts [⟨p, Or.inl hp, e⟩, ⟨p, Or.inr hp, e⟩]

/-- The `ZFSet` model is a model of set.mm's `ZF` with its definitions. -/
theorem isModel_zf : (model ZFSet.{u} N).IsModel zf := by
  simp only [zf, zfList, ofList_append, Model.isModel_union]
  exact ⟨⟨isModel_predCalc extensional_zfset, isModel_defs⟩, isModel_zfAx⟩

/-- The `ZFSet` model is a model of set.mm's `ZFC` with its definitions. -/
theorem isModel_zfc : (model ZFSet.{u} N).IsModel zfc := by
  simp only [zfc, zfcList, ofList_append, Model.isModel_union]
  refine ⟨isModel_zf, ?_⟩
  rintro B ⟨p, hp, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact sat_axAc

end ZF

end Silmaril.Logic.Metamath.SetMM

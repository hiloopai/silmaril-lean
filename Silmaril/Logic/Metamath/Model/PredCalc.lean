module

public import Silmaril.Logic.Metamath.Model.Env
public import Silmaril.Logic.Metamath.Model.Consistency
public import Silmaril.Logic.Metamath.Model.Check
public import Silmaril.Logic.Metamath.Grammar.Examples
public import Silmaril.Logic.SetTheory.PredicateCalculus
public import Mathlib.SetTheory.ZFC.Basic

@[expose] public section

/-!
# The predicate calculus of set.mm in environment models

The primitive grammar of set.mm (`Grammar.Examples.SetMM`: `wn`, `wi`, `wb`,
`wa`, `wo`, `wal`, `wex`, `cv`, `wceq`, `wcel`, `cab`) over the variables
`ph ps ch x y z A B`, and its standard environment model (Carneiro, *Models
for Metamath*, §3.3) over any membership structure `D` and any infinite type
of names `N` (`SetMM.envModel`):

* `setvar` denotes names, `wff` finitely supported formulas `Env D N → Prop`,
  and `class` finitely supported functions `Env D N → Set D`;
* the connectives and quantifiers are those of `SetTheory.Wff`, `cv x` is the
  class of members of `x`, `A = B` is equality of classes, `A e. B` holds when
  `A` is the class of members of some member of `B`, and `{ x | ph }` is class
  abstraction;
* `|- ph` holds when `ph` is valid.

The axioms and rules of set.mm's predicate calculus, `ax-mp`, `ax-1` to
`ax-3`, `ax-gen` and `ax-4` to `ax-13` (`SetMM.predCalc`), transcribed as tree
assertions with set.mm's mandatory hypotheses and disjoint-variable
conditions, hold in every environment model over an extensional membership
structure (`SetMM.isModel_predCalc`), by the semantic facts of
`Silmaril.Logic.SetTheory.PredicateCalculus`. Extensionality makes class
equality and membership of set variables the primitive ones. The model is not
trivial at `|-`, so the predicate calculus is consistent
(`SetMM.tConsistent_predCalc`).

The ZFC axioms can be added to `predCalc` and checked in the environment
model over `ZFSet` with `Silmaril.Logic.SetTheory.ZFSetModel`.
-/

namespace Silmaril.Logic.Metamath.Model.SetMM

open Silmaril.Logic.Metamath Grammar Grammar.TAssertion Silmaril.Logic.SetTheory Function Env
universe w

/-- Typecodes and constants of set.mm's primitive grammar. -/
abbrev C := Grammar.Examples.SetMM.C

/-- Rule labels of set.mm's primitive grammar. -/
abbrev L := Grammar.Examples.SetMM.L

/-- Variables: formulas `ph ps ch`, set variables `x y z` and classes `A B`. -/
inductive V
  | ph | ps | ch | x | y | z | A | B
  deriving DecidableEq, Repr

open Grammar.Examples.SetMM.C V in
/-- The primitive syntax rules of set.mm, with floating hypotheses in database
order. -/
def rules : L → SyntaxRule C V
  | .wn => Grammar.Examples.rule wff [(wff, ph)] [.const not, .var ph]
  | .wi => Grammar.Examples.rule wff [(wff, ph), (wff, ps)]
      [.const lp, .var ph, .const imp, .var ps, .const rp]
  | .wb => Grammar.Examples.rule wff [(wff, ph), (wff, ps)]
      [.const lp, .var ph, .const bi, .var ps, .const rp]
  | .wa => Grammar.Examples.rule wff [(wff, ph), (wff, ps)]
      [.const lp, .var ph, .const and, .var ps, .const rp]
  | .wo => Grammar.Examples.rule wff [(wff, ph), (wff, ps)]
      [.const lp, .var ph, .const or, .var ps, .const rp]
  | .wal => Grammar.Examples.rule wff [(wff, ph), (setvar, x)] [.const all, .var x, .var ph]
  | .wex => Grammar.Examples.rule wff [(wff, ph), (setvar, x)] [.const ex, .var x, .var ph]
  | .cv => Grammar.Examples.rule «class» [(setvar, x)] [.var x]
  | .wceq => Grammar.Examples.rule wff [(«class», A), («class», B)] [.var A, .const eq, .var B]
  | .wcel => Grammar.Examples.rule wff [(«class», A), («class», B)] [.var A, .const el, .var B]
  | .cab => Grammar.Examples.rule «class» [(wff, ph), (setvar, x)]
      [.const lb, .var x, .const bar, .var ph, .const rb]

/-- The grammar; `|-` is read as `wff`. -/
def grammar : Grammar L C V where
  sorts := {c | Grammar.Examples.SetMM.IsSort c}
  prov := fun
    | .turnstile => some .wff
    | _ => none
  rule := rules
  rule_tc l := by cases l <;> rfl
  rule_args l := by cases l <;> decide
  prov_sort {c s} h := by cases c <;> cases h; rfl
  prov_not_sort {c s} h := by cases c <;> cases h; decide

instance : DecidablePred (· ∈ grammar.sorts) :=
  fun c => inferInstanceAs (Decidable (Grammar.Examples.SetMM.IsSort c))

theorem unambiguous : grammar.Unambiguous :=
  LLCert.unambiguous (F := Grammar.Examples.SetMM.first) (by decide)

/-! ## Tree notation -/

/-- `-. t`. -/
abbrev wn (t : Tree L V) : Tree L V := .node .wn [t]
/-- `( t -> u )`. -/
abbrev wi (t u : Tree L V) : Tree L V := .node .wi [t, u]
/-- `A. x t`. -/
abbrev wal (v : V) (t : Tree L V) : Tree L V := .node .wal [t, .var v]
/-- `x = y` for set variables. -/
abbrev weq (v v' : V) : Tree L V := .node .wceq [.node .cv [.var v], .node .cv [.var v']]
/-- `x e. y` for set variables. -/
abbrev wel (v v' : V) : Tree L V := .node .wcel [.node .cv [.var v], .node .cv [.var v']]
/-- A formula variable. -/
abbrev wv (v : V) : Tree L V := .var v
/-- The floating hypothesis `wff v`. -/
abbrev fw (v : V) : THyp L C V := .float .wff v
/-- The floating hypothesis `setvar v`. -/
abbrev fs (v : V) : THyp L C V := .float .setvar v
/-- `|- t`. -/
abbrev pf (t : Tree L V) : TExpr L C V := ⟨.turnstile, t⟩

/-! ## The axioms of predicate calculus -/

open V

/-- `ax-mp`. -/
def axMp : TAssertion L C V :=
  ⟨[], [fw ph, fw ps, .ess (pf (wv ph)), .ess (pf (wi (wv ph) (wv ps)))], pf (wv ps)⟩
/-- `ax-1`. -/
def ax1 : TAssertion L C V := ⟨[], [fw ph, fw ps], pf (wi (wv ph) (wi (wv ps) (wv ph)))⟩
/-- `ax-2`. -/
def ax2 : TAssertion L C V := ⟨[], [fw ph, fw ps, fw ch],
  pf (wi (wi (wv ph) (wi (wv ps) (wv ch))) (wi (wi (wv ph) (wv ps)) (wi (wv ph) (wv ch))))⟩
/-- `ax-3`. -/
def ax3 : TAssertion L C V := ⟨[], [fw ph, fw ps],
  pf (wi (wi (wn (wv ph)) (wn (wv ps))) (wi (wv ps) (wv ph)))⟩
/-- `ax-gen`. -/
def axGen : TAssertion L C V := ⟨[], [fw ph, fs x, .ess (pf (wv ph))], pf (wal x (wv ph))⟩
/-- `ax-4`. -/
def ax4 : TAssertion L C V := ⟨[], [fw ph, fw ps, fs x],
  pf (wi (wal x (wi (wv ph) (wv ps))) (wi (wal x (wv ph)) (wal x (wv ps))))⟩
/-- `ax-5`, with `$d x ph`. -/
def ax5 : TAssertion L C V := ⟨[(x, ph)], [fw ph, fs x], pf (wi (wv ph) (wal x (wv ph)))⟩
/-- `ax-6`. -/
def ax6 : TAssertion L C V := ⟨[], [fs x, fs y], pf (wn (wal x (wn (weq x y))))⟩
/-- `ax-7`. -/
def ax7 : TAssertion L C V := ⟨[], [fs x, fs y, fs z],
  pf (wi (weq x y) (wi (weq x z) (weq y z)))⟩
/-- `ax-8`. -/
def ax8 : TAssertion L C V := ⟨[], [fs x, fs y, fs z],
  pf (wi (weq x y) (wi (wel x z) (wel y z)))⟩
/-- `ax-9`. -/
def ax9 : TAssertion L C V := ⟨[], [fs x, fs y, fs z],
  pf (wi (weq x y) (wi (wel z x) (wel z y)))⟩
/-- `ax-10`. -/
def ax10 : TAssertion L C V := ⟨[], [fw ph, fs x],
  pf (wi (wn (wal x (wv ph))) (wal x (wn (wal x (wv ph)))))⟩
/-- `ax-11`. -/
def ax11 : TAssertion L C V := ⟨[], [fw ph, fs x, fs y],
  pf (wi (wal x (wal y (wv ph))) (wal y (wal x (wv ph))))⟩
/-- `ax-12`. -/
def ax12 : TAssertion L C V := ⟨[], [fw ph, fs x, fs y],
  pf (wi (weq x y) (wi (wal y (wv ph)) (wal x (wi (weq x y) (wv ph)))))⟩
/-- `ax-13`. -/
def ax13 : TAssertion L C V := ⟨[], [fs x, fs y, fs z],
  pf (wi (wn (weq x y)) (wi (weq y z) (wal x (weq y z))))⟩

/-- The axioms and rules of set.mm's predicate calculus. -/
def predCalc : Set (TAssertion L C V) :=
  {axMp, ax1, ax2, ax3, axGen, ax4, ax5, ax6, ax7, ax8, ax9, ax10, ax11, ax12, ax13}

theorem wellFormed_predCalc : ∀ B ∈ predCalc, B.WellFormed grammar := by
  simp only [predCalc, Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro B (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl) <;> exact .of_checkWF (by decide)

/-! ## The environment model -/

variable (D : Type w) [Membership D D] (N : Type w) [DecidableEq N]

/-- The kinds of the typecodes: set variables are names, formulas are
formulas, classes are functions into `Set D`. -/
abbrev kind : C → Kind.{w}
  | .setvar => .name
  | .wff => .formula
  | .«class» => .term (Set D) ∅
  | _ => .term PUnit PUnit.unit

variable {D N}

/-- The class of members of `m`. -/
def cls (m : D) : Set D := {n | n ∈ m}

/-- `-. ph`. -/
abbrev opNot (φ : Term D N Prop) : Term D N Prop := φ.map Not
/-- `( ph -> ps )`. -/
abbrev opImp (φ ψ : Term D N Prop) : Term D N Prop := Term.map₂ (· → ·) φ ψ
/-- `( ph <-> ps )`. -/
abbrev opIff (φ ψ : Term D N Prop) : Term D N Prop := Term.map₂ Iff φ ψ
/-- `( ph /\ ps )`. -/
abbrev opAnd (φ ψ : Term D N Prop) : Term D N Prop := Term.map₂ And φ ψ
/-- `( ph \/ ps )`. -/
abbrev opOr (φ ψ : Term D N Prop) : Term D N Prop := Term.map₂ Or φ ψ
/-- `A. x ph`. -/
abbrev opAll (x : N) (φ : Term D N Prop) : Term D N Prop := φ.bind x fun P => ∀ m, P m
/-- `E. x ph`. -/
abbrev opEx (x : N) (φ : Term D N Prop) : Term D N Prop := φ.bind x fun P => ∃ m, P m
/-- `x` as a class. -/
abbrev opCv (x : N) : Term D N (Set D) := Term.name x cls
/-- `A = B`. -/
abbrev opEq (a b : Term D N (Set D)) : Term D N Prop := Term.map₂ (· = ·) a b
/-- `A e. B`. -/
abbrev opEl (a b : Term D N (Set D)) : Term D N Prop :=
  Term.map₂ (fun a b => ∃ m, a = cls m ∧ m ∈ b) a b
/-- `{ x | ph }`. -/
abbrev opAb (x : N) (φ : Term D N Prop) : Term D N (Set D) := φ.bind x fun P => {m | P m}

variable (D N)

/-- The standard environment model of set.mm's primitive grammar. -/
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
    | _, ⟨.cab, rfl⟩, a => opAb (a ⟨1, by decide⟩) (a ⟨0, by decide⟩)
  fresh_op {s t} a o args h := by
    obtain ⟨l, rfl⟩ := o
    refine Kind.fresh_of_ignores (by cases l <;> rfl) fun x hx => ?_
    have hj := fun j => (h j).of_name hx
    cases l with
    | wn => exact Term.notFree_map (hj ⟨0, by decide⟩).2
    | wi => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | wb => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | wa => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | wo => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | wal => exact Term.notFree_bind ((hj ⟨1, by decide⟩).1 _ rfl) (hj ⟨0, by decide⟩).2
    | wex => exact Term.notFree_bind ((hj ⟨1, by decide⟩).1 _ rfl) (hj ⟨0, by decide⟩).2
    | cv => exact Term.notFree_name ((hj ⟨0, by decide⟩).1 _ rfl)
    | wceq => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | wcel => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | cab => exact Term.notFree_bind ((hj ⟨1, by decide⟩).1 _ rfl) (hj ⟨0, by decide⟩).2
  IsTrue {_ s} _ a := match s, a with
    | .wff, (φ : Term D N Prop) => Valid φ.1
    | _, _ => False

variable [Infinite N]

/-- The standard environment model, as a model of the grammar. -/
abbrev model : Model grammar := (envModel D N).toModel

variable {D N}

/-! ## Computing values -/

section Values

variable {ctx : V → C → Prop} (ρ : (model D N).Valuation ctx)

/-- The sorting context of values. -/
local notation "HS" t:max s:max => grammar.HasSort (grammar.synCtx ctx) t s

theorem wn_0 {a : Tree L V} (h : HS (.node .wn [a]) .wff) : HS a .wff := h.child ⟨0, by decide⟩
theorem wi_0 {a b : Tree L V} (h : HS (.node .wi [a, b]) .wff) : HS a .wff := h.child ⟨0, by decide⟩
theorem wi_1 {a b : Tree L V} (h : HS (.node .wi [a, b]) .wff) : HS b .wff := h.child ⟨1, by decide⟩
theorem wal_0 {a b : Tree L V} (h : HS (.node .wal [a, b]) .wff) : HS a .wff :=
  h.child ⟨0, by decide⟩
theorem wal_1 {a b : Tree L V} (h : HS (.node .wal [a, b]) .wff) : HS b .setvar :=
  h.child ⟨1, by decide⟩
theorem cv_0 {a : Tree L V} (h : HS (.node .cv [a]) .class) : HS a .setvar :=
  h.child ⟨0, by decide⟩
theorem wceq_0 {a b : Tree L V} (h : HS (.node .wceq [a, b]) .wff) : HS a .class :=
  h.child ⟨0, by decide⟩
theorem wceq_1 {a b : Tree L V} (h : HS (.node .wceq [a, b]) .wff) : HS b .class :=
  h.child ⟨1, by decide⟩
theorem wcel_0 {a b : Tree L V} (h : HS (.node .wcel [a, b]) .wff) : HS a .class :=
  h.child ⟨0, by decide⟩
theorem wcel_1 {a b : Tree L V} (h : HS (.node .wcel [a, b]) .wff) : HS b .class :=
  h.child ⟨1, by decide⟩

theorem value_wn {a : Tree L V} (h : HS (.node .wn [a]) .wff) :
    (model D N).value ρ _ h =
      opNot (D := D) (N := N) ((model D N).value ρ a (wn_0 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wi {a b : Tree L V} (h : HS (.node .wi [a, b]) .wff) :
    (model D N).value ρ _ h =
      opImp (D := D) (N := N) ((model D N).value ρ a (wi_0 h))
        ((model D N).value ρ b (wi_1 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wal {a b : Tree L V} (h : HS (.node .wal [a, b]) .wff) :
    (model D N).value ρ _ h =
      opAll (D := D) (N := N) ((model D N).value ρ b (wal_1 h))
        ((model D N).value ρ a (wal_0 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_cv {a : Tree L V} (h : HS (.node .cv [a]) .class) :
    (model D N).value ρ _ h =
      opCv (D := D) (N := N) ((model D N).value ρ a (cv_0 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wceq {a b : Tree L V} (h : HS (.node .wceq [a, b]) .wff) :
    (model D N).value ρ _ h =
      opEq (D := D) (N := N) ((model D N).value ρ a (wceq_0 h))
        ((model D N).value ρ b (wceq_1 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem value_wcel {a b : Tree L V} (h : HS (.node .wcel [a, b]) .wff) :
    (model D N).value ρ _ h =
      opEl (D := D) (N := N) ((model D N).value ρ a (wcel_0 h))
        ((model D N).value ρ b (wcel_1 h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

end Values

theorem holds_iff {ctx : V → C → Prop} (ρ : (model D N).Valuation ctx) (t : Tree L V) :
    (model D N).Holds ρ (pf t) ↔ ∃ h : grammar.HasSort (grammar.synCtx ctx) t .wff,
      Valid ((model D N).value ρ t h : Term D N Prop).1 := by
  constructor
  · rintro ⟨s, hs, ht, htrue⟩
    obtain rfl : .wff = s := Option.some.inj hs
    exact ⟨ht, htrue⟩
  · rintro ⟨ht, htrue⟩
    exact ⟨.wff, rfl, ht, htrue⟩

theorem cls_inj (hext : ∀ a b : D, (∀ m, m ∈ a ↔ m ∈ b) → a = b) {a b : D} :
    cls a = cls b ↔ a = b :=
  ⟨fun h => hext a b fun m => Set.ext_iff.1 h m, fun h => h ▸ rfl⟩

theorem exists_cls_mem (hext : ∀ a b : D, (∀ m, m ∈ a ↔ m ∈ b) → a = b) {a b : D} :
    (∃ m, cls a = cls m ∧ m ∈ cls b) ↔ a ∈ b :=
  ⟨fun ⟨_, h, hm⟩ => (cls_inj hext).1 h ▸ hm, fun h => ⟨a, rfl, h⟩⟩

/-- A well-formed assertion at `|-` holds when the value of its conclusion is
valid under every valuation satisfying its hypotheses. -/
theorem satisfies_of_valid {A : TAssertion L C V} {t : Tree L V} (hA : A.WellFormed grammar)
    (hc : A.concl = pf t)
    (h : ∀ ρ : (model D N).Valuation A.ctx, (model D N).DVHolds ρ A.dv →
      (∀ e ∈ A.essentials, (model D N).Holds ρ e) →
      ∀ ht : grammar.HasSort (grammar.synCtx A.ctx) t .wff,
        Valid ((model D N).value ρ t ht : Term D N Prop).1) :
    (model D N).Satisfies A := by
  intro ρ hdv hess
  obtain ⟨s, hs, ht⟩ := hA.concl_wellTyped
  rw [hc] at hs ht ⊢
  obtain rfl : .wff = s := Option.some.inj hs
  exact (holds_iff ρ _).2 ⟨ht.synCtx rfl, h ρ hdv hess _⟩

theorem sat_ax1 : (model D N).Satisfies ax1 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, Model.value_var]
  exact PredicateCalculus.valid_ax1 _ _

/-! ## Validity of the axioms -/

variable (D) in
/-- The membership relation of `D` is extensional. -/
def Extensional : Prop := ∀ a b : D, (∀ m, m ∈ a ↔ m ∈ b) → a = b

/-- Equality of names as a term: `x = y`. -/
abbrev termEq (a b : N) : Term D N Prop := Term.map₂ (· = ·) (Term.name a id) (Term.name b id)

/-- Membership of names as a term: `x e. y`. -/
abbrev termMem (a b : N) : Term D N Prop := Term.map₂ (· ∈ ·) (Term.name a id) (Term.name b id)

omit [Infinite N] in
/-- For set variables, class equality is equality. -/
theorem opEq_cv (hext : Extensional D) (a b : N) : opEq (opCv (D := D) a) (opCv b) = termEq a b :=
  Subtype.ext (funext fun _ => propext (cls_inj hext))

omit [Infinite N] in
/-- For set variables, class membership is membership. -/
theorem opEl_cv (hext : Extensional D) (a b : N) : opEl (opCv (D := D) a) (opCv b) = termMem a b :=
  Subtype.ext (funext fun _ => propext (exists_cls_mem hext))

open PredicateCalculus

section Axioms

theorem sat_ax2 : (model D N).Satisfies ax2 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, Model.value_var]
  exact valid_ax2 _ _ _

theorem sat_ax3 : (model D N).Satisfies ax3 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wn, Model.value_var]
  exact valid_ax3 _ _

theorem sat_axMp : (model D N).Satisfies axMp := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl
    fun ρ _ hess ht => ?_
  obtain ⟨h₁, v₁⟩ := (holds_iff ρ _).1 (hess (pf (wv ph)) (by simp [axMp, essentials]))
  obtain ⟨h₂, v₂⟩ := (holds_iff ρ _).1
    (hess (pf (wi (wv ph) (wv ps))) (by simp [axMp, essentials]))
  simp only [value_wi, Model.value_var] at v₁ v₂ ⊢
  exact valid_mp v₁ v₂

theorem sat_axGen : (model D N).Satisfies axGen := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl
    fun ρ _ hess ht => ?_
  obtain ⟨h₁, v₁⟩ := (holds_iff ρ _).1 (hess (pf (wv ph)) (by simp [axGen, essentials]))
  simp only [value_wal, Model.value_var] at v₁ ⊢
  exact valid_gen _ v₁

theorem sat_ax4 : (model D N).Satisfies ax4 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wal, Model.value_var]
  exact valid_ax4 _ _ _

theorem sat_ax5 : (model D N).Satisfies ax5 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl
    fun ρ hdv _ ht => ?_
  simp only [value_wi, value_wal, Model.value_var]
  refine valid_ax5 (notFree_iff.1 (Kind.fresh_name_formula.1 ?_))
  exact hdv x ph (by simp [ax5]) (by decide) .setvar .wff _ _

theorem sat_ax6 (hext : Extensional D) : (model D N).Satisfies ax6 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wn, value_wal, value_wceq, value_cv, Model.value_var, opEq_cv (N := N) hext]
  exact valid_ax6 _ _

theorem sat_ax7 (hext : Extensional D) : (model D N).Satisfies ax7 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wceq, value_cv, Model.value_var, opEq_cv (N := N) hext]
  exact valid_ax7 _ _ _

theorem sat_ax8 (hext : Extensional D) : (model D N).Satisfies ax8 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wceq, value_wcel, value_cv, Model.value_var, opEq_cv (N := N) hext,
    opEl_cv (N := N) hext]
  exact valid_ax8 _ _ _

theorem sat_ax9 (hext : Extensional D) : (model D N).Satisfies ax9 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wceq, value_wcel, value_cv, Model.value_var, opEq_cv (N := N) hext,
    opEl_cv (N := N) hext]
  exact valid_ax9 _ _ _

theorem sat_ax10 : (model D N).Satisfies ax10 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wn, value_wal, Model.value_var]
  exact valid_ax10 _ _

theorem sat_ax11 : (model D N).Satisfies ax11 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wal, Model.value_var]
  exact valid_ax11 _ _ _

theorem sat_ax12 (hext : Extensional D) : (model D N).Satisfies ax12 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wal, value_wceq, value_cv, Model.value_var, opEq_cv (N := N) hext]
  exact valid_ax12 _ _ _

theorem sat_ax13 (hext : Extensional D) : (model D N).Satisfies ax13 := by
  refine satisfies_of_valid (wellFormed_predCalc _ (by simp [predCalc])) rfl fun ρ _ _ ht => ?_
  simp only [value_wi, value_wn, value_wal, value_wceq, value_cv, Model.value_var,
    opEq_cv (N := N) hext]
  exact valid_ax13 _ _ _

/-- Every environment model over an extensional membership structure is a
model of set.mm's predicate calculus. -/
theorem isModel_predCalc (hext : Extensional D) : (model D N).IsModel predCalc := by
  rintro B (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl)
  exacts [sat_axMp, sat_ax1, sat_ax2, sat_ax3, sat_axGen, sat_ax4, sat_ax5, sat_ax6 hext,
    sat_ax7 hext, sat_ax8 hext, sat_ax9 hext, sat_ax10, sat_ax11, sat_ax12 hext, sat_ax13 hext]

/-- Over a nonempty domain the model is not trivial: the constantly false
formula is not valid. -/
theorem not_trivialAt [Nonempty D] :
    ¬ (model D N).TrivialAt (c := .turnstile) (s := .wff) rfl := fun h => by
  obtain ⟨d⟩ := ‹Nonempty D›
  exact h (Term.const False) fun _ => d

/-- Every tree theorem of the predicate calculus is true in every environment
model over an extensional membership structure. -/
theorem sound_predCalc (hext : Extensional D) {A : TAssertion L C V}
    (h : TDerivable grammar predCalc A) : (model D N).Satisfies A :=
  (model D N).sound wellFormed_predCalc (isModel_predCalc hext) h

end Axioms

/-- The predicate calculus of set.mm is consistent: it does not prove `|- ph`,
as the environment model over `ZFSet` shows. -/
theorem not_tderivable_falsum :
    ¬ TDerivable grammar predCalc (falsum .turnstile .wff ph) :=
  Model.not_tderivable_falsum (M := model ZFSet.{0} (ULift.{1} ℕ)) wellFormed_predCalc
    (isModel_predCalc fun _ _ => ZFSet.ext) rfl not_trivialAt ph

theorem tConsistent_predCalc : TConsistent grammar predCalc .turnstile :=
  tConsistent_of_not_falsum rfl not_tderivable_falsum

/-- The string system of set.mm's predicate calculus is consistent. -/
theorem nonUniversal_predCalc : (system (grammar.axioms predCalc)).NonUniversal :=
  Model.nonUniversal_system (M := model ZFSet.{0} (ULift.{1} ℕ)) unambiguous wellFormed_predCalc
    (isModel_predCalc fun _ _ => ZFSet.ext) rfl not_trivialAt ph

end Silmaril.Logic.Metamath.Model.SetMM

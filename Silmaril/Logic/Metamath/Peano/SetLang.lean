module

public import Silmaril.Logic.Metamath.Model.PredCalc
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# The language of set.mm's ZFC with infinitely many variables

The ZFC fragment of set.mm uses the syntax axioms `wn`,
`wi`, `wb`, `wa`, `wo`, `wal`, `wex`, `cv`, `wceq` and `wcel`. This is their
grammar (`Peano.ZF.grammar`) over infinitely many variables
(`Peano.ZF.V`): the metavariables `ph ps ch`, `x y z w v u t`, `A B` of
set.mm's statements, and further variables `var n` for translations that need
unboundedly many bound variables. The grammar is unambiguous by an LL
certificate.

Its standard environment model over a membership structure `D`
(`Peano.ZF.model`) is that of `Silmaril.Logic.Metamath.Model.PredCalc`:
set variables denote names, formulas finitely supported formulas and classes
finitely supported functions into `Set D`.

A pure formula is a formula tree all of whose variables are set variables
(`Peano.ZF.IsPure`). Over an extensional membership structure its value is
given by the usual Tarski semantics of first-order set theory
(`Peano.ZF.value_pure`, `Peano.ZF.sem`), reading variables through the names
of the valuation.
-/

namespace Silmaril.Logic.Metamath.Peano.ZF

open Silmaril.Logic.Metamath Grammar Grammar.TAssertion Silmaril.Logic.SetTheory Function Env
open Silmaril.Logic.Metamath.Model.SetMM (opNot opImp opIff opAnd opOr opAll opEx opCv opEq opEl
  termEq termMem opEq_cv opEl_cv Extensional)

/-- Typecodes and constants of set.mm. -/
abbrev C := Grammar.Examples.SetMM.C

/-- The syntax axioms of set.mm's ZFC. -/
inductive L
  | wn | wi | wb | wa | wo | wal | wex | cv | wceq | wcel
  deriving DecidableEq, Repr

instance : Fintype L :=
  .ofList [.wn, .wi, .wb, .wa, .wo, .wal, .wex, .cv, .wceq, .wcel] (by intro l; cases l <;> simp)

/-- Variables: set.mm's `ph ps ch`, `x y z w v u t`, `A B`, and `var n`. -/
inductive V
  | ph | ps | ch | x | y | z | w | v | u | t | A | B
  | var (n : ℕ)
  deriving DecidableEq, Repr

instance : Infinite V := Infinite.of_injective V.var fun _ _ h => V.var.inj h

open Grammar.Examples.SetMM.C Grammar.Examples in
/-- The syntax rules, with floating hypotheses in database order. -/
def rules : L → SyntaxRule C V
  | .wn => rule wff [(wff, .ph)] [.const not, .var .ph]
  | .wi => rule wff [(wff, .ph), (wff, .ps)] [.const lp, .var .ph, .const imp, .var .ps, .const rp]
  | .wb => rule wff [(wff, .ph), (wff, .ps)] [.const lp, .var .ph, .const bi, .var .ps, .const rp]
  | .wa => rule wff [(wff, .ph), (wff, .ps)] [.const lp, .var .ph, .const and, .var .ps, .const rp]
  | .wo => rule wff [(wff, .ph), (wff, .ps)] [.const lp, .var .ph, .const or, .var .ps, .const rp]
  | .wal => rule wff [(wff, .ph), (setvar, .x)] [.const all, .var .x, .var .ph]
  | .wex => rule wff [(wff, .ph), (setvar, .x)] [.const ex, .var .x, .var .ph]
  | .cv => rule «class» [(setvar, .x)] [.var .x]
  | .wceq => rule wff [(«class», .A), («class», .B)] [.var .A, .const eq, .var .B]
  | .wcel => rule wff [(«class», .A), («class», .B)] [.var .A, .const el, .var .B]

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

theorem llCert : LLCert grammar Grammar.Examples.SetMM.first := by decide

theorem unambiguous : grammar.Unambiguous := llCert.unambiguous

/-! ## Tree notation -/

namespace T

/-- `-. a`. -/
abbrev wn (a : Tree L V) : Tree L V := .node .wn [a]
/-- `( a -> b )`. -/
abbrev wi (a b : Tree L V) : Tree L V := .node .wi [a, b]
/-- `( a <-> b )`. -/
abbrev wb (a b : Tree L V) : Tree L V := .node .wb [a, b]
/-- `( a /\ b )`. -/
abbrev wa (a b : Tree L V) : Tree L V := .node .wa [a, b]
/-- `( a \/ b )`. -/
abbrev wo (a b : Tree L V) : Tree L V := .node .wo [a, b]
/-- `A. c a`. -/
abbrev wal (c : V) (a : Tree L V) : Tree L V := .node .wal [a, .var c]
/-- `E. c a`. -/
abbrev wex (c : V) (a : Tree L V) : Tree L V := .node .wex [a, .var c]
/-- `c = d` for set variables. -/
abbrev weq (c d : V) : Tree L V := .node .wceq [.node .cv [.var c], .node .cv [.var d]]
/-- `c e. d` for set variables. -/
abbrev wel (c d : V) : Tree L V := .node .wcel [.node .cv [.var c], .node .cv [.var d]]
/-- A formula metavariable. -/
abbrev mv (c : V) : Tree L V := .var c
/-- `|- a`. -/
abbrev pf (a : Tree L V) : TExpr L C V := ⟨.turnstile, a⟩

end T

/-! ## The environment model -/

variable (D : Type 1) [Membership D D] (N : Type 1) [DecidableEq N]

/-- The kinds of the typecodes: set variables are names, formulas are
formulas, classes are functions into `Set D`. -/
abbrev kind : C → Kind.{1}
  | .setvar => .name
  | .wff => .formula
  | .«class» => .term (Set D) ∅
  | _ => .term PUnit PUnit.unit

/-- The standard environment model of set.mm's ZFC language. -/
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

theorem value_wn {a : Tree L V} (h : HS (.node .wn [a]) .wff) :
    (model D N).value ρ _ h =
      opNot (D := D) (N := N)
        ((model D N).value ρ a (show HS a .wff from h.child ⟨0, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_wi {a b : Tree L V} (h : HS (.node .wi [a, b]) .wff) :
    (model D N).value ρ _ h =
      opImp (D := D) (N := N) ((model D N).value ρ a (show HS a .wff from h.child ⟨0, by decide⟩))
        ((model D N).value ρ b (show HS b .wff from h.child ⟨1, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_wb {a b : Tree L V} (h : HS (.node .wb [a, b]) .wff) :
    (model D N).value ρ _ h =
      opIff (D := D) (N := N) ((model D N).value ρ a (show HS a .wff from h.child ⟨0, by decide⟩))
        ((model D N).value ρ b (show HS b .wff from h.child ⟨1, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_wa {a b : Tree L V} (h : HS (.node .wa [a, b]) .wff) :
    (model D N).value ρ _ h =
      opAnd (D := D) (N := N) ((model D N).value ρ a (show HS a .wff from h.child ⟨0, by decide⟩))
        ((model D N).value ρ b (show HS b .wff from h.child ⟨1, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_wo {a b : Tree L V} (h : HS (.node .wo [a, b]) .wff) :
    (model D N).value ρ _ h =
      opOr (D := D) (N := N) ((model D N).value ρ a (show HS a .wff from h.child ⟨0, by decide⟩))
        ((model D N).value ρ b (show HS b .wff from h.child ⟨1, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_wal {a b : Tree L V} (h : HS (.node .wal [a, b]) .wff) :
    (model D N).value ρ _ h =
      opAll (D := D) (N := N)
        ((model D N).value ρ b (show HS b .setvar from h.child ⟨1, by decide⟩))
        ((model D N).value ρ a (show HS a .wff from h.child ⟨0, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_wex {a b : Tree L V} (h : HS (.node .wex [a, b]) .wff) :
    (model D N).value ρ _ h =
      opEx (D := D) (N := N)
        ((model D N).value ρ b (show HS b .setvar from h.child ⟨1, by decide⟩))
        ((model D N).value ρ a (show HS a .wff from h.child ⟨0, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_cv {a : Tree L V} (h : HS (.node .cv [a]) .class) :
    (model D N).value ρ _ h =
      opCv (D := D) (N := N)
        ((model D N).value ρ a (show HS a .setvar from h.child ⟨0, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_wceq {a b : Tree L V} (h : HS (.node .wceq [a, b]) .wff) :
    (model D N).value ρ _ h =
      opEq (D := D) (N := N) ((model D N).value ρ a (show HS a .class from h.child ⟨0, by decide⟩))
        ((model D N).value ρ b (show HS b .class from h.child ⟨1, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

theorem value_wcel {a b : Tree L V} (h : HS (.node .wcel [a, b]) .wff) :
    (model D N).value ρ _ h =
      opEl (D := D) (N := N) ((model D N).value ρ a (show HS a .class from h.child ⟨0, by decide⟩))
        ((model D N).value ρ b (show HS b .class from h.child ⟨1, by decide⟩)) := by
  unfold Model.value; rw [eval_node]; rfl

end Values

theorem holds_iff {ctx : V → C → Prop} (ρ : (model D N).Valuation ctx) (t : Tree L V) :
    (model D N).Holds ρ (T.pf t) ↔ ∃ h : grammar.HasSort (grammar.synCtx ctx) t .wff,
      Valid ((model D N).value ρ t h : Term D N Prop).1 := by
  constructor
  · rintro ⟨s, hs, ht, htrue⟩
    obtain rfl : .wff = s := Option.some.inj hs
    exact ⟨ht, htrue⟩
  · rintro ⟨ht, htrue⟩
    exact ⟨.wff, rfl, ht, htrue⟩

/-- A well-formed assertion at `|-` holds when the value of its conclusion is
valid under every valuation satisfying its hypotheses. -/
theorem satisfies_of_valid {A : TAssertion L C V} {t : Tree L V} (hA : A.WellFormed grammar)
    (hc : A.concl = T.pf t)
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

/-! ## Pure formulas and their Tarski semantics -/

/-- The context in which every variable is a set variable. -/
def setCtx (_ : V) (c : C) : Prop := c = .setvar

/-- A pure formula: a formula tree whose variables are set variables. -/
def IsPure (t : Tree L V) : Prop := grammar.HasSort setCtx t .wff

/-- The Tarski semantics of a formula of set theory in a membership structure,
reading each variable `c` as the name `nm c` of an environment `E`. -/
def sem {D' N' : Type*} [Membership D' D'] [DecidableEq N'] (nm : V → N') :
    Tree L V → (N' → D') → Prop
  | .node .wn [a], E => ¬ sem nm a E
  | .node .wi [a, b], E => sem nm a E → sem nm b E
  | .node .wb [a, b], E => (sem nm a E ↔ sem nm b E)
  | .node .wa [a, b], E => sem nm a E ∧ sem nm b E
  | .node .wo [a, b], E => sem nm a E ∨ sem nm b E
  | .node .wal [a, .var c], E => ∀ m, sem nm a (update E (nm c) m)
  | .node .wex [a, .var c], E => ∃ m, sem nm a (update E (nm c) m)
  | .node .wceq [.node .cv [.var c], .node .cv [.var d]], E => E (nm c) = E (nm d)
  | .node .wcel [.node .cv [.var c], .node .cv [.var d]], E => E (nm c) ∈ E (nm d)
  | _, _ => False

section Sem

variable {D' N' : Type*} [Membership D' D'] [DecidableEq N'] (nm : V → N') (E : N' → D')

@[simp] theorem sem_wn (a : Tree L V) : sem nm (T.wn a) E ↔ ¬ sem nm a E := Iff.rfl
@[simp] theorem sem_wi (a b : Tree L V) : sem nm (T.wi a b) E ↔ (sem nm a E → sem nm b E) :=
  Iff.rfl
@[simp] theorem sem_wb (a b : Tree L V) : sem nm (T.wb a b) E ↔ (sem nm a E ↔ sem nm b E) :=
  Iff.rfl
@[simp] theorem sem_wa (a b : Tree L V) : sem nm (T.wa a b) E ↔ sem nm a E ∧ sem nm b E :=
  Iff.rfl
@[simp] theorem sem_wo (a b : Tree L V) : sem nm (T.wo a b) E ↔ sem nm a E ∨ sem nm b E :=
  Iff.rfl
@[simp] theorem sem_wal (c : V) (a : Tree L V) :
    sem nm (T.wal c a) E ↔ ∀ m, sem nm a (update E (nm c) m) := Iff.rfl
@[simp] theorem sem_wex (c : V) (a : Tree L V) :
    sem nm (T.wex c a) E ↔ ∃ m, sem nm a (update E (nm c) m) := Iff.rfl
@[simp] theorem sem_weq (c d : V) : sem nm (T.weq c d) E ↔ E (nm c) = E (nm d) := Iff.rfl
@[simp] theorem sem_wel (c d : V) : sem nm (T.wel c d) E ↔ E (nm c) ∈ E (nm d) := Iff.rfl

end Sem

theorem hasSort_setCtx_setvar {t : Tree L V} (h : grammar.HasSort setCtx t .setvar) :
    ∃ c, t = .var c := by
  generalize hs : (.setvar : C) = s at h
  cases h with
  | var => exact ⟨_, rfl⟩
  | node => rename_i l _ _ _; cases l <;> exact absurd hs (by decide)

theorem hasSort_setCtx_class {t : Tree L V} (h : grammar.HasSort setCtx t .class) :
    ∃ c, t = .node .cv [.var c] := by
  generalize hs : (.class : C) = s at h
  cases h with
  | var hv => cases hs; cases hv
  | node hlen hargs =>
    rename_i l args
    cases l <;> first | exact absurd hs (by decide) | skip
    obtain ⟨a, rfl⟩ : ∃ a, args = [a] := match args, hlen with | [a], _ => ⟨a, rfl⟩
    obtain ⟨c, rfl⟩ := hasSort_setCtx_setvar (hargs (a, (.setvar, .x)) (by simp [grammar, rules]))
    exact ⟨c, rfl⟩

/-- The shapes of pure formulas. -/
theorem IsPure.cases {t : Tree L V} (h : IsPure t) :
    (∃ a, t = T.wn a ∧ IsPure a) ∨
      (∃ l a b, t = .node l [a, b] ∧ (l = .wi ∨ l = .wb ∨ l = .wa ∨ l = .wo) ∧
        IsPure a ∧ IsPure b) ∨
      (∃ l a c, t = .node l [a, .var c] ∧ (l = .wal ∨ l = .wex) ∧ IsPure a) ∨
      (∃ l c d, t = .node l [.node .cv [.var c], .node .cv [.var d]] ∧
        (l = .wceq ∨ l = .wcel)) := by
  unfold IsPure at h
  generalize hs : (.wff : C) = s at h
  cases h with
  | var hv => cases hs; cases hv
  | node hlen hargs =>
    rename_i l args
    have two : ∀ l', l = l' → (grammar.rule l).arity = 2 → ∃ a b, args = [a, b] := by
      intro l' _ h2
      match args, hlen.trans h2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    cases l <;> first | exact absurd hs (by decide) | skip
    · obtain ⟨a, rfl⟩ : ∃ a, args = [a] := match args, hlen with | [a], _ => ⟨a, rfl⟩
      exact .inl ⟨a, rfl, hargs (a, (.wff, .ph)) (by simp [grammar, rules])⟩
    all_goals obtain ⟨a, b, rfl⟩ := two _ rfl rfl
    all_goals have ha := hargs (a, _) (List.mem_cons_self ..)
    all_goals have hb := hargs (b, _) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact .inr (.inl ⟨_, a, b, rfl, .inl rfl, ha, hb⟩)
    · exact .inr (.inl ⟨_, a, b, rfl, .inr (.inl rfl), ha, hb⟩)
    · exact .inr (.inl ⟨_, a, b, rfl, .inr (.inr (.inl rfl)), ha, hb⟩)
    · exact .inr (.inl ⟨_, a, b, rfl, .inr (.inr (.inr rfl)), ha, hb⟩)
    · obtain ⟨c, rfl⟩ := hasSort_setCtx_setvar hb
      exact .inr (.inr (.inl ⟨_, a, c, rfl, .inl rfl, ha⟩))
    · obtain ⟨c, rfl⟩ := hasSort_setCtx_setvar hb
      exact .inr (.inr (.inl ⟨_, a, c, rfl, .inr rfl, ha⟩))
    · obtain ⟨c, rfl⟩ := hasSort_setCtx_class ha
      obtain ⟨d, rfl⟩ := hasSort_setCtx_class hb
      exact .inr (.inr (.inr ⟨_, c, d, rfl, .inl rfl⟩))
    · obtain ⟨c, rfl⟩ := hasSort_setCtx_class ha
      obtain ⟨d, rfl⟩ := hasSort_setCtx_class hb
      exact .inr (.inr (.inr ⟨_, c, d, rfl, .inr rfl⟩))

section Pure

variable {ctx : V → C → Prop} (ρ : (model D N).Valuation ctx) (nm : V → N)
  (hnm : ∀ a h, ρ a .setvar h = nm a)

include hnm

/-- Over an extensional membership structure, the value of a pure formula is
its Tarski semantics. -/
theorem value_pure (hext : Extensional D) : ∀ (t : Tree L V), IsPure t →
    ∀ (h : grammar.HasSort (grammar.synCtx ctx) t .wff) (E : SetTheory.Env D N),
      ((model D N).value ρ t h : Term D N Prop).1 E ↔ sem nm t E := by
  intro t
  induction t using Tree.induction with
  | var a => intro ht; cases ht with | var hv => cases hv
  | node l args ih =>
    intro ht h E
    rcases ht.cases with ⟨a, e, ha⟩ | ⟨l', a, b, e, hl, ha, hb⟩ | ⟨l', a, c, e, hl, ha⟩ |
      ⟨l', c, d, e, hl⟩ <;> cases e
    · rw [value_wn]
      exact not_congr (ih a (by simp) ha _ E)
    · have iha := fun h' => ih a (by simp) ha h'
      have ihb := fun h' => ih b (by simp) hb h'
      rcases hl with rfl | rfl | rfl | rfl
      · rw [value_wi]; exact imp_congr (iha _ E) (ihb _ E)
      · rw [value_wb]; exact iff_congr (iha _ E) (ihb _ E)
      · rw [value_wa]; exact and_congr (iha _ E) (ihb _ E)
      · rw [value_wo]; exact or_congr (iha _ E) (ihb _ E)
    · rcases hl with rfl | rfl
      · rw [value_wal, Model.value_var, hnm]
        exact forall_congr' fun m => ih a (by simp) ha _ _
      · rw [value_wex, Model.value_var, hnm]
        exact exists_congr fun m => ih a (by simp) ha _ _
    · rcases hl with rfl | rfl
      · rw [value_wceq, value_cv, value_cv, Model.value_var, Model.value_var, hnm, hnm,
          opEq_cv hext]
        rfl
      · rw [value_wcel, value_cv, value_cv, Model.value_var, Model.value_var, hnm, hnm,
          opEl_cv hext]
        rfl

end Pure

end Silmaril.Logic.Metamath.Peano.ZF

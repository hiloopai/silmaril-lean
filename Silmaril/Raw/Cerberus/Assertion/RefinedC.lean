module

public import Silmaril.Cerberus.Assertion.Resources.Defs
public import Mathlib.Data.List.Forall2

/-!
A small semantic target for RefinedC integer annotations, inspired by the project's
`n @ int<i32>` singleton refinements and `&own<...>` owned types:
https://plv.mpi-sws.org/refinedc/ and its linked paper (Figure 1, Section 2).

This module interprets explicit mathematical integer refinements, representability,
pure requirements/ensures, and exclusive abstract integer cells. It does not interpret
RefinedC's Iris typing judgment, Lithium proof search, struct layouts, pointer provenance,
optional types or dependent ownership. In particular, the abstract cell theorem below
is not an adequacy theorem for RefinedC's concrete pointer semantics. Ghost parameters
are supplied by an explicit environment; their surface Rocq syntax is not interpreted.
-/

@[expose] public section
namespace Silmaril.Cerberus.Assertion.RefinedC

open Silmaril.Cerberus.Assertion.Pure

inductive IntegerType where
  | i8 | i16 | i32 | i64 | u8 | u16 | u32 | u64
  deriving Repr, DecidableEq

def IntegerType.bits : IntegerType → Nat
  | .i8 | .u8 => 8
  | .i16 | .u16 => 16
  | .i32 | .u32 => 32
  | .i64 | .u64 => 64

def IntegerType.signed : IntegerType → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | .u8 | .u16 | .u32 | .u64 => false

def IntegerType.lower (t : IntegerType) : Int :=
  if t.signed then -(2 ^ (t.bits - 1)) else 0

def IntegerType.upper (t : IntegerType) : Int :=
  if t.signed then 2 ^ (t.bits - 1) else 2 ^ t.bits

/-- Representability excludes mathematical refinements outside the machine type. -/
def IntegerType.admits (t : IntegerType) (n : Int) : Prop :=
  t.lower ≤ n ∧ n < t.upper

def IntegerType.toFormula (t : IntegerType) (actual : Term) : Pure.Formula :=
  .and (.le (.literal t.lower) actual) (.lt actual (.literal t.upper))

theorem IntegerType.toFormula_correct (ρ : Env) (t : IntegerType) (actual : Term) :
    (t.toFormula actual).holds ρ ↔ t.admits (actual.eval ρ) := Iff.rfl

/-- `none` is the unrefined integer type; `some n` is the singleton `n @ int<t>`. -/
structure IntRefinement where
  kind : IntegerType
  value : Option Term
  deriving Repr, DecidableEq

def IntRefinement.holds (ρ : Env) (r : IntRefinement) (actual : Int) : Prop :=
  r.kind.admits actual ∧ match r.value with
    | none => True
    | some expected => actual = expected.eval ρ

def IntRefinement.toFormula (r : IntRefinement) (actual : Term) : Pure.Formula :=
  .and (r.kind.toFormula actual) (match r.value with
    | none => .truth
    | some expected => .eq actual expected)

theorem IntRefinement.toFormula_correct (ρ : Env) (r : IntRefinement) (actual : Term) :
    (r.toFormula actual).holds ρ ↔ r.holds ρ (actual.eval ρ) := by
  cases r with
  | mk kind value => cases value <;> rfl

/-- The executable pure-assertion goal is equivalent to integer refinement typing. -/
theorem IntRefinement.leanGoal_correct (ρ : Env) (r : IntRefinement) (actual : Term) :
    (r.toFormula actual).leanGoal ρ ↔ r.holds ρ (actual.eval ρ) :=
  (Pure.Formula.leanGoal_correct _ _).trans (r.toFormula_correct ρ actual)

/-- Explicit metadata and elaborated integer refinements from one annotation block.
`parameters` records ghost binders; the caller supplies their valuation in `Env`.
Arguments are positional, while terms in requirements and ensures use that supplied
valuation. Connecting source names and runtime stores remains an explicit obligation. -/
structure Contract where
  parameters : List String
  args : List IntRefinement
  returns : IntRefinement
  requires : Pure.Formula
  ensures : Pure.Formula
  deriving Repr, DecidableEq

def ArgRefinements (ρ : Env) (types : List IntRefinement) (values : List Int) : Prop :=
  List.Forall₂ (fun r n => r.holds ρ n) types values

def ArgGoals (ρ : Env) (types : List IntRefinement) (values : List Int) : Prop :=
  List.Forall₂ (fun r n => (r.toFormula (.literal n)).leanGoal ρ) types values

theorem argGoals_correct (ρ : Env) (types : List IntRefinement) (values : List Int) :
    ArgGoals ρ types values ↔ ArgRefinements ρ types values := by
  induction types generalizing values with
  | nil => cases values <;> simp [ArgGoals, ArgRefinements]
  | cons r rs ih =>
    cases values <;> simp [ArgGoals, ArgRefinements, List.forall₂_cons,
      IntRefinement.leanGoal_correct, Term.eval]

def Contract.pre (ρ : Env) (c : Contract) (args : List Int) : Prop :=
  ArgRefinements ρ c.args args ∧ c.requires.holds ρ

def Contract.post (ρ : Env) (c : Contract) (result : Int) : Prop :=
  c.returns.holds ρ result ∧ c.ensures.holds ρ

/-- A certificate proves this conditional for every relevant initial/final valuation;
this pointwise formulation leaves execution and source-name readback explicit. -/
def Contract.obligation (before after : Env) (c : Contract)
    (args : List Int) (result : Int) : Prop :=
  c.pre before args → c.post after result

def Contract.leanGoal (before after : Env) (c : Contract)
    (args : List Int) (result : Int) : Prop :=
  (ArgGoals before c.args args ∧ c.requires.leanGoal before) →
    (c.returns.toFormula (.literal result)).leanGoal after ∧ c.ensures.leanGoal after

theorem Contract.leanGoal_correct (before after : Env) (c : Contract)
    (args : List Int) (result : Int) :
    c.leanGoal before after args result ↔ c.obligation before after args result := by
  simp only [leanGoal, obligation, pre, post, argGoals_correct,
    Pure.Formula.leanGoal_correct, IntRefinement.toFormula_correct, Term.eval]

/-- An abstract owned singleton refinement: the value is representable and the
entire cell at `address` is owned. Pure facts consume the empty heap. -/
def IntRefinement.owned (r : IntRefinement) (address : Nat) (actual : Term) :
    Resources.Formula :=
  .sep (.pure (r.toFormula actual)) (.pointsTo address actual)

theorem IntRefinement.owned_correct (ρ : Env) (r : IntRefinement)
    (address : Nat) (actual : Term) (h : Resources.Heap) :
    (r.owned address actual).holds ρ h ↔
      r.holds ρ (actual.eval ρ) ∧ h = [(address, actual.eval ρ)] := by
  constructor
  · rintro ⟨h₁, h₂, _, hp, ⟨he, hr⟩, hc⟩
    subst h₁
    change h₂ = [(address, actual.eval ρ)] at hc
    subst h₂
    exact ⟨(r.toFormula_correct ρ actual).mp hr, hp.eq_singleton⟩
  · rintro ⟨hr, rfl⟩
    refine ⟨[], [(address, actual.eval ρ)], ?_, .refl _, ?_, rfl⟩
    · intro a x y hx
      cases hx
    · exact ⟨rfl, (r.toFormula_correct ρ actual).mpr hr⟩

theorem IntRefinement.ownedGoal_correct (ρ : Env) (r : IntRefinement)
    (address : Nat) (actual : Term) (h : Resources.Heap) :
    (r.owned address actual).leanGoal ρ h ↔
      r.holds ρ (actual.eval ρ) ∧ h = [(address, actual.eval ρ)] :=
  (Resources.Formula.leanGoal_correct _ _ _).trans
    (r.owned_correct ρ address actual h)

end Silmaril.Cerberus.Assertion.RefinedC

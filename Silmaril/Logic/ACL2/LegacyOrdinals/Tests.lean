module

import Silmaril.Logic.ACL2.LegacyOrdinals.Thms
import Silmaril.Logic.ACL2.OrdinalAdmission.Thms
meta import Silmaril.Logic.ACL2.OrdinalAdmission.Thms
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith

namespace Silmaril.Logic.ACL2.LegacyOrdinals.Tests

open Ordinals Recursive

def omega : Encoding := .cons (.natural 1) (.natural 0)

-- Legacy repeated and nested exponents, and invalid exponent order or tail.
example : ordinalMeasure (.cons (.natural 1) (.cons (.natural 1) (.natural 5))) =
    .makeOrd (.natural 1) 2 (.natural 5) := by decide
example : valid (.cons omega (.natural 0)) = true := by decide
example : lt (.cons (.natural 20) (.natural 0)) (.cons omega (.natural 0)) := by decide
example : valid (.cons (.natural 1) (.cons (.natural 2) (.natural 0))) = false := by decide
example : valid (.cons (.natural 1) .otherAtom) = false := by decide
example : valid (.cons (.natural 0) (.natural 0)) = false := by decide

/-- The exported RTL::EXPO-MEASURE formula in standard ACL2. Nonnegative floors
are naturals, and total reciprocal at zero yields the finite tail zero. -/
def expoMeasure : Option ℚ → Encoding
  | none => .natural 0
  | some x =>
    if x < 0 then .cons (.natural 2) (.natural 0)
    else if x < 1 then .cons (.natural 1) (.natural ⌊x⁻¹⌋₊)
    else .natural ⌊x⌋₊

theorem expoMeasure_valid (x : Option ℚ) : valid (expoMeasure x) = true := by
  cases x with
  | none => rfl
  | some x =>
    by_cases h0 : x < 0 <;> by_cases h1 : x < 1 <;> simp [expoMeasure, h0, h1, valid]

private theorem floor_div_lt (a b : ℚ) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    ⌊a / b⌋₊ < ⌊a⌋₊ := by
  have hb' : 0 < b := by linarith
  apply (Nat.floor_lt (div_nonneg (by linarith) hb'.le)).2
  apply (div_lt_iff₀ hb').2
  have h : 1 ≤ (⌊a⌋₊ : ℚ) := by exact_mod_cast (Nat.one_le_floor_iff a).2 ha
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ (⌊a⌋₊ : ℚ) by positivity)
  linarith [Nat.lt_floor_add_one a]

theorem expo_negate (x : ℚ) (h : x < 0) :
    lt (expoMeasure (some (-x))) (expoMeasure (some x)) := by
  have h' : ¬ -x < 0 := by linarith
  by_cases h1 : -x < 1 <;>
    simp [expoMeasure, h, h', h1, lt, cmp, Ordering.then_eq_lt, Nat.compare_eq_lt]

theorem expo_multiply (x b : ℚ) (hx : 0 < x) (h1 : x < 1) (hb : 2 ≤ b) :
    lt (expoMeasure (some (b * x))) (expoMeasure (some x)) := by
  have hb' : 0 < b := by linarith
  have hbx := mul_pos hb' hx
  by_cases h : b * x < 1
  · have hInv : (b * x)⁻¹ = x⁻¹ / b := by rw [mul_inv_rev, div_eq_mul_inv]
    have hfloor := floor_div_lt x⁻¹ b ((one_le_inv₀ hx).2 h1.le) hb
    simpa [expoMeasure, hx.not_gt, h1, hbx.not_gt, h, lt, cmp, hInv, Nat.compare_eq_lt] using hfloor
  · simp [expoMeasure, hx.not_gt, h1, hbx.not_gt, h, lt, cmp]

theorem expo_divide (x b : ℚ) (hb : 2 ≤ b) (hx : b ≤ x) :
    lt (expoMeasure (some (x / b))) (expoMeasure (some x)) := by
  have hb' : 0 < b := by linarith
  have hq : 1 ≤ x / b := (le_div_iff₀ hb').2 (by simpa using hx)
  have hx' : 1 ≤ x := by linarith
  simpa [expoMeasure, show ¬x < 0 by linarith, show ¬x / b < 0 by linarith,
    not_lt_of_ge hq, not_lt_of_ge hx', lt, cmp, Nat.compare_eq_lt] using floor_div_lt x b hx' hb

#guard expoMeasure (some (-2/3)) == .cons (.natural 2) (.natural 0)
#guard expoMeasure (some (1/40)) == .cons (.natural 1) (.natural 40)
#guard expoMeasure (some (13/4)) == .natural 3
#guard expoMeasure (some 0) == .cons (.natural 1) (.natural 0)

inductive Value where
  | nil | truth
  | rational (q : ℚ)
  | cons (car cdr : Value)
  deriving DecidableEq

def Value.asRat : Value → Option ℚ
  | .rational q => some q
  | _ => none

def primitives : Primitives where
  Value := Value
  nil := .nil
  truth := .truth
  cons := .cons
  car := fun | .cons x _ => x | _ => .nil
  cdr := fun | .cons _ y => y | _ => .nil
  consp := fun | .cons .. => true | _ => false
  truth_ne_nil := by decide
  consp_nil := rfl
  consp_truth := rfl
  consp_cons _ _ := rfl
  car_cons _ _ := rfl
  cdr_cons _ _ := rfl
  car_atom x h := by cases x <;> simp_all
  cdr_atom x h := by cases x <;> simp_all

def testName : Name := ⟨"SILMARIL", "POSITIVE-BELOW-ONE"⟩
def doubleName : Name := ⟨"SILMARIL", "DOUBLE"⟩
def loopName : Name := ⟨"SILMARIL", "EXPE-DOUBLE"⟩

def old : Signature := ⟨fun f => if f = testName ∨ f = doubleName then some 1 else none⟩
def members : Signature := ⟨fun f => if f = loopName then some 1 else none⟩

def test : old.Symbol 1 := ⟨testName, by decide⟩
def twice : old.Symbol 1 := ⟨doubleName, by decide⟩
def loop : members.Symbol 1 := ⟨loopName, by decide⟩

private theorem old_arity {k : Nat} (f : old.Symbol k) : k = 1 := by
  have h := f.property
  change (if f.val = testName ∨ f.val = doubleName then some 1 else none) = some k at h
  split at h <;> simp_all

private theorem member_arity {k : Nat} (f : members.Symbol k) : k = 1 := by
  have h := f.property
  change (if f.val = loopName then some 1 else none) = some k at h
  split at h <;> simp_all

def oldModel : Model old where
  primitives := primitives
  interpret f args :=
    let x := (args ⟨0, old_arity f ▸ (by decide : 0 < 1)⟩).asRat
    if f.val = testName then
      primitives.ofBool (x.any (fun q => decide (0 < q ∧ q < 1)))
    else
      .rational (2 * x.getD 0)

-- The body isolates the RTL::EXPE multiply edge at radix 2. Returning the
-- first value outside the branch is an authored fixture, with no exponent arithmetic.
def body : Body old members 1 :=
  .ite (.app test ![.var 0]) (.call loop ![.app twice ![.var 0]]) (.base (.var 0))

def block : Block old where
  members := members
  fresh := by
    intro name k h
    change (if name = loopName then some 1 else none) = some k at h
    split at h
    next hn => subst name; decide
    next => contradiction
  body f := member_arity f ▸ body

def rank : OrdinalAdmission.Measure block oldModel := fun state =>
  let x := state.args ⟨0, member_arity state.symbol ▸ (by decide : 0 < 1)⟩
  expoMeasure (some (x.asRat.getD 0))

theorem projection_terminates : Terminates block oldModel rank := by
  refine ⟨?_, ?_⟩
  · intro state
    unfold rank
    exact expoMeasure_valid _
  rintro ⟨k, f, args⟩
  have hk := member_arity f
  subst k
  change body.CallsSatisfy oldModel args (fun next => lt (rank next) (rank ⟨1, f, args⟩))
  simp only [body, Body.CallsSatisfy, Term.eval]
  refine ⟨fun h => ?_, fun _ => trivial⟩
  cases hx : Value.asRat (args 0) with
  | none => simp [oldModel, test, Term.eval, primitives, Primitives.ofBool, hx] at h
  | some q =>
    have hq : 0 < q ∧ q < 1 := by
      simpa [oldModel, test, Term.eval, primitives, Primitives.ofBool, hx] using h
    have hne : doubleName ≠ testName := by decide
    have rat (z : ℚ) : Value.asRat (.rational z) = some z := rfl
    simpa [Call.ofTerms, rank, oldModel, Term.eval, twice, primitives, hne, rat, hx] using
      expo_multiply q 2 hq.1 hq.2 le_rfl

theorem admitted : OrdinalAdmission.Terminates block oldModel (fun s => ordinalMeasure (rank s)) :=
  projection_terminates.toOrdinal

theorem equation : (block.equation loop).Holds admitted.model := admitted.equation_holds loop

def run (q : ℚ) : Value := admitted.interpret ⟨1, loop, ![.rational q]⟩

#guard run (1/40) == .rational (8/5)

#print axioms ordinal_valid
#print axioms lt_iff
#print axioms cmp_eq_eq
#print axioms lt_cons_cons
#print axioms wellFounded
#print axioms Terminates.toOrdinal
#print axioms expoMeasure_valid
#print axioms expo_negate
#print axioms expo_multiply
#print axioms expo_divide
#print axioms projection_terminates
#print axioms equation

end Silmaril.Logic.ACL2.LegacyOrdinals.Tests

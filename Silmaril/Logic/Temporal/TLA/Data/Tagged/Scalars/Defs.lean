module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Defs

/-! # Integer and Boolean values -/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

/-- Interleave the nonnegative integers and the negative integers in a natural code. -/
def intIndex : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

namespace Value

def integer (n : Int) : Value.{u} :=
  .tagged .integer (natCode (intIndex n))

def boolean (b : Bool) : Value.{u} :=
  .tagged .boolean (natCode b.toNat)

noncomputable def asInt : Value.{u} → Option Int := decode integer
noncomputable def asBool : Value.{u} → Option Bool := decode boolean

def isTrue (x : Value.{u}) : Prop := x = boolean true

noncomputable def ofProp (p : Prop) : Value.{u} :=
  open Classical in boolean (decide p)

/-- Boolean negation in the liberal truth interpretation. -/
noncomputable def neg (x : Value.{u}) : Value.{u} := ofProp (¬ x.isTrue)

/-- Boolean conjunction in the liberal truth interpretation. -/
noncomputable def and (x y : Value.{u}) : Value.{u} := ofProp (x.isTrue ∧ y.isTrue)

noncomputable def add (policy : Unspecified.{u}) (x y : Value.{u}) : Value.{u} :=
  match x.asInt, y.asInt with
  | some a, some b => integer (a + b)
  | _, _ => policy .add [x, y]

noncomputable def sub (policy : Unspecified.{u}) (x y : Value.{u}) : Value.{u} :=
  match x.asInt, y.asInt with
  | some a, some b => integer (a - b)
  | _, _ => policy .sub [x, y]

/-- The reference integer remainder equation applies to positive divisors. -/
noncomputable def modulo (policy : Unspecified.{u}) (x y : Value.{u}) : Value.{u} :=
  open Classical in
  match x.asInt, y.asInt with
  | some a, some b => if 0 < b then integer (a % b) else policy .modulo [x, y]
  | _, _ => policy .modulo [x, y]

noncomputable def le (policy : Unspecified.{u}) (x y : Value.{u}) : Value.{u} :=
  open Classical in
  match x.asInt, y.asInt with
  | some a, some b => ofProp (a ≤ b)
  | _, _ => if x = y then boolean true else policy .le [x, y]

noncomputable def lt (policy : Unspecified.{u}) (x y : Value.{u}) : Value.{u} :=
  ofProp ((le policy x y).isTrue ∧ x ≠ y)

end Value

namespace SetData

noncomputable def integers : SetData.{u} :=
  ⟨ZFSet.range (fun n : Int => (Value.integer.{u} n).code)⟩

noncomputable def naturals : SetData.{u} :=
  ⟨ZFSet.range (fun n : Nat => (Value.integer.{u} n).code)⟩

def booleans : SetData.{u} := enum [Value.boolean false, Value.boolean true]

noncomputable def intRange (lo hi : Int) : SetData.{u} :=
  integers.sep (fun v => ∃ n : Int, Value.integer n = v ∧ lo ≤ n ∧ n ≤ hi)

end SetData

noncomputable def Value.interval (policy : Unspecified.{u}) (x y : Value.{u}) : Value.{u} :=
  match x.asInt, y.asInt with
  | some a, some b => set (SetData.intRange a b)
  | _, _ => policy .interval [x, y]

end Silmaril.Logic.Temporal.TLA.Data.Tagged

module

public import Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Defs

/-! Laws of the tagged interpretation, with set formation restricted to recognized bounds. -/

public section

namespace Silmaril.Logic.Temporal.TLA.DataElab.Tagged

open Resolution Data.Tagged

universe u

variable (policy : Policy.{u})

@[simp] theorem Policy.numeral_eq (n : Nat) :
    policy.operations.numeral n = Value.integer (Int.ofNat n) := rfl

@[simp] theorem Policy.mem_value (x bound : Value.{u}) :
    policy.operations.mem x bound ↔ x.mem bound := Iff.rfl

@[simp] theorem Policy.mem_enum (x : Value.{u}) (values : List Value.{u}) :
    policy.operations.mem x (policy.operations.enum values) ↔ x ∈ values :=
  Value.mem_set.trans (SetData.mem_enum x values)

@[simp] theorem Policy.sep_set (set : SetData.{u}) (predicate : Value.{u} → Prop) :
    policy.operations.sep (Value.set set) predicate = Value.set (set.sep predicate) := by
  simp [Policy.operations]

@[simp] theorem Policy.image_set (set : SetData.{u}) (f : Value.{u} → Value.{u}) :
    policy.operations.image (Value.set set) f = Value.set (set.image f) := by
  simp [Policy.operations]

theorem Policy.mem_sep_set {x : Value.{u}} {set : SetData.{u}} {predicate : Value.{u} → Prop} :
    policy.operations.mem x (policy.operations.sep (Value.set set) predicate) ↔
      policy.operations.mem x (Value.set set) ∧ predicate x := by
  simp

theorem Policy.mem_image_set {x : Value.{u}} {set : SetData.{u}} {f : Value.{u} → Value.{u}} :
    policy.operations.mem x (policy.operations.image (Value.set set) f) ↔
      ∃ y, policy.operations.mem y (Value.set set) ∧ f y = x := by
  simp [SetData.mem_image]

theorem Policy.set_eq_iff {s t : SetData.{u}} :
    Value.set s = Value.set t ↔
      ∀ x : Value.{u}, policy.operations.mem x (Value.set s) ↔ policy.operations.mem x (Value.set t) :=
  Value.set_eq_iff

theorem Policy.not_mem_of_asSet_none {x bound : Value.{u}} (h : bound.asSet = none) :
    ¬ policy.operations.mem x bound :=
  Value.not_mem_of_asSet_none h

theorem Policy.sep_of_asSet_none {bound : Value.{u}} (h : bound.asSet = none)
    (predicate : Value.{u} → Prop) :
    policy.operations.sep bound predicate = policy.invalidSet .separation bound := by
  simp [Policy.operations, h]

theorem Policy.image_of_asSet_none {bound : Value.{u}} (h : bound.asSet = none)
    (f : Value.{u} → Value.{u}) :
    policy.operations.image bound f = policy.invalidSet .image bound := by
  simp [Policy.operations, h]

theorem Policy.choose_of_asSet_none {bound : Value.{u}} (h : bound.asSet = none)
    (predicate : Value.{u} → Prop) :
    policy.operations.choice.choose (fun x => policy.operations.mem x bound ∧ predicate x) =
      policy.choice.noWitness := by
  apply congrArg policy.choice.choose
  exact funext fun _ => propext (iff_of_false (fun hp => policy.not_mem_of_asSet_none h hp.1) id)

@[simp] theorem Policy.holds_eq (x : Value.{u}) : policy.booleans.holds x ↔ x.isTrue := Iff.rfl

theorem Policy.ofProp_eq (p : Prop) : policy.booleans.ofProp p = Value.ofProp p := by
  classical
  by_cases h : p <;> simp [Policy.booleans, Booleans.ofProp, Value.ofProp, h]

theorem Policy.external_apply (table : BindingId → Option NumericPrimitive)
    {id : BindingId} {op : NumericPrimitive} {arity : Nat} (found : table id = some op)
    (admitted : numericSignature table id = some arity) (args : List Value.{u}) :
    (policy.external table id arity admitted).apply args = (policy.primitive op).apply args := by
  revert admitted
  unfold Policy.external numericSignature
  rw [found]
  exact fun admitted => by cases Option.some.inj admitted; rfl

@[simp] theorem Policy.interval_apply (x y : Value.{u}) :
    (policy.primitive .interval).apply [x, y] = Value.interval policy.numeric x y := by rfl

@[simp] theorem Policy.add_apply (x y : Value.{u}) :
    (policy.primitive .add).apply [x, y] = Value.add policy.numeric x y := by rfl

@[simp] theorem Policy.sub_apply (x y : Value.{u}) :
    (policy.primitive .sub).apply [x, y] = Value.sub policy.numeric x y := by rfl

@[simp] theorem Policy.modulo_apply (x y : Value.{u}) :
    (policy.primitive .modulo).apply [x, y] = Value.modulo policy.numeric x y := by rfl

@[simp] theorem Policy.le_apply (x y : Value.{u}) :
    (policy.primitive .le).apply [x, y] = Value.le policy.numeric x y := by rfl

@[simp] theorem Policy.lt_apply (x y : Value.{u}) :
    (policy.primitive .lt).apply [x, y] = Value.lt policy.numeric x y := by rfl

@[simp] theorem Policy.naturals_apply :
    (policy.primitive .naturals).apply [] = Value.set SetData.naturals := by rfl

@[simp] theorem Policy.integers_apply :
    (policy.primitive .integers).apply [] = Value.set SetData.integers := by rfl

theorem Policy.mem_naturals (x : Value.{u}) :
    policy.operations.mem x ((policy.primitive .naturals).apply []) ↔
      ∃ n : Nat, Value.integer n = x := by
  simp [SetData.mem_naturals]

theorem Policy.mem_integers (x : Value.{u}) :
    policy.operations.mem x ((policy.primitive .integers).apply []) ↔
      ∃ n : Int, Value.integer n = x := by
  simp [SetData.mem_integers]

end Silmaril.Logic.Temporal.TLA.DataElab.Tagged

module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Scalars.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Thms

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

theorem intIndex_injective : Function.Injective intIndex := by
  intro a b h
  cases a <;> cases b <;> simp only [intIndex] at h
  · exact congrArg Int.ofNat (by omega)
  · omega
  · omega
  · exact congrArg Int.negSucc (by omega)

namespace Value

theorem integer_injective : Function.Injective (integer.{u}) :=
  fun _ _ h => intIndex_injective (natCode_injective (tagged_inj.mp h).2)

theorem boolean_injective : Function.Injective (boolean.{u}) := by
  intro a b h
  have h := natCode_injective (tagged_inj.mp h).2
  cases a <;> cases b <;> simp_all [Bool.toNat]

theorem integer_ne_boolean (n : Int) (b : Bool) : integer.{u} n ≠ boolean b :=
  fun h => Kind.noConfusion (tagged_inj.mp h).1

theorem integer_ne_set (n : Int) (s : SetData.{u}) : integer n ≠ set s :=
  fun h => Kind.noConfusion (tagged_inj.mp h).1

theorem boolean_ne_set (b : Bool) (s : SetData.{u}) : boolean b ≠ set s :=
  fun h => Kind.noConfusion (tagged_inj.mp h).1

theorem asInt_eq_some {x : Value.{u}} {n : Int} : x.asInt = some n ↔ integer n = x :=
  decode_eq_some integer_injective

theorem asBool_eq_some {x : Value.{u}} {b : Bool} : x.asBool = some b ↔ boolean b = x :=
  decode_eq_some boolean_injective

@[simp] theorem asInt_integer (n : Int) : (integer.{u} n).asInt = some n :=
  asInt_eq_some.mpr rfl

@[simp] theorem asBool_boolean (b : Bool) : (boolean.{u} b).asBool = some b :=
  asBool_eq_some.mpr rfl

@[simp] theorem asInt_boolean (b : Bool) : (boolean.{u} b).asInt = none :=
  decode_eq_none (fun ⟨n, h⟩ => integer_ne_boolean n b h)

@[simp] theorem asInt_set (s : SetData.{u}) : (set s).asInt = none :=
  decode_eq_none (fun ⟨n, h⟩ => integer_ne_set n s h)

@[simp] theorem asSet_integer (n : Int) : (integer.{u} n).asSet = none :=
  decode_eq_none (fun ⟨s, h⟩ => integer_ne_set n s h.symm)

@[simp] theorem asSet_boolean (b : Bool) : (boolean.{u} b).asSet = none :=
  decode_eq_none (fun ⟨s, h⟩ => boolean_ne_set b s h.symm)

@[simp] theorem isTrue_boolean (b : Bool) : (boolean.{u} b).isTrue ↔ b = true :=
  ⟨fun h => boolean_injective h, congrArg boolean⟩

@[simp] theorem isTrue_ofProp (p : Prop) : (ofProp.{u} p).isTrue ↔ p := by
  classical
  simp [ofProp]

@[simp] theorem neg_boolean (b : Bool) : neg (boolean.{u} b) = boolean (!b) := by
  classical
  cases b <;> simp [neg, ofProp]

@[simp] theorem and_boolean (a b : Bool) :
    and (boolean.{u} a) (boolean b) = boolean (a && b) := by
  classical
  cases a <;> cases b <;> simp [and, ofProp]

variable (policy : Unspecified.{u})

@[simp] theorem add_integer (a b : Int) : add policy (integer a) (integer b) = integer (a + b) := by
  simp [add]

@[simp] theorem sub_integer (a b : Int) : sub policy (integer a) (integer b) = integer (a - b) := by
  simp [sub]

theorem add_bad_left {x y : Value.{u}} (h : x.asInt = none) : add policy x y = policy .add [x, y] := by
  simp [add, h]

theorem add_bad_right {x y : Value.{u}} (h : y.asInt = none) :
    add policy x y = policy .add [x, y] := by
  cases hx : x.asInt <;> simp [add, hx, h]

theorem modulo_integer (a b : Int) (h : 0 < b) :
    modulo policy (integer a) (integer b) = integer (a % b) := by
  simp [modulo, h]

theorem modulo_nonpositive (a b : Int) (h : b ≤ 0) :
    modulo policy (integer a) (integer b) = policy .modulo [integer a, integer b] := by
  simp [modulo, Int.not_lt.mpr h]

theorem modulo_bad_left {x y : Value.{u}} (h : x.asInt = none) :
    modulo policy x y = policy .modulo [x, y] := by
  simp [modulo, h]

theorem modulo_bad_right {x y : Value.{u}} (h : y.asInt = none) :
    modulo policy x y = policy .modulo [x, y] := by
  cases hx : x.asInt <;> simp [modulo, hx, h]

theorem le_integer (a b : Int) :
    le policy (integer a) (integer b) = ofProp (a ≤ b) := by
  simp [le]

theorem lt_integer (a b : Int) :
    (lt policy (integer a) (integer b)).isTrue ↔ a < b := by
  simp only [lt, isTrue_ofProp, le_integer, ne_eq, integer_injective.eq_iff]
  omega

@[simp] theorem le_self (x : Value.{u}) : le policy x x = boolean true := by
  classical
  cases h : x.asInt <;> simp [le, h, ofProp]

@[simp] theorem interval_integer (lo hi : Int) :
    interval policy (integer lo) (integer hi) = set (SetData.intRange lo hi) := by
  simp [interval]

end Value

namespace SetData

theorem mem_integers {v : Value.{u}} : integers.mem v ↔ ∃ n : Int, Value.integer n = v :=
  ZFSet.mem_range.trans (exists_congr fun _ => ⟨fun h => Value.code_injective h, congrArg Value.code⟩)

theorem mem_naturals {v : Value.{u}} :
    naturals.mem v ↔ ∃ n : Nat, Value.integer n = v :=
  ZFSet.mem_range.trans (exists_congr fun _ => ⟨fun h => Value.code_injective h, congrArg Value.code⟩)

theorem integer_mem_naturals (n : Int) : naturals.mem (Value.integer.{u} n) ↔ 0 ≤ n := by
  rw [mem_naturals]
  simp only [Value.integer_injective.eq_iff]
  exact ⟨fun ⟨m, h⟩ => h ▸ Int.natCast_nonneg m, fun h => ⟨n.toNat, Int.toNat_of_nonneg h⟩⟩

theorem mem_booleans {v : Value.{u}} : booleans.mem v ↔ ∃ b : Bool, Value.boolean b = v := by
  simp only [booleans, mem_enum, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨fun h => h.elim (fun e => ⟨false, e.symm⟩) (fun e => ⟨true, e.symm⟩),
    fun ⟨b, h⟩ => by cases b <;> simp [← h]⟩

theorem mem_intRange (lo hi : Int) {v : Value.{u}} :
    (intRange lo hi).mem v ↔ ∃ n : Int, Value.integer n = v ∧ lo ≤ n ∧ n ≤ hi := by
  rw [intRange, mem_sep, mem_integers]
  exact ⟨And.right, fun h => ⟨let ⟨n, hn, _, _⟩ := h; ⟨n, hn⟩, h⟩⟩

theorem integer_mem_intRange (lo hi n : Int) :
    (intRange lo hi).mem (Value.integer.{u} n) ↔ lo ≤ n ∧ n ≤ hi := by
  simp [mem_intRange, Value.integer_injective.eq_iff]

end SetData

end Silmaril.Logic.Temporal.TLA.Data.Tagged

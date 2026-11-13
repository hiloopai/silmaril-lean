module

public import Silmaril.Wasm.Component.Reference.ABI.Scalar.Defs

public import Silmaril.Raw.Wasm.Component.ABI.Calling
public import Silmaril.Wasm.Execution.Runtime

/-!
# Canonical boolean and integer values

These direct adapters cover booleans and all eight WIT integer types. Narrow
unsigned values are zero-extended and signed values are sign-extended on
lowering; lifting keeps the low bits. Floating-point NaN choices, Unicode,
handles, and memory-backed values are separate extensions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

private theorem truncate_signExtend {n m : Nat} (h : n ≤ m) (x : BitVec n) :
    (x.signExtend m).setWidth n = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have him : i < m := Nat.lt_of_lt_of_le hi h
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi, him, decide_true, Bool.true_and, ite_true]

theorem Scalar.lift_lower (v : ScalarValue) : v.type.lift v.lower = some v := by
  rcases v with ⟨t, x⟩
  cases t <;> dsimp only [Scalar.width] at x
  all_goals simp [ScalarValue.lower, Scalar.lift, Scalar.liftBits, Scalar.coreType,
    Scalar.signed, Scalar.width, Execution.Runtime.Value.int, IntType.width, NumType.width, truncate_signExtend, BitVec.setWidth_setWidth_of_le]

  have hx : x.toNat = 0 ∨ x.toNat = 1 := by
    have bound := x.isLt
    omega
  rcases hx with hx | hx
  · have h : x = 0 := BitVec.eq_of_toNat_eq hx
    subst x
    rfl
  · have h : x = 1 := BitVec.eq_of_toNat_eq hx
    subst x
    rfl

theorem Scalar.lift_type (t : Scalar) (v : Execution.Runtime.Value) (w : ScalarValue)
    (h : t.lift v = some w) : w.type = t := by
  unfold Scalar.lift at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  · exact (congrArg ScalarValue.type h).symm
  · exact (congrArg ScalarValue.type h).symm

theorem liftValues_lowerValues (vs : List ScalarValue) :
    liftValues (vs.map ScalarValue.type) (lowerValues vs) = some vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [lowerValues, List.map_cons, liftValues, Scalar.lift_lower] at *
    rw [ih]
    rfl

theorem liftValues_types (ts : List Scalar) (vs : List Execution.Runtime.Value)
    (ws : List ScalarValue) (h : liftValues ts vs = some ws) : ws.map ScalarValue.type = ts := by
  induction ts generalizing vs ws with
  | nil => cases vs <;> simp_all [liftValues]
  | cons t ts ih =>
    cases vs with
    | nil => simp [liftValues] at h
    | cons v vs =>
      simp only [liftValues, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨w, hw, tail, ht, he⟩ := h
      cases he
      simp [Scalar.lift_type t v w hw, ih _ _ ht]

theorem flattenTypes_scalars (p : AddrType) (ts : List Scalar) :
    flattenTypes p (ts.map Scalar.wit) = ts.map (fun t => .int t.coreType) := by
  induction ts with
  | nil => simp only [List.map_nil, flattenTypes]
  | cons t ts ih => simp only [List.map_cons, flattenTypes, Scalar.flatten_wit, ih,
      List.cons_append, List.nil_append]

theorem DirectSignature.flatten_abi (f : DirectSignature) (p : AddrType) (d : Direction) :
    flattenFunc ⟨p, false, false⟩ d f.abi = f.core := by
  rw [flattenFunc_sync_direct]
  · simp only [DirectSignature.abi, DirectSignature.core, flattenTypes_scalars]
  · simpa only [DirectSignature.abi, flattenTypes_scalars, List.length_map] using f.paramsBound
  · simp only [DirectSignature.abi, flattenTypes_scalars, List.length_map]
    cases f.result <;> simp

end Silmaril.Wasm.Component.ABI

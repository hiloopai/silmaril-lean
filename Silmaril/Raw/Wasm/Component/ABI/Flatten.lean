module

public import Silmaril.Wasm.Component.Reference.ABI.Flatten.Defs

public import Silmaril.Raw.Wasm.Component.WIT
public import Mathlib.Data.List.Basic

/-! # Canonical ABI scalar flattening -/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

universe u

theorem joinType_comm (a b : CoreType) : joinType a b = joinType b a := by
  rcases a with (a | a) <;> cases a <;>
    rcases b with (b | b) <;> cases b <;> rfl

theorem joinType_assoc (a b c : CoreType) : joinType (joinType a b) c = joinType a (joinType b c) := by
  rcases a with (a | a) <;> cases a <;>
    rcases b with (b | b) <;> cases b <;>
    rcases c with (c | c) <;> cases c <;> rfl

theorem joinFlat_comm (xs ys : List CoreType) : joinFlat xs ys = joinFlat ys xs := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => cases ys <;> simp only [joinFlat, joinType_comm, ih]

theorem joinFlat_assoc (xs ys zs : List CoreType) :
    joinFlat (joinFlat xs ys) zs = joinFlat xs (joinFlat ys zs) := by
  induction xs generalizing ys zs with
  | nil => rfl
  | cons x xs ih =>
    cases ys <;> cases zs <;>
      simp only [joinFlat, joinFlat_nil_right, joinType_assoc, ih]

theorem joinFlat_length (xs ys : List CoreType) :
    (joinFlat xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys <;> simp only [joinFlat, List.length_cons, List.length_nil, Nat.max_zero, ih,
      Nat.succ_max_succ]

variable {Resource : Type u}

/-- Variant payload slots are independent of the ordering of two alternatives;
only the separate discriminant assignment changes. -/
theorem variantPayload_swap (a b : List CoreType) (rest : List (List CoreType)) :
    variantPayload (a :: b :: rest) = variantPayload (b :: a :: rest) := by
  simp only [variantPayload, ← joinFlat_assoc, joinFlat_comm a b]

theorem flattenTypes_append (p : AddrType) (xs ys : List (WIT.ClosedType Resource)) :
    flattenTypes p (xs ++ ys) = flattenTypes p xs ++ flattenTypes p ys := by
  induction xs with
  | nil => simp only [List.nil_append, flattenTypes]
  | cons x xs ih => simp only [List.cons_append, flattenTypes, ih, List.append_assoc]

end Silmaril.Wasm.Component.ABI

module

public import Silmaril.Proofs.Wasm.Jco.Styles.Wide.Layout

/-!
# Wide results: the scalar roundtrip

* `lift1 t r`: the flat lift of one scalar; `liftArgs_cons`: lifting a list of scalars is lifting
  each one.
* **`loadScalar_store`**: loading a scalar from the stored bytes of its flat value (a `bool`
  normalised) is its flat lift.
* `fieldWrites_sep`: the writes of the fields of a record are separated.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Component (Flat ValTy Val liftArgs charOfBits)

/-- The flat lift of one scalar. -/
def lift1 (t : ValTy) (r : Flat) : Option Val := (t.lift [r]).bind fun p =>
  if p.2 = [] then some p.1 else none

theorem lift_scalar {t : ValTy} {n : Nat} (ht : scalarSize t = some n) (r : Flat)
    (rest : List Flat) : t.lift (r :: rest) = (lift1 t r).map fun v => (v, rest) := by
  rcases r with ⟨ty, x⟩
  cases t <;> simp [scalarSize] at ht <;> cases ty <;> rename_i k <;> cases k <;>
    simp [ValTy.lift, lift1]
  cases charOfBits x <;> rfl

theorem liftArgs_nil : liftArgs [] [] = some [] := rfl

theorem liftArgs_cons {t : ValTy} {n : Nat} (ht : scalarSize t = some n) (ts : List ValTy)
    (r : Flat) (rs : List Flat) :
    liftArgs (t :: ts) (r :: rs) = (lift1 t r).bind fun v => (liftArgs ts rs).map (v :: ·) := by
  unfold liftArgs
  simp only [ValTy.liftList, lift_scalar ht]
  cases lift1 t r with
  | none => rfl
  | some v =>
    simp only [Option.map_some, Option.bind_some]
    cases ValTy.liftList ts rs with
    | none => rfl
    | some p => rcases p with ⟨vs, _ | _⟩ <;> rfl

theorem ofNat_mod_toNat {w k : Nat} (x : BitVec k) (m : Nat) (hm : 2 ^ w ∣ m) :
    BitVec.ofNat w (x.toNat % m) = x.setWidth w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  exact Nat.mod_mod_of_dvd _ hm

theorem bool_case (x : BitVec 32) :
    ((if (x == 0#32) = true then 0#32 else 1#32).toNat % 256 != 0) = (x != 0#32) := by
  split
  · next hx =>
    have hx' : x = 0#32 := by simpa using hx
    rw [hx']
    rfl
  · next hx =>
    have hx' : ¬ x = 0#32 := by simpa using hx
    simp [hx']

theorem char_case (x : BitVec 32) :
    Option.map Val.char (charOfBits (BitVec.ofNat 32 (x.toNat % 4294967296))) =
      (Option.map (fun c => (Val.char c, ([] : List Flat))) (charOfBits x)).bind fun p =>
        if p.2 = [] then some p.1 else none := by
  rw [Nat.mod_eq_of_lt x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  cases charOfBits x <;> rfl

theorem loadScalar_store {t : ValTy} {n : Nat} (ht : scalarSize t = some n) (r : Flat)
    (hr : t.flat = [r.type]) :
    loadScalar t (leBytes n (normField t r).bits.toNat) = lift1 t r := by
  rcases r with ⟨ty, x⟩
  cases t <;> simp [scalarSize] at ht <;> subst ht <;>
    simp [ValTy.flat] at hr <;> subst hr <;>
    simp [loadScalar, normField, asI32?, leNat_leBytes, lift1, ValTy.lift]
  case bool => exact bool_case x
  case char => exact char_case x
  all_goals first
    | exact ofNat_mod_toNat x _ ⟨1, rfl⟩
    | (congr 1; exact (ofNat_mod_toNat x _ ⟨1, rfl⟩).trans (BitVec.setWidth_eq x))

end Silmaril.Proofs.Wasm.Jco

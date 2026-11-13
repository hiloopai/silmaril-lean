module

public import Silmaril.Wasm.Component.ABI.Defs
import Silmaril.Proofs.Wasm.Component.ABI.RoundTrip

/-!
# Canonical ABI: theorems

* `ValTy.lift_lower`: **the canonical ABI round trip** — for a well-typed
  value `v : t`, `t.lift (t.lower v ++ r) = some (v, r)`; in particular
  `liftArgs_lowerArgs`: `liftArgs ts (lowerArgs ts vs) = some vs`.
* `ValTy.lower_types`: lowered well-typed values have the flattened types.
* `ValTy.check_of_lift`, `checkList_of_liftArgs`: lifting produces well-typed
  values (so a lowering after a lifting never fails its type check).
* `canonFlat_trivial`: for trivially represented types (32/64-bit integers,
  floats and records of these) the canonicalisation `lower ∘ lift` is a type
  check of the core values. For the other types it is a genuine
  normalisation (for example `bool` sends every nonzero `i32` to `1`), so the
  other composite `lift ∘ lower` on core values is *not* the identity.

Proofs are in `Silmaril.Proofs.Wasm.Component.ABI.RoundTrip`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Wasm (NumType)

/-- **Canonical ABI round trip.** -/
theorem ValTy.lift_lower (t : ValTy) (v : Val) (h : t.check v = true) (r : List Flat) :
    t.lift (t.lower v ++ r) = some (v, r) :=
  Silmaril.Proofs.Wasm.Component.ABI.lift_lower t v h r

/-- The round trip for lists of values. -/
theorem ValTy.liftList_lowerList (ts : List ValTy) (vs : List Val)
    (h : ValTy.checkList ts vs = true) (r : List Flat) :
    ValTy.liftList ts (ValTy.lowerList ts vs ++ r) = some (vs, r) :=
  Silmaril.Proofs.Wasm.Component.ABI.liftList_lowerList ts vs h r

/-- The round trip for argument (or result) lists. -/
theorem liftArgs_lowerArgs {ts : List ValTy} {vs : List Val} (h : ValTy.checkList ts vs = true) :
    liftArgs ts (lowerArgs ts vs) = some vs :=
  Silmaril.Proofs.Wasm.Component.ABI.liftArgs_lowerArgs h

/-- Lowered values have the flattened types. -/
theorem ValTy.lower_types (t : ValTy) (v : Val) (h : t.check v = true) :
    (t.lower v).map (·.type) = t.flat :=
  Silmaril.Proofs.Wasm.Component.ABI.lower_types t v h

/-- Lifted values are well typed. -/
theorem ValTy.check_of_lift {t : ValTy} {xs : List Flat} {v : Val} {r : List Flat}
    (h : t.lift xs = some (v, r)) : t.check v = true :=
  Silmaril.Proofs.Wasm.Component.ABI.check_of_lift t xs v r h

/-- Lifted argument lists are well typed. -/
theorem checkList_of_liftArgs {ts : List ValTy} {xs : List Flat} {vs : List Val}
    (h : liftArgs ts xs = some vs) : ValTy.checkList ts vs = true :=
  Silmaril.Proofs.Wasm.Component.ABI.checkList_of_liftArgs h

/-- For trivially represented types the canonicalisation is a type check. -/
theorem canonFlat_trivial {ts : List ValTy} (ht : ValTy.trivialList ts = true) (xs : List Flat) :
    canonFlat ts xs = checkFlat (ValTy.flatList ts) xs :=
  Silmaril.Proofs.Wasm.Component.ABI.canonFlat_trivial ht xs

/-- Lowering after a lifting never fails its type check: `checkLower` after
`liftArgs` is the canonicalisation. -/
theorem liftArgs_bind_checkLower (ts : List ValTy) (xs : List Flat) :
    (liftArgs ts xs).bind (checkLower ts) = canonFlat ts xs := by
  cases e : liftArgs ts xs with
  | none => simp [canonFlat, e]
  | some vs => simp [canonFlat, checkLower, checkList_of_liftArgs e, e]

/-- Lifting after a checked lowering is the type check. -/
theorem checkLower_bind_liftArgs (ts : List ValTy) (vs : List Val) :
    (checkLower ts vs).bind (liftArgs ts) = checkVals ts vs := by
  unfold checkLower checkVals
  split_ifs with h
  · simp [liftArgs_lowerArgs h]
  · rfl

/-! ## Examples -/

/-- `bool` lifting normalises: the core value `5` canonicalises to `1`. -/
example : canonFlat [.bool] [.i32 5] = some [.i32 1] := by decide

/-- An out-of-range `char` traps. -/
example : liftArgs [.char] [.i32 0xD800] = none := by decide

/-- A `result<u8, s16>` round trip, with joined payload slots. -/
example : liftArgs [.result (some .u8) (some .s16)]
    (lowerArgs [.result (some .u8) (some .s16)] [.variant 1 (some (.s16 (-3)))]) =
    some [.variant 1 (some (.s16 (-3)))] := by rfl

end Silmaril.Wasm.Component

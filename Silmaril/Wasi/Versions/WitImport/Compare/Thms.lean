module

public import Silmaril.Wasi.Versions.WitImport.Names.Thms
public import Silmaril.Wasi.Versions.Random.Thms
public import Silmaril.Wasi.Versions.Random.Wit.Thms
public import Silmaril.Wasi.Theory.Thms

/-!
# The imported WASI signatures equal the hand-written ones

**Names**: `Silmaril.Wasi.Versions.WitImport.Names.Thms`.

**Signatures.** `rand3_sigs`, `rand2_sigs`: the imported signatures of `wasi:random`, with
`rand_sig_types` (0.2 and 0.3 have the same types; the parameter is renamed `len` → `max-len`,
the seed function `insecure-seed` → `get-insecure-seed`).

**Typing.** `ok3_eq`, `ok2_eq`: the hand-written `wasi:random` answer checks are exactly the
WIT typing of the imported table and the length condition. `rand3Impl_wit`, `rand2Impl_wit`:
the concrete device hosts satisfy the imported WIT typing. `p3_ok3_wit`: the hand-written 0.3
typing `P3.ok3` implies the imported WIT typing for the slice's functions except
`get-directories`; **refuted** for it (`getDirs3_not_wit`: `P3.ok3` does not check the
preopen names are strings). `openAt3_slice_untyped`: the slice's two-argument `open-at` calls
are not WIT-typed calls (WIT has five parameters), so `witOk` does not constrain them.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component.Binary (PrimValType)
open Silmaril.Wasi.Versions.Random

/-- The 0.3 `wasi:random` theory implies the imported WIT typing. -/
theorem randTh3_wit {t : List WEv} (h : randTh3.Accepts t) : (witTh rand3T).Accepts t := by
  rw [randTh3, pointwise_accepts_iff] at h
  refine (pointwise_accepts_iff _ t).2 fun e he => ?_
  have := h e he; rw [ok3_eq, Bool.and_eq_true] at this; exact this.1

/-- The 0.2 `wasi:random` theory implies the imported WIT typing. -/
theorem randTh2_wit {t : List WEv} (h : randTh2.Accepts t) : (witTh rand2T).Accepts t := by
  rw [randTh2, pointwise_accepts_iff] at h
  refine (pointwise_accepts_iff _ t).2 fun e he => ?_
  have := h e he; rw [ok2_eq, Bool.and_eq_true] at this; exact this.1

/-- **The concrete 0.3 device host answers with the imported WIT types.** -/
theorem rand3Impl_wit {Y : Silmaril.Games.Sig.{0}} {I : Set FnName} (src : Nat → BitVec 8) (c : Nat) :
    (hostSat (witTh rand3T).Accepts).holds (concrete (Y := Y) (I := I) (rand3Impl src c)) :=
  fun s hs => randTh3_wit (rand3Impl_sat src c s hs)

/-- **The concrete 0.2 device host answers with the imported WIT types.** -/
theorem rand2Impl_wit {Y : Silmaril.Games.Sig.{0}} {I : Set FnName} (src : Nat → BitVec 8) :
    (hostSat (witTh rand2T).Accepts).holds (concrete (Y := Y) (I := I) (rand2Impl src)) :=
  fun s hs => randTh2_wit (rand2Impl_sat src s hs)

end Silmaril.Wasi.Versions.WitImport

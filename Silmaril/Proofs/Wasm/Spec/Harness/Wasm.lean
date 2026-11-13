module

public import Silmaril.Proofs.Wasm.Spec.Harness.Basic
public import Silmaril.Proofs.Wasm.Spec.Basic.Basic

@[expose] public section

/-!
# Harness reduction: exactness and the Wasm assertion harness

`RetHarness.reduce_iff`: for the most general harness, "the linked system never fails a check"
is equivalent to the return postcondition, on every trace set. For Wasm, the check is an
`assert` import receiving `i32 1` or `i32 0` (`assertVerdict`), so: **the linkage of the most
general harness with the program never calls `assert` with `i32 0` iff export `e` only returns
results satisfying `Q`** (`wasm_harness_iff`), and then every terminating closed-world Core
behaviour of `e` against any host machine satisfies `Q` (`wasm_harness_closed_world`).
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {Ty A R : Type} {Xp Xh Xl : Iface Ty} {W : Wiring Xp Xh Xl}

/-- **Harness reduction is exact** for the most general harness (sound and complete). -/
theorem RetHarness.reduce_iff (H : RetHarness W A R) {okArg : A → Prop} {Q : R → Prop}
    (hv : ∀ r, okArg (H.verdict r) ↔ Q r) (hpl : ∀ k, W.pl k ≠ W.ol H.chk)
    (hol : Function.Injective W.ol) (hph : ∀ j k, W.ph j ≠ W.oh k)
    (hinj : Function.Injective W.ph) (Tp : Set (List (Event A R Xp))) :
    (callPre Ty A R).Sat (linkTraces W Tp H.traces) ⟨W.ol H.chk, okArg⟩ ↔
      (retPost Ty A R).Sat Tp ⟨H.e, Q⟩ := by
  rw [ofTrace_sat_linkTraces_iff]
  refine forall₂_congr fun tp _ => ⟨fun h => H.sound (fun r => (hv r).1) h, fun h => ?_⟩
  exact H.complete (fun r => (hv r).2) hpl hol hph hinj h

open Classical in
/-- The `assert` argument checking `Q` on a result: `i32 1` if it holds, `i32 0` otherwise. -/
noncomputable def assertVerdict (Q : Behaviour Val → Prop) (b : Behaviour Val) : List Val :=
  if Q b then [Val.i32 1] else [Val.i32 0]

/-- The verdict passes `assert` iff `Q` holds. -/
theorem assertOk_assertVerdict (Q : Behaviour Val → Prop) (b : Behaviour Val) :
    assertOk (assertVerdict Q b) ↔ Q b := by
  unfold assertVerdict assertOk
  by_cases hQ : Q b
  · simp only [hQ, ↓reduceIte, List.head?_cons, ne_eq, Option.some.injEq, iff_true]
    decide
  · simp [hQ]

/-- **The Wasm assertion harness**: the linkage of the most general harness (checking with
`assertVerdict Q`) and a Wasm program never calls `assert` with `i32 0` iff every return of
export `e` satisfies `Q` (every profile). -/
theorem wasm_harness_iff {P : Profile} {Xp Xh Xl : WIface} {W : Wiring Xp Xh Xl}
    (H : RetHarness W (List Val) (Behaviour Val)) {Q : Behaviour Val → Prop}
    (hQ : H.verdict = assertVerdict Q) (hpl : ∀ k, W.pl k ≠ W.ol H.chk)
    (hol : Function.Injective W.ol) (hph : ∀ j k, W.ph j ≠ W.oh k)
    (hinj : Function.Injective W.ph) (p : WasmProg Xp) :
    (assertNeverFalse FnType (Behaviour Val)).Sat
        (linkTraces W ((wasmSem P).traces p) H.traces) (W.ol H.chk) ↔
      Models (retPost FnType (List Val) (Behaviour Val)) (wasmSem P) p ⟨H.e, Q⟩ := by
  rw [models_iff]
  have hv : ∀ r, assertOk (H.verdict r) ↔ Q r := fun r => by
    rw [hQ]
    exact assertOk_assertVerdict Q r
  exact H.reduce_iff hv hpl hol hph hinj _

/-- **Harness reduction down to Core 3.0**: if the linkage of the most general harness and a
well-formed Wasm program never calls `assert` with `i32 0`, every terminating closed-world Core
behaviour of a call of `e` against any host machine satisfies `Q` (every profile). -/
theorem wasm_harness_closed_world {P : Profile} {Xp Xh Xl : WIface} {W : Wiring Xp Xh Xl}
    (H : RetHarness W (List Val) (Behaviour Val)) {Q : Behaviour Val → Prop}
    (hQ : H.verdict = assertVerdict Q) (hpl : ∀ k, W.pl k ≠ W.ol H.chk)
    (hol : Function.Injective W.ol) (hph : ∀ j k, W.ph j ≠ W.oh k)
    (hinj : Function.Injective W.ph) (p : WasmProg Xp) (hw : p.inst.WellFormed p.store)
    (hlink : (assertNeverFalse FnType (Behaviour Val)).Sat
        (linkTraces W ((wasmSem P).traces p) H.traces) (W.ol H.chk))
    (L : SEnv (ifaceSig Xp.imports)) (hL : L.ThrowsBelow p.store.exns.length) (q : L.S)
    (a : Typed (Xp.exports.get H.e).params) {b : Behaviour Val} (hb : b ≠ .diverges)
    (h : b ∈ sbehavioursOf P L q (invoke p.store (p.inst.addr H.e) a.1)) : Q b :=
  retPost_closed_world (φ := ⟨H.e, Q⟩) p hw
    ((wasm_harness_iff H hQ hpl hol hph hinj p).1 hlink) L hL q a hb h

end Silmaril.Wasm.Spec

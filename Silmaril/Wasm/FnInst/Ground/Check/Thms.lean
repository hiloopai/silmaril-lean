module

public import Silmaril.Wasm.FnInst.Ground.Check.Defs
public import Silmaril.Wasm.Auto.Front.Thms

@[expose] public section

/-! # wasm-check's verdicts as satisfaction in `checkInst`

* `checkEquiv_proved_sat`: a `proved` report of `checkEquivBase` makes `m₁ ≐ m₂` hold in every
  model with the checked relation (every profile);
* `checkEquiv_refuted_not_sat`: a `refuted` report falsifies `m₁ ≐ m₂` at the reference
  profile `profile refOracle`;
* the same for `checkRefinesBase` and `m ⊑ m'`.

Each is the front end's soundness theorem read through `CSen.Holds`; no new semantics is
involved. Open: relating these sentences to the grounded bridge, whose export equivalence
(`exportEquiv_of_good`) is silmaril-lean's `Binaryen.ExportEquiv` under the closed host at
instantiation, while `ModEquiv` is stated on the instance computed by
`Silmaril.Wasm.Verify.instance?` without host.
-/

namespace Silmaril.Wasm.FnInst.Ground.Check

open Silmaril.Wasm.Auto.Front
open Silmaril.Wasm.Verify (refOracle)
open Silmaril.Wasm
open Silmaril.Wasm.SingleThreaded (profile)
open Silmaril.Wasm.Numerics (Profile)

theorem sat_eqv_iff (j : ℕ) (P : Profile) (R : Rel) (m₁ m₂ : Module) :
    checkPlain.Sat (S := ⟨j⟩) (P, R) (.eqv m₁ m₂) ↔ ModEquiv R.toProp P m₁ m₂ j := Iff.rfl

theorem sat_le_iff (j : ℕ) (P : Profile) (R : Rel) (m m' : Module) :
    checkPlain.Sat (S := ⟨j⟩) (P, R) (.le m m') ↔ ModRefines R.toProp P m m' j := Iff.rfl

/-- A `proved` equivalence report: the sentence holds at every profile. -/
theorem checkEquiv_proved_sat {R : Rel} {m₁ m₂ : Module} {j n : ℕ} {idt : Bool}
    (hid : idt = true → m₁ = m₂) (h : (checkEquivBase R m₁ m₂ j n idt).verdict = .proved)
    (P : Profile) : checkPlain.Sat (S := ⟨j⟩) (P, R) (.eqv m₁ m₂) :=
  checkEquivBase_proved hid h P

/-- A `refuted` equivalence report: the sentence fails at the reference profile. -/
theorem checkEquiv_refuted_not_sat {R : Rel} {m₁ m₂ : Module} {j n : ℕ} {idt : Bool}
    (h : (checkEquivBase R m₁ m₂ j n idt).verdict = .refuted) :
    ¬ checkPlain.Sat (S := ⟨j⟩) (profile refOracle, R) (.eqv m₁ m₂) :=
  checkEquivBase_refuted h

/-- A `proved` refinement report: the sentence holds at every profile. -/
theorem checkRefines_proved_sat {R : Rel} {m m' : Module} {j n : ℕ} {idt : Bool}
    (hid : idt = true → m = m') (h : (checkRefinesBase R m m' j n idt).verdict = .proved)
    (P : Profile) : checkPlain.Sat (S := ⟨j⟩) (P, R) (.le m m') :=
  checkRefinesBase_proved_refines hid h P

/-- A `refuted` refinement report: the sentence fails at the reference profile. -/
theorem checkRefines_refuted_not_sat {R : Rel} {m m' : Module} {j n : ℕ} {idt : Bool}
    (h : (checkRefinesBase R m m' j n idt).verdict = .refuted) :
    ¬ checkPlain.Sat (S := ⟨j⟩) (profile refOracle, R) (.le m m') :=
  checkRefinesBase_refuted h

end Silmaril.Wasm.FnInst.Ground.Check

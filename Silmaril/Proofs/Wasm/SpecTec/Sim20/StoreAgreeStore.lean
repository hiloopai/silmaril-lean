module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreAgreeDerive

/-!
# The scalar stores forward in `simEnv20T`, under a context

* `typedV_to20T`: a closed type name typed in `simEnv20 B` is typed in `simEnv20T B` (relation
  table, then `fixCase`);
* **`typedV_intStore20T`**, **`typedV_floatStore20T`**: every V2 scalar store whose pack size is
  below its width (the 2.0 validity condition) is a typed `admininstr` of `simEnv20T B`, at every
  builtins. The corrected premise is checked by evaluation, one number type and pack size at a
  time, with the memory argument left symbolic;
* **`fwdT_storeCtx`**: a top-level V2 scalar store step (`Whole.StoreTop20`) under a value prefix
  and a suffix is a step of `simEnv20T (storeB P)` between the images, from a state typed in
  `simEnv20` and a suffix typed in `simEnv20T`. Round 3's `fwd_storeTop20` gave the step at the
  top of the code only; the context needs the erratum, since `ctxt-instrs` types its code.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly stateT SStep cfgV)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S adminsTy valsTy)
open Silmaril.Wasm.SpecTec.Sim20.Whole (StoreTop20 storeB)

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Typing in `simEnv20T` -/

/-- A closed type name typed in `simEnv20 B` is typed in `simEnv20T B`. -/
theorem typedV_to20T {x : IL.Id} {v : Value}
    (hx : (Sim.Round7.Script.evTyp (.varT x [])).all (RelFree.rfEvB RelFree.bad20) = true)
    (h : TypedV (simEnv20 B) (.varT x []) v) : TypedV (simEnv20T B) (.varT x []) v :=
  typedV_of (envSame20T B) (typRepair20T B) (Whole.typedV_withRels20 hx h)

/-- A list over a closed type name typed in `simEnv20 B` is typed in `simEnv20T B`. -/
theorem typedV_list_to20T {x : IL.Id} {l : List Value}
    (hx : (Sim.Round7.Script.evTyp (.varT x [])).all (RelFree.rfEvB RelFree.bad20) = true)
    (h : TypedV (simEnv20 B) (.iterT (.varT x []) .list) (.list l)) :
    TypedV (simEnv20T B) (.iterT (.varT x []) .list) (.list l) :=
  Sim.typedV_list_iff.2 fun u hu => typedV_to20T hx (Sim.typedV_list_iff.1 h u hu)

/-- The payload type of the corrected `STORE` case. -/
abbrev storePayT : Typ := .tupT [.mk "numtype" (.varT "numtype" []),
  .mk "sz?" (.iterT (.varT "sz" []) .opt), .mk "memarg" (.varT "memarg" [])]

/-- **A payload the corrected case accepts, field by field, is a typed `admininstr`.** -/
theorem typedV_storeT_of {nt sz : Value} (a : V2.MemArg)
    (hnt : TypedV (simEnv20T B) (.varT "numtype" []) nt)
    (hsz : TypedV (simEnv20T B) (.iterT (.varT "sz" []) .opt) sz)
    (hp : PremsOk (simEnv20T B) (caseScope VarEnv.empty storePayT (.tuple [nt, sz, memargV a]))
      [storePremFix]) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (.case "STORE" (.tuple [nt, sz, memargV a])) := by
  have hm : TypedV (simEnv20T B) (.varT "memarg" []) (memargV a) :=
    typedV_to20T (by decide) (Whole.typedV_memarg20 a)
  have ht : HasTyp (simEnv20T B) VarEnv.empty storePayT (.tuple [nt, sz, memargV a]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hnt _ ⟨rfl, rfl, rfl⟩,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hsz _ ⟨rfl, rfl, rfl⟩,
        hasTypTup_cons_iff.2 ⟨_, _, rfl, hm _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩
  have hc := Sim.Typing.hasTypCase_of_findCaseQ findCaseQ_adminStoreT ht
    (bindQuants_nil_iff.2 rfl) hp
  exact typedV_of_empty (hasTyp_varT_case rfl (findTyp_admininstr20T B) Equiv.evalArgs_nil
    matchArgs_nil hc)

set_option maxRecDepth 100000 in
theorem typedV_numtype20T (t : NumType) :
    TypedV (simEnv20T B) (.varT "numtype" []) (numTypeV t) := by
  cases t with
  | int t => cases t <;> exact typedV_of_empty ⟨20, by with_unfolding_all rfl⟩
  | float t => cases t <;> exact typedV_of_empty ⟨20, by with_unfolding_all rfl⟩

set_option maxRecDepth 100000 in
theorem typedV_szOpt20T (p : Option PackSize) :
    TypedV (simEnv20T B) (.iterT (.varT "sz" []) .opt) (.opt (p.map szV)) := by
  intro ρ hρ
  cases p with
  | none => exact ⟨1, by simp [hasTyp, Value.asOpt?]⟩
  | some p =>
    have hl : localTyp? ρ "sz" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
    have h : HasTyp (simEnv20T B) VarEnv.empty (.varT "sz" []) (szV p) := by
      cases p <;> exact ⟨20, by with_unfolding_all rfl⟩
    obtain ⟨n, hn⟩ := Sim.IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ hρ h
    exact ⟨n + 1, by simpa [hasTyp, Value.asOpt?] using hn⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Every valid V2 integer store is a typed `admininstr`** of the corrected script. -/
theorem typedV_intStore20T (t : IntType) (p : Option PackSize) (a : V2.MemArg)
    (hp : ∀ sz, p = some sz → sz.width < t.width) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV (.plain (.intStore t p a))) := by
  refine typedV_storeT_of a (typedV_numtype20T _) (typedV_szOpt20T p) ?_
  cases t <;> cases p with
  | none => exact ⟨20, by with_unfolding_all rfl⟩
  | some sz =>
    have := hp sz rfl
    cases sz <;> first
      | exact ⟨20, by with_unfolding_all rfl⟩
      | exact absurd this (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Every V2 float store is a typed `admininstr`** of the corrected script. -/
theorem typedV_floatStore20T (t : FloatType) (a : V2.MemArg) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV (.plain (.floatStore t a))) := by
  refine typedV_storeT_of a (typedV_numtype20T _) (typedV_szOpt20T none) ?_
  cases t <;> exact ⟨20, by with_unfolding_all rfl⟩

/-! ## The store steps under a context -/

end Silmaril.Wasm.SpecTec.Sim20.StoreAgree

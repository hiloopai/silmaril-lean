module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HostD.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.Thms

/-!
# Round 7, `BD`: the primitives the host rules read

`BD P hn host` answers every name other than `$hostcall` as `withVBytes (Prims.builtins P hn host)`
does (`HostD.bd_call_of_ne`), so as `Prims.builtins P hn host` off `$vbytes_`. The host-call rules
read `$unrolldt` (through `Expand`) and `$lift_result`. This file restates, at `simEnv (BD …)`,
the facts round 5 proved at `simEnv (BI …)`:

* `bd_call_unrolldt`, `bd_call_unrollrt`: `BD`'s answers at `$unrolldt` and `$unrollrt`;
* `applies_unrolldtD`: `$unrolldt` on the image of a defined type is the image of Core's
  `unrolldt` (copy of `Prims.applies_unrolldt`);
* `dderives_expandD`, `callTypesD`: SpecTec's `Expand` on the images of Core's `Expand d ct` for
  bounded `d`, and the typed result types the call rules consume (copies of
  `Round5.Fwd.dderives_expandB` and `callTypesB`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef not_tryClauses_and_undef)
open Silmaril.SpecTec.Equiv.Validation (tyV HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (tyBnd)
open Round7.HostD (BD bd_call_of_ne)
open Round7.MemSimd (withVBytes)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Calls -/

theorem bd_call_unrolldt (v : Value) :
    (BD P hn host).call "unrolldt" [.val v] = Prims.unrolldtCall v := by
  rw [bd_call_of_ne (by decide)]
  simp only [withVBytes, show ("unrolldt" : String) ≠ "vbytes_" by decide, ite_false]
  exact Prims.call_unrolldt hn host v

theorem bd_call_unrollrt (v : Value) : (BD P hn host).call "unrollrt" [.val v] = none := by
  rw [bd_call_of_ne (by decide)]
  simp only [withVBytes, show ("unrollrt" : String) ≠ "vbytes_" by decide, ite_false]
  exact Prims.call_unrollrt hn host v

/-- **`$unrolldt` on an image, at `BD`**: the image of Core's `unrolldt`. -/
theorem applies_unrolldtD (d : DefType) (w : Value) :
    Applies (simEnv (BD P hn host)) "unrolldt" [.val (tyV d)] w ↔
      (unrolldt d).map tyV = some w := by
  have D := Prims.unrollDefs_simEnv (BD P hn host)
  obtain ⟨g, i, rfl⟩ : ∃ g i, d = Ty.defn g i := by cases d; exact ⟨_, _, rfl⟩
  obtain ⟨ps, t, q, body, hd⟩ := D.unrolldt
  obtain ⟨ps', t', cs', hd', hu'⟩ := Prims.unrollrt_undef D (tyV g)
  have hu : TryClausesUndef (simEnv (BD P hn host)) [.defD q [.expA (.caseE "_DEF"
      (.tupE [.varE "rectype", .varE "i"]))] body [Prims.unrolldtPrem]]
      [.val (tyV (Ty.defn g i))] :=
    IntNumeric.tryClausesUndef_skip_prem (Prims.matchArgs_def g i)
      (Prims.premsUndef_if (Prims.evalExpUndef_cmpL
        (Prims.evalExpUndef_call rfl (Equiv.evalArgs_cons (evalExp_var rfl) Equiv.evalArgs_nil) hd' hu'
          (bd_call_unrollrt _)))) IntNumeric.tryClausesUndef_nil
  have hb : (simEnv (BD P hn host)).builtins.call "unrolldt" [.val (tyV (Ty.defn g i))] =
      (unrolldt (Ty.defn g i)).map tyV := by
    rw [simEnv, Env.builtins_withBuiltins, bd_call_unrolldt, Prims.unrolldtCall_tyV]
  constructor
  · rintro ⟨ps₁, t₁, cs₁, hf, hc⟩
    rw [hd] at hf
    cases hf
    rcases hc with hc | ⟨_, hc⟩
    · exact absurd hu (fun h => not_tryClauses_and_undef hc h)
    · rw [← hb, hc]
  · intro h
    exact ⟨ps, t, _, hd, Or.inr ⟨hu, hb.trans h⟩⟩

/-! ## `Expand` and the call types -/

/-- **SpecTec's `Expand` holds of the images of Core's `Expand d ct`, for bounded `d`, at
`BD`.** -/
theorem dderives_expandD (O : ElseI) {d : DefType} {ct : CCompType} (hd : tyBnd d = true)
    (h : Expand d ct) :
    DDerives (simEnv (BD P hn host)) O "Expand" "%~~%" [] (.tuple [tyV d, tyV ct]) := by
  have T := Round5.Int.typesB (BD P hn host)
  obtain ⟨hu⟩ := h
  rename_i fin sups
  have hb : tyBnd sups = true ∧ tyBnd ct = true := Round5.Fwd.tyBnd_of_unrolldt hd hu
  have hρ : ValsOnly (VarEnv.empty.bindVals (Prims.expandσ d fin sups ct)) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt (Prims.hasRuleAt_expand _) (Prims.expandσ d fin sups ct)
    (QuantsOk.cons rfl (T.deftype d hd _ hρ) (QuantsOk.cons rfl (T.comptype ct hb.2 _ hρ)
      (QuantsOk.cons rfl (T.final fin _ hρ) (QuantsOk.cons rfl (T.typeuses sups hb.1 _ hρ)
        QuantsOk.nil))))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) ?_
  intro pr hpr
  simp only [List.mem_singleton] at hpr
  subst hpr
  exact .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_callArgs rfl
    (Equiv.evalArgs_cons (evalExp_var rfl) (evalArgs_nil _ _))
    ((applies_unrolldtD d _).2 (by rw [hu]; rfl)),
    Prims.evalExp_expandSub d fin sups ct, by simp [cmpValues]⟩)

/-- The facts the call rules consume, at `BD`: both result types of a bounded defined type
expanding to a function type are typed, and SpecTec's `Expand` holds of the images. -/
theorem callTypesD {d : DefType} {ps rs : Ty (.list .val)} (hd : tyBnd d = true)
    (hex : Expand d (.func ps rs)) :
    TypedV (simEnv (BD P hn host)) valtypesT (.list (ps.toList.map tyV)) ∧
      TypedV (simEnv (BD P hn host)) valtypesT (.list (rs.toList.map tyV)) ∧
      DDerives (simEnv (BD P hn host)) (otherwise (simEnv (BD P hn host))) "Expand" "%~~%" []
        (.tuple [CT.defType d, funcTypeV ps rs]) := by
  have T := Round5.Int.typesB (BD P hn host)
  have hct : tyBnd ps = true ∧ tyBnd rs = true :=
    Round5.Fwd.tyBnd_func (Round5.Fwd.tyBnd_of_expand hd hex)
  refine ⟨T.valtypes ps hct.1, T.valtypes rs hct.2, ?_⟩
  rw [Prims.funcTypeV_eq]
  exact dderives_expandD _ hd hex

end Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD

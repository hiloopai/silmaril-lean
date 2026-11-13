module

public import Silmaril.Wasm.SpecTec.Institution.Instr30Y.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.Thms
public import Silmaril.Wasm.SpecTec.Institution.Instr30Z.Defs

/-!
# Instruction typing of the wasm-3.0 script, `Instrs_ok/sub` at non-flat types in `{}`

`Instr30Y` fired `Instrs_ok/sub` only towards number and vector types, where
`Valtype_sub` needs no field of the context. In `{}`, round 6's canonical derivations
(`Round6.AgreeOk.subD_of`, at `ctxOf {} = {}`) cover every Core subtyping between bounded valid
types, defined types and their declared supertypes included. This module reads Core's
`ResultSub {}` through them:

* `subB_results`: Core's `ResultSub {} ts ts'` between valid result types is a canonical `SubB`
  derivation (through `Round6.AgreeOk.subB_of_sub` at the function type `[] -> ts`);
* `resulttypeSub_of`: so `Resulttype_sub {}` holds at the images, at every bounded valid pair;
* `dd_subZ`: `Instrs_ok/sub` in `{}` at every bounded valid Core instruction-type subsumption
  without locals, at any value types.
* `fragOkZ_dd`, `fragOkZ_sound`: every `FragOkZ` derivation (`Instr30X.FragOkX` with `sub` at any
  bounded valid types) is an `Instrs_ok {}` fact of `stepModel BI`, and a Core derivation.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV instrtypeV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round4Int (BI)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk (SubB subB_of_sub subD_of resultSub_of recsBnd_empty)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV ctxT_empty typedV_vals)

/-- `{}` has no `RECS`, so they are trivially good. -/
theorem recsGoodB_empty : Round6.AgreeOk.RecsGoodB {} := fun _ _ h => by simp at h

/-- `{}` has no `RECS`, so they are trivially valid. -/
theorem recsOk_empty : ({} : TypeCtx).RecsOk := fun _ _ h => by simp at h

/-- **Core's `ResultSub {}` between valid result types is canonical.** -/
theorem subB_results {ts ts' : List CValType} (hs : ResultSub {} ts ts') (h₁ : ResultOk {} ts)
    (h₂ : ResultOk {} ts') : SubB {} (Ty.ofList ts) (Ty.ofList ts') := by
  have hsub : Sub ({} : TypeCtx) (Ty.func .nil (Ty.ofList ts)) (Ty.func .nil (Ty.ofList ts')) :=
    .func .nil ((ResultSub.iff_sub _ _ _).1 hs)
  have hB : SubB (Round6.AgreeOk.ext {} []) (Ty.func .nil (Ty.ofList ts))
      (Ty.func .nil (Ty.ofList ts')) :=
    subB_of_sub (Δ := {}) rfl recsGoodB_empty recsOk_empty hsub (.func .nil (TyOk.ofList _ h₁))
      (.func .nil (TyOk.ofList _ h₂)) []
  cases hB with
  | func _ hr => exact hr

variable {H : Type} {P : Profile} {hn : H → String} {host : HostSemantics H}

/-- **`Resulttype_sub {}` at Core's `ResultSub {}`**, between bounded valid result types. -/
theorem resulttypeSub_of (O : ElseI) {ts ts' : List CValType}
    (hb₁ : ∀ t ∈ ts, Round4.tyBnd t = true) (hb₂ : ∀ t ∈ ts', Round4.tyBnd t = true)
    (hs : ResultSub {} ts ts') (h₁ : ResultOk {} ts) (h₂ : ResultOk {} ts') :
    DDerivesB (simEnv (BI P hn host)) O "Resulttype_sub" "%|-%<:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, .case "%" (.tuple [.list (ts.map tyV)]),
        .case "%" (.tuple [.list (ts'.map tyV)])]) := by
  have l₁ : Round4.tyBnd (Ty.ofList ts) = true :=
    (Round6.AgreeOk.tyBnd_list_iff _).2 (by simpa using hb₁)
  have l₂ : Round4.tyBnd (Ty.ofList ts') = true :=
    (Round6.AgreeOk.tyBnd_list_iff _).2 (by simpa using hb₂)
  have h := resultSub_of ctxT_empty l₁ l₂
    (subD_of (P := P) (hn := hn) (host := host) O (subB_results hs h₁ h₂) recsBnd_empty l₁ l₂)
  simpa using h

/-- **`Instrs_ok/sub` in `{}` at non-flat types**: from an `Instrs_ok {}` fact at `ps -> rs`, a
Core subsumption `ps -> rs <: ps' -> rs'` without locals between bounded valid instruction types
(of `u32` lengths) gives the fact at `ps' -> rs'`. -/
theorem dd_subZ (O : ElseI) {is : List Value} {ps rs ps' rs' : List CValType}
    (hi : ∀ i ∈ is, TypedV (simEnv (BI P hn host)) (.varT "instr" []) i)
    (hb : Instr30.ItBnd (.plain ps rs)) (hb' : Instr30.ItBnd (.plain ps' rs'))
    (hs : InstrTypeSub {} (.plain ps rs) (.plain ps' rs'))
    (hok : InstrTypeOk {} (.plain ps rs)) (hok' : InstrTypeOk {} (.plain ps' rs'))
    (hlen : ps.length < 2 ^ 32 ∧ rs.length < 2 ^ 32)
    (h : DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, .list is, instrtypeV (.plain ps rs)])) :
    DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, .list is, instrtypeV (.plain ps' rs')]) := by
  have hl₁ : ps'.length = ps.length := List.Forall₂.length_eq hs.1
  have hl₂ : rs.length = rs'.length := List.Forall₂.length_eq hs.2.1
  have hit : TypedV (simEnv (BI P hn host)) (.varT "instrtype" []) (itV (ps.map tyV) [] (rs.map tyV)) :=
    Instr30Y.typedV_itV (by simpa using hlen.1) (by simpa using hlen.2) (typedV_vals hb.1)
      (typedV_vals hb.2)
  have hit' : TypedV (simEnv (BI P hn host)) (.varT "instrtype" [])
      (itV (ps'.map tyV) [] (rs'.map tyV)) :=
    Instr30Y.typedV_itV (by simpa [hl₁] using hlen.1) (by simpa [← hl₂] using hlen.2)
      (typedV_vals hb'.1) (typedV_vals hb'.2)
  have hsub : DDerivesB (simEnv (BI P hn host)) O "Instrtype_sub" "%|-%<:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, itV (ps.map tyV) [] (rs.map tyV),
        itV (ps'.map tyV) [] (rs'.map tyV)]) :=
    Instr30Y.dd_instrtypeSub O ctxT_empty (typedV_vals hb.1) (typedV_vals hb.2) (typedV_vals hb'.1)
      (typedV_vals hb'.2) (resulttypeSub_of O hb'.1 hb.1 hs.1 hok'.1 hok.1)
      (resulttypeSub_of O hb.2 hb'.2 hs.2.1 hok.2.1 hok'.2.1)
  exact Instr30Y.dd_instrsSub O ctxT_empty hi hit hit' h hsub
    (Instr30.instrtypeOk_of P hn host O hb' hok')

/-! ## `FragOkZ` -/

/-- A `FragOkZ` derivation is a Core derivation. -/
theorem fragOkZ_sound {is : List Instr} {it : InstrType} (h : FragOkZ is it) : InstrsOk {} is it := by
  induction h with
  | nil => exact .nil
  | instr _ _ h => exact .instr h
  | seq _ _ _ ih₁ ih₂ => exact .seq ih₁ (fun _ hx => absurd hx List.not_mem_nil) ih₂
  | frame _ hok _ ih => exact .frame ih hok
  | sub _ _ hs _ hok' _ ih => exact .sub ih hs hok'

/-- A `FragOkZ` derivation has bounded types. -/
theorem fragOkZ_bnd {is : List Instr} {it : InstrType} (h : FragOkZ is it) : Instr30.ItBnd it := by
  induction h with
  | nil => exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | instr _ hb _ => exact hb
  | seq _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | frame hb _ _ ih =>
    exact ⟨fun t ht => (List.mem_append.1 ht).elim (hb t) (ih.1 t),
      fun t ht => (List.mem_append.1 ht).elim (hb t) (ih.2 t)⟩
  | sub _ hb' _ _ _ _ _ => exact hb'

/-- The instructions of a `FragOkZ` derivation have typed images. -/
theorem fragOkZ_typed {B : Builtins} {is : List Instr} {it : InstrType} (h : FragOkZ is it) :
    ∀ v ∈ instrsToV is, TypedV (simEnv B) (.varT "instr" []) v := by
  induction h with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | instr hf _ h =>
    intro v hv
    rw [Exn.instrsToV_eq_map] at hv
    obtain rfl := List.mem_singleton.1 hv
    exact Instr30X.typedV_fragX hf h
  | seq _ _ _ ih₁ ih₂ =>
    intro v hv
    rw [Instr30.instrsToV_append] at hv
    exact (List.mem_append.1 hv).elim (ih₁ v) (ih₂ v)
  | frame _ _ _ ih => exact ih
  | sub _ _ _ _ _ _ ih => exact ih

/-- **`FragOkZ` derivations are `Instrs_ok {}` facts** of `simEnv BI`, under every reading of
`otherwise`. -/
theorem fragOkZ_dd (O : ElseI) {is : List Instr} {it : InstrType} (h : FragOkZ is it) :
    DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, .list (instrsToV is), instrtypeV it]) := by
  induction h with
  | nil => exact Instr30.dd_instrsEmpty O ctxT_empty
  | instr hf hb h =>
    exact Instr30.dd_instrsInstr O ctxT_empty (Instr30X.typedV_fragX hf h) (typedV_vals hb.1)
      (fun _ h => absurd h List.not_mem_nil) (typedV_vals hb.2)
      (Instr30X.instrX_preserves' P hn host O hf hb h)
  | @seq is₁ is₂ t₁ t₂ t₃ hb h₁ h₂ ih₁ ih₂ =>
    show DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" [] (.tuple
      [Round6.RefOkV.ctxEmptyV, .list (instrsToV (is₁ ++ is₂)), itV (t₁.map tyV) [] (t₃.map tyV)])
    rw [Instr30.instrsToV_append]
    exact Instr30.dd_instrsSeq O ctxT_empty (fragOkZ_typed h₁) (fragOkZ_typed h₂)
      (typedV_vals (fragOkZ_bnd h₁).1) (typedV_vals hb) (typedV_vals (fragOkZ_bnd h₂).2) ih₁ ih₂
  | @frame is ts t₁ t₂ hb hok h ih =>
    show DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" [] (.tuple
      [Round6.RefOkV.ctxEmptyV, .list (instrsToV is), itV ((ts ++ t₁).map tyV) [] ((ts ++ t₂).map tyV)])
    rw [List.map_append, List.map_append]
    exact Instr30.dd_instrsFrame O ctxT_empty (fragOkZ_typed h) (typedV_vals hb)
      (typedV_vals (fragOkZ_bnd h).1) (typedV_vals (fragOkZ_bnd h).2) ih
      (Instr30.resulttypeOk_of P hn host O hb hok)
  | sub h hb' hs hok hok' hlen ih =>
    exact dd_subZ O (fragOkZ_typed h) (fragOkZ_bnd h) hb' hs hok hok' hlen ih

end Silmaril.Wasm.SpecTec.Institution.Instr30Z

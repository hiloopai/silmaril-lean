module

public import Silmaril.Wasm.SpecTec.Institution.Instr30.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30Inv
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30Seq
public import Silmaril.Wasm.SpecTec.Institution.Typing30.Thms

/-!
# Instruction typing of the wasm-3.0 script against Core 3.0 validation

The model is `stepModel BI`, as in `Typing30`. The judgements are `Instr30.ISen`.

* `valtypeOk_of`, `resulttypeOk_of`, `instrtypeOk_of`: Core-valid bounded value, result and
  instruction types are `Valtype_ok`, `Resulttype_ok`, `Instrtype_ok` facts in `{}`, through
  round 6's canonical validity derivations (`AgreeOk.okD_of`).
* `instr_preserves`: on the domain, an `Instr_ok` judgement Core validates is a fact.
* `fragOk_dd`, `instrs_preserves`: the same for `Instrs_ok` on bounded derivations over the
  reached instructions (`FragOk`: `empty`, `instr`, `seq`, `frame`).
* `nop_sat_iff`: at `nop` the satisfaction condition is exact, for every instruction type
  (`nop_inv`: only `Instr_ok/nop` types `NOP`).
* `drop_shape`, `drop_reflects`: an `Instr_ok {}` fact at `drop` has a type `[t] -> []`, and it
  is Core-valid as soon as `t` is.
* `emptyModule_ok`: Core validates the empty module (the model side is `Task.emptyModuleOk`).
* `drop_nested`: `drop` at `REF NULL D_out` is an `Instr_ok {}` fact while Core rejects it, so
  `Instr_ok` is not reflected (the `Reftype_ok` gap of `Typing30.ok_not_reflects`, one level up).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (tyV instrtypeV)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading

variable {H : Type} (P : Profile) (hn : H → String) (host : HostSemantics H)

/-- The model of the comorphism: `stepModel` at the concrete primitives `BI`. -/
local notation "MB" => Wasm30.stepModel (Round4Int.BI P hn host)

/-- Its evaluator. -/
local notation "EB" => simEnv (Round4Int.BI P hn host)

/-- `{}` is a typed context. -/
theorem ctxT_empty {B : Builtins} : Round6.AgreeSub.CtxT B Round6.RefOkV.ctxEmptyV :=
  Round6.RefOkB.typedV_ctxR fun _ h => absurd h List.not_mem_nil

/-- A bounded value type has a typed image. -/
theorem typedV_val {B : Builtins} {t : CValType} (hb : Round4.tyBnd t = true) :
    TypedV (simEnv B) (.varT "valtype" []) (tyV t) := (Round5.Pos.tyT_tyV t hb).1

/-- Bounded value types have typed images. -/
theorem typedV_vals {B : Builtins} {ts : List CValType} (hb : ∀ t ∈ ts, Round4.tyBnd t = true) :
    ∀ v ∈ ts.map tyV, TypedV (simEnv B) (.varT "valtype" []) v := by
  intro v hv
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
  exact typedV_val (hb t ht)

/-- **A bounded, Core-valid value type is a `Valtype_ok {}` fact.** -/
theorem valtypeOk_of (O : ElseI) {t : CValType} (hb : Round4.tyBnd t = true) (h : TyOk {} t) :
    DDerivesB (EB) O "Valtype_ok" "%|-%:OK" [] (.tuple [Round6.RefOkV.ctxEmptyV, tyV t]) :=
  Round6.AgreeOk.okD_of O (Round6.AgreeOk.tyOkB_empty h hb) Round6.AgreeOk.recsBnd_empty hb

/-- **A bounded, Core-valid result type is a `Resulttype_ok {}` fact.** -/
theorem resulttypeOk_of (O : ElseI) {ts : List CValType} (hb : ∀ t ∈ ts, Round4.tyBnd t = true)
    (h : ResultOk {} ts) :
    DDerivesB (EB) O "Resulttype_ok" "%|-%:OK" []
      (.tuple [Round6.RefOkV.ctxEmptyV, .case "%" (.tuple [.list (ts.map tyV)])]) :=
  Round6.AgreeOk.dd_resulttypeOk O ctxT_empty (typedV_vals hb) fun v hv => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
    exact valtypeOk_of P hn host O (hb t ht) (h t ht)

/-- **A bounded, Core-valid instruction type without initialised locals is an
`Instrtype_ok {}` fact.** -/
theorem instrtypeOk_of (O : ElseI) {ps rs : List CValType} (hb : ItBnd (.plain ps rs))
    (h : InstrTypeOk {} (.plain ps rs)) :
    DDerivesB (EB) O "Instrtype_ok" "%|-%:OK" []
      (.tuple [Round6.RefOkV.ctxEmptyV, instrtypeV (.plain ps rs)]) :=
  dd_instrtypeOk O ctxT_empty (typedV_vals hb.1) (typedV_vals hb.2)
    (resulttypeOk_of P hn host O hb.1 h.1) (resulttypeOk_of P hn host O hb.2 h.2.1)

/-- `instrToV` at the reached instructions. -/
theorem instrToV_nop : instrToV .nop = .case "NOP" (.tuple []) := rfl

/-- `instrToV` at the reached instructions. -/
theorem instrToV_unreachable : instrToV .unreachable = .case "UNREACHABLE" (.tuple []) := rfl

/-- `instrToV` at the reached instructions. -/
theorem instrToV_drop : instrToV .drop = .case "DROP" (.tuple []) := rfl

/-- `Instr_ok {}` at `nop`. -/
theorem instr_nop (O : ElseI) {it : InstrType} (h : InstrOk {} .nop it) :
    DDerivesB (EB) O "Instr_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, instrToV .nop, instrtypeV it]) := by
  cases h with
  | parametric h => cases h; exact dd_nop _ ctxT_empty
  | numeric h => nomatch h
  | vector h => nomatch h
  | «variable» h => nomatch h
  | memory h => nomatch h
  | table h => nomatch h
  | reference h => nomatch h

/-- `Instr_ok {}` at `unreachable`. -/
theorem instr_unreachable (O : ElseI) {it : InstrType} (hb : ItBnd it)
    (h : InstrOk {} .unreachable it) :
    DDerivesB (EB) O "Instr_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, instrToV .unreachable, instrtypeV it]) := by
  cases h with
  | parametric h =>
    cases h with
    | unreachable hok =>
      exact dd_unreachable _ ctxT_empty (typedV_vals hb.1) (typedV_vals hb.2)
        (instrtypeOk_of P hn host _ hb hok)
  | numeric h => nomatch h
  | vector h => nomatch h
  | «variable» h => nomatch h
  | memory h => nomatch h
  | table h => nomatch h
  | reference h => nomatch h

/-- `Instr_ok {}` at `drop`. -/
theorem instr_drop (O : ElseI) {it : InstrType} (hb : ItBnd it) (h : InstrOk {} .drop it) :
    DDerivesB (EB) O "Instr_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, instrToV .drop, instrtypeV it]) := by
  cases h with
  | parametric h =>
    cases h with
    | @drop t hok =>
      have ht : Round4.tyBnd t = true := hb.1 t (List.mem_singleton_self t)
      exact dd_drop _ ctxT_empty (typedV_val ht) (valtypeOk_of P hn host _ ht hok)
  | numeric h => nomatch h
  | vector h => nomatch h
  | «variable» h => nomatch h
  | memory h => nomatch h
  | table h => nomatch h
  | reference h => nomatch h

/-- `Instr_ok {}` at a reached instruction and a bounded type, under every reading of
`otherwise`. -/
theorem instr_preserves' (O : ElseI) {i : Instr} {it : InstrType} (hf : frag i = true)
    (hb : ItBnd it) (h : InstrOk {} i it) :
    DDerivesB (EB) O "Instr_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, instrToV i, instrtypeV it]) := by
  cases i <;> simp only [frag, Bool.false_eq_true] at hf
  · exact instr_nop P hn host O h
  · exact instr_unreachable P hn host O hb h
  · exact instr_drop P hn host O hb h

/-- **Core validation is preserved** for `Instr_ok`: on the domain, a judgement that Core
validates is a fact of `stepModel BI`. -/
theorem instr_preserves {i : Instr} {it : InstrType} (hd : (ISen.instr i it).Dom)
    (h : (ISen.instr i it).Holds) : ((ISen.instr i it).toSen).Sat backend (MB).env (MB).D :=
  instr_preserves' P hn host _ hd.1 hd.2 h

/-! ## Reflection at `nop` and `drop` -/

/-- An instruction type whose image is `[] -> []` is `[] -> []`. -/
theorem instrtypeV_nil {it : InstrType} (h : instrtypeV it = itV [] [] []) : it = .plain [] [] := by
  obtain ⟨ps, xs, rs⟩ := it
  simp only [instrtypeV_eq, itV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
    Value.list.injEq, List.map_eq_nil_iff, true_and, and_true] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- An instruction type whose image is `[u] -> []` is `[t] -> []` with `tyV t = u`. -/
theorem instrtypeV_one {it : InstrType} {u : Value} (h : instrtypeV it = itV [u] [] []) :
    ∃ t, it = .plain [t] [] ∧ tyV t = u := by
  obtain ⟨ps, xs, rs⟩ := it
  simp only [instrtypeV_eq, itV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
    Value.list.injEq, List.map_eq_nil_iff, List.map_eq_singleton_iff, true_and, and_true] at h
  obtain ⟨⟨t, rfl, rfl⟩, rfl, rfl⟩ := h
  exact ⟨t, rfl, rfl⟩

/-- **`nop` is reflected**: an `Instr_ok {}` fact at `nop` is Core-valid. -/
theorem nop_reflects {it : InstrType}
    (h : ((ISen.instr .nop it).toSen).Sat backend (MB).env (MB).D) : (ISen.instr .nop it).Holds := by
  obtain rfl := instrtypeV_nil (nop_inv h)
  exact .parametric .nop

/-- **The satisfaction condition at `nop`**, at every instruction type. -/
theorem nop_sat_iff {it : InstrType} :
    ((ISen.instr .nop it).toSen).Sat backend (MB).env (MB).D ↔ (ISen.instr .nop it).Holds :=
  ⟨nop_reflects P hn host, instr_nop P hn host _⟩

/-- An `Instr_ok {}` fact at `drop` has a type `[t] -> []`, with `Valtype_ok {}` at `t`. -/
theorem drop_shape {it : InstrType}
    (h : ((ISen.instr .drop it).toSen).Sat backend (MB).env (MB).D) :
    ∃ t, it = .plain [t] [] ∧
      DDerivesB (EB) (otherwiseB (EB)) "Valtype_ok" "%|-%:OK" [] (.tuple [Round6.RefOkV.ctxEmptyV, tyV t]) := by
  obtain ⟨u, hu, hv⟩ := drop_inv h
  obtain ⟨t, rfl, rfl⟩ := instrtypeV_one hu
  exact ⟨t, rfl, hv⟩

/-- **`drop` is reflected at Core-valid types**: an `Instr_ok {}` fact at `drop` whose parameter
types Core validates is Core-valid. -/
theorem drop_reflects {it : InstrType}
    (h : ((ISen.instr .drop it).toSen).Sat backend (MB).env (MB).D)
    (hok : ∀ t ∈ it.params, TyOk {} t) : (ISen.instr .drop it).Holds := by
  obtain ⟨t, rfl, -⟩ := drop_shape P hn host h
  exact .parametric (.drop (hok t (List.mem_singleton_self t)))

/-! ## Sequences -/

set_option maxRecDepth 100000 in
/-- A reached instruction has a typed image. -/
theorem typedV_frag {B : Builtins} {i : Instr} (hf : frag i = true) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV i) := by
  cases i <;> simp only [frag, Bool.false_eq_true] at hf
  · exact Typing.typedV_closedCase (IntNumeric.findTyp_instr' B) rfl hasTyp_tupT_nil
  · exact Typing.typedV_closedCase (IntNumeric.findTyp_instr' B) rfl hasTyp_tupT_nil
  · exact Typing.typedV_closedCase (IntNumeric.findTyp_instr' B) rfl hasTyp_tupT_nil

/-- A `FragOk` derivation is a Core derivation. -/
theorem fragOk_sound {is : List Instr} {it : InstrType} (h : FragOk is it) : InstrsOk {} is it := by
  induction h with
  | nil => exact .nil
  | instr _ _ h => exact .instr h
  | seq _ _ _ ih₁ ih₂ => exact .seq ih₁ (fun _ hx => absurd hx List.not_mem_nil) ih₂
  | frame _ hok _ ih => exact .frame ih hok

/-- A `FragOk` derivation has bounded types. -/
theorem fragOk_bnd {is : List Instr} {it : InstrType} (h : FragOk is it) : ItBnd it := by
  induction h with
  | nil => exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | instr _ hb _ => exact hb
  | seq _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | frame hb _ _ ih =>
    exact ⟨fun t ht => (List.mem_append.1 ht).elim (hb t) (ih.1 t),
      fun t ht => (List.mem_append.1 ht).elim (hb t) (ih.2 t)⟩

/-- A `FragOk` derivation is over reached instructions. -/
theorem fragOk_frag {is : List Instr} {it : InstrType} (h : FragOk is it) :
    ∀ i ∈ is, frag i = true := by
  induction h with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | instr hf _ _ => exact fun _ h => (List.mem_singleton.1 h) ▸ hf
  | seq _ _ _ ih₁ ih₂ => exact fun i h => (List.mem_append.1 h).elim (ih₁ i) (ih₂ i)
  | frame _ _ _ ih => exact ih

/-- The images of reached instructions are typed. -/
theorem typedV_frags {B : Builtins} {is : List Instr} (h : ∀ i ∈ is, frag i = true) :
    ∀ v ∈ instrsToV is, TypedV (simEnv B) (.varT "instr" []) v := by
  intro v hv
  rw [Exn.instrsToV_eq_map] at hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
  exact typedV_frag (h i hi)

/-- `instrsToV` on a concatenation. -/
theorem instrsToV_append (is₁ is₂ : List Instr) :
    instrsToV (is₁ ++ is₂) = instrsToV is₁ ++ instrsToV is₂ := by
  simp only [Exn.instrsToV_eq_map, List.map_append]

/-- The image of `t₁ -> t₂`. -/
theorem instrtypeV_plain (ps rs : List CValType) :
    instrtypeV (.plain ps rs) = itV (ps.map tyV) [] (rs.map tyV) := rfl

/-- **`FragOk` derivations are read by `DDerivesB`.** -/
theorem fragOk_dd (O : ElseI) {is : List Instr} {it : InstrType} (h : FragOk is it) :
    DDerivesB (EB) O "Instrs_ok" "%|-%:%" []
      (.tuple [Round6.RefOkV.ctxEmptyV, .list (instrsToV is), instrtypeV it]) := by
  induction h with
  | nil => exact dd_instrsEmpty O ctxT_empty
  | instr hf hb h =>
    exact dd_instrsInstr O ctxT_empty (typedV_frag hf) (typedV_vals hb.1)
      (fun _ h => absurd h List.not_mem_nil) (typedV_vals hb.2) (instr_preserves' P hn host O hf hb h)
  | @seq is₁ is₂ t₁ t₂ t₃ hb h₁ h₂ ih₁ ih₂ =>
    show DDerivesB (EB) O "Instrs_ok" "%|-%:%" [] (.tuple [Round6.RefOkV.ctxEmptyV,
      .list (instrsToV (is₁ ++ is₂)), itV (t₁.map tyV) [] (t₃.map tyV)])
    rw [instrsToV_append]
    exact dd_instrsSeq O ctxT_empty (typedV_frags (fragOk_frag h₁)) (typedV_frags (fragOk_frag h₂))
      (typedV_vals (fragOk_bnd h₁).1) (typedV_vals hb) (typedV_vals (fragOk_bnd h₂).2) ih₁ ih₂
  | @frame is ts t₁ t₂ hb hok h ih =>
    show DDerivesB (EB) O "Instrs_ok" "%|-%:%" [] (.tuple [Round6.RefOkV.ctxEmptyV,
      .list (instrsToV is), itV ((ts ++ t₁).map tyV) [] ((ts ++ t₂).map tyV)])
    rw [List.map_append, List.map_append]
    exact dd_instrsFrame O ctxT_empty (typedV_frags (fragOk_frag h)) (typedV_vals hb)
      (typedV_vals (fragOk_bnd h).1) (typedV_vals (fragOk_bnd h).2) ih
      (resulttypeOk_of P hn host O hb hok)

/-- **Core validation is preserved** for `Instrs_ok` on its domain, the bounded derivations over
reached instructions. -/
theorem instrs_preserves {is : List Instr} {it : InstrType} (hd : (ISen.instrs is it).Dom) :
    ((ISen.instrs is it).toSen).Sat backend (MB).env (MB).D :=
  fragOk_dd P hn host _ hd

/-- `instrs` judgements in the domain hold in Core. -/
theorem instrs_holds {is : List Instr} {it : InstrType} (hd : (ISen.instrs is it).Dom) :
    (ISen.instrs is it).Holds :=
  fragOk_sound hd

/-- `unreachable drop` at `[] -> []`, through the intermediate stack `[i32]`: a `FragOk`
derivation that uses `Instrs_ok/seq`. -/
theorem fragOk_unreachableDrop : FragOk [.unreachable, .drop] (.plain [] []) :=
  have hb : ∀ t ∈ [Ty.i32], Round4.tyBnd t = true := fun _ ht => (List.mem_singleton.1 ht) ▸ rfl
  have hok : ResultOk {} [Ty.i32] := fun _ ht => (List.mem_singleton.1 ht) ▸ TyOk.num _
  FragOk.seq (is₁ := [.unreachable]) (is₂ := [.drop]) hb
    (.instr rfl ⟨fun _ h => absurd h List.not_mem_nil, hb⟩
      (.parametric (.unreachable ⟨fun _ h => absurd h List.not_mem_nil, hok,
        fun _ h => absurd h List.not_mem_nil⟩)))
    (.instr rfl ⟨hb, fun _ h => absurd h List.not_mem_nil⟩
      (.parametric (.drop (hok _ (List.mem_singleton_self _)))))

/-- **Non-vacuity**: `unreachable drop` at `[] -> []` is an `Instrs_ok {}` fact of
`stepModel BI` and Core-valid. -/
theorem unreachableDrop :
    ((ISen.instrs [.unreachable, .drop] (.plain [] [])).toSen).Sat backend (MB).env (MB).D ∧
      (ISen.instrs [.unreachable, .drop] (.plain [] [])).Holds :=
  ⟨instrs_preserves P hn host fragOk_unreachableDrop, instrs_holds fragOk_unreachableDrop⟩

/-! ## Not reflected -/

/-- `drop` at `REF NULL D_out`, the type round 6 found valid in the script and invalid in Core. -/
def dropNested : ISen := .instr .drop (.plain [.refv Round5.RefOk.nestedRT] [])

/-- Core rejects `drop` at `REF NULL D_out`. -/
theorem not_dropNested : ¬ dropNested.Holds := by
  intro h
  cases h with
  | parametric h =>
    cases h with
    | drop hok =>
      cases hok with
      | refv hr => exact Round5.RefOk.not_tyOk_nested hr
  | numeric h => nomatch h
  | vector h => nomatch h
  | «variable» h => nomatch h
  | memory h => nomatch h
  | table h => nomatch h
  | reference h => nomatch h

/-- `REF NULL D_out` is bounded, as a value type. -/
theorem tyBnd_nestedV : Round4.tyBnd (Ty.refv Round5.RefOk.nestedRT) = true :=
  Round6.RefOkB.tyBnd_nested

/-- `drop` at `REF NULL D_out` is in the domain. -/
theorem dropNested_dom : dropNested.Dom :=
  ⟨rfl, fun _ ht => (List.mem_singleton.1 ht) ▸ tyBnd_nestedV,
    fun _ ht => absurd ht List.not_mem_nil⟩

/-- **`Instr_ok` is not reflected**: `drop` at `REF NULL D_out` is in the domain and an
`Instr_ok {}` fact of `stepModel BI`, and Core rejects it. -/
theorem drop_nested :
    dropNested.Dom ∧ (dropNested.toSen).Sat backend (MB).env (MB).D ∧ ¬ dropNested.Holds :=
  ⟨dropNested_dom, dd_drop _ ctxT_empty (typedV_val tyBnd_nestedV)
    (Round6.RefOkB.dderivesB_valtypeOkRef _ ctxT_empty
      (Round6.Reading.typedV_reftype Round6.RefOkB.tyBnd_nested)
      (Round6.RefOkB.dderivesB_reftypeOk_nested _)), not_dropNested⟩

/-! ## The empty module -/

/-- **Core validates the empty module** at `[] -> []`. -/
theorem emptyModule_ok : ModuleOk {} ⟨[], []⟩ :=
  .mk (dts := []) (xtI := []) (jts := []) (gts := []) (tts := []) (fdts := []) (rts := [])
    (xtE := []) .nil .nil rfl rfl .nil .nil (fun _ h => absurd h List.not_mem_nil) .nil .nil
    (fun _ h => absurd h List.not_mem_nil) .nil (fun _ h => nomatch h) .nil
    List.nodup_nil

end Silmaril.Wasm.SpecTec.Institution.Instr30

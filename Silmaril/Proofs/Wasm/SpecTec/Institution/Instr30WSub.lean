module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30WTrans
public import Silmaril.Wasm.SpecTec.Institution.Instr30Z.Thms

/-!
# Instruction typing of the wasm-3.0 script, `frame` and `sub` at non-flat types under locals and globals

`Instr30Y` fired `Instrs_ok/frame` and `Instrs_ok/sub` in `{locals := L, globals := G}`
only at flat types, and `Instr30Z` fired them at any bounded valid types only in `{}`.
With `Instr30WTrans`'s `okDX_of` and `subDX_of` read at `ctxOfX ls gs {} = ctxLGV L G`:

* `valtypeOkLG_of`, `resulttypeOkLG_of`, `instrtypeOkLG_of`: every bounded Core-valid value,
  result and instruction type is a `Valtype_ok`, `Resulttype_ok`, `Instrtype_ok` fact in
  `ctxLGV L G`;
* `resulttypeSubLG_of`: every Core `ResultSub` between bounded valid result types is a
  `Resulttype_sub` fact there;
* `dd_frameW`, `dd_subW`: so `Instrs_ok/frame` and `Instrs_ok/sub` fire there at any bounded valid
  types;
* `fragOkW_sound`, `fragOkW_dd`: every `FragOkW L G` derivation is a Core derivation in
  `{locals := L, globals := G}` and an `Instrs_ok` fact of `stepModel BI` in `ctxLGV L G`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30W

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
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk (recsBnd_empty tyOkB_empty resultSub_of)
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (CtxT)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV ItBnd typedV_vals)
open Silmaril.Wasm.SpecTec.Institution.Instr30Y (ctxLoc ctxLGV CtxBnd ctxT_lg globalV)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (localV)

variable {H : Type} {P : Profile} {hn : H → String} {host : HostSemantics H}

/-! ## Types -/

/-- The images of bounded locals are `localtype`s. -/
theorem localsT {B : Builtins} {L : List LocalType} {G : List CGlobalType} (hb : CtxBnd L G) :
    ∀ u ∈ L.map localV, TypedV (simEnv B) (.varT "localtype" []) u := fun u hu => by
  obtain ⟨lt, hlt, rfl⟩ := List.mem_map.1 hu
  exact Instr30X.typedV_localV (hb.1 lt hlt)

/-- The images of bounded globals are `globaltype`s. -/
theorem globalsT {B : Builtins} {L : List LocalType} {G : List CGlobalType} (hb : CtxBnd L G) :
    ∀ u ∈ G.map globalV, TypedV (simEnv B) (.varT "globaltype" []) u := fun u hu => by
  obtain ⟨gt, hgt, rfl⟩ := List.mem_map.1 hu
  exact Instr30Y.typedV_globalV (hb.2 gt hgt)

/-- **A bounded, Core-valid value type is a `Valtype_ok` fact in `ctxLGV L G`.** -/
theorem valtypeOkLG_of (O : ElseI) {L : List LocalType} {G : List CGlobalType} (hcb : CtxBnd L G)
    {t : CValType} (hb : Round4.tyBnd t = true) (h : TyOk {} t) :
    DDerivesB (simEnv (BI P hn host)) O "Valtype_ok" "%|-%:OK" [] (.tuple [ctxLGV L G, tyV t]) :=
  okDX_of O (localsT hcb) (globalsT hcb) (tyOkB_empty h hb) recsBnd_empty hb

/-- **A bounded, Core-valid result type is a `Resulttype_ok` fact in `ctxLGV L G`.** -/
theorem resulttypeOkLG_of (O : ElseI) {L : List LocalType} {G : List CGlobalType}
    (hcb : CtxBnd L G) {ts : List CValType} (hb : ∀ t ∈ ts, Round4.tyBnd t = true)
    (h : ResultOk {} ts) :
    DDerivesB (simEnv (BI P hn host)) O "Resulttype_ok" "%|-%:OK" []
      (.tuple [ctxLGV L G, .case "%" (.tuple [.list (ts.map tyV)])]) :=
  Round6.AgreeOk.dd_resulttypeOk O (ctxT_lg hcb) (typedV_vals hb) fun v hv => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
    exact valtypeOkLG_of O hcb (hb t ht) (h t ht)

/-- **A bounded, Core-valid instruction type without initialised locals is an `Instrtype_ok`
fact in `ctxLGV L G`.** -/
theorem instrtypeOkLG_of (O : ElseI) {L : List LocalType} {G : List CGlobalType}
    (hcb : CtxBnd L G) {ps rs : List CValType} (hb : ItBnd (.plain ps rs))
    (h : InstrTypeOk (ctxLoc L G) (.plain ps rs)) :
    DDerivesB (simEnv (BI P hn host)) O "Instrtype_ok" "%|-%:OK" []
      (.tuple [ctxLGV L G, instrtypeV (.plain ps rs)]) :=
  Instr30.dd_instrtypeOk O (ctxT_lg hcb) (typedV_vals hb.1) (typedV_vals hb.2)
    (resulttypeOkLG_of O hcb hb.1 h.1) (resulttypeOkLG_of O hcb hb.2 h.2.1)

/-- **`Resulttype_sub` in `ctxLGV L G` at Core's `ResultSub {}`**, between bounded valid result
types. -/
theorem resulttypeSubLG_of (O : ElseI) {L : List LocalType} {G : List CGlobalType}
    (hcb : CtxBnd L G) {ts ts' : List CValType}
    (hb₁ : ∀ t ∈ ts, Round4.tyBnd t = true) (hb₂ : ∀ t ∈ ts', Round4.tyBnd t = true)
    (hs : ResultSub {} ts ts') (h₁ : ResultOk {} ts) (h₂ : ResultOk {} ts') :
    DDerivesB (simEnv (BI P hn host)) O "Resulttype_sub" "%|-%<:%" []
      (.tuple [ctxLGV L G, .case "%" (.tuple [.list (ts.map tyV)]),
        .case "%" (.tuple [.list (ts'.map tyV)])]) := by
  have l₁ : Round4.tyBnd (Silmaril.Wasm.Validation.Ty.ofList ts) = true :=
    (Round6.AgreeOk.tyBnd_list_iff _).2 (by simpa using hb₁)
  have l₂ : Round4.tyBnd (Silmaril.Wasm.Validation.Ty.ofList ts') = true :=
    (Round6.AgreeOk.tyBnd_list_iff _).2 (by simpa using hb₂)
  have h := resultSub_of (ctxT_lg hcb) l₁ l₂
    (subDX_of (P := P) (hn := hn) (host := host) O (localsT hcb) (globalsT hcb)
      (Instr30Z.subB_results hs h₁ h₂) recsBnd_empty l₁ l₂)
  simpa using h

/-! ## `frame` and `sub` -/

/-- **`Instrs_ok/frame` in `ctxLGV L G` at any bounded valid frame.** -/
theorem dd_frameW (O : ElseI) {L : List LocalType} {G : List CGlobalType} (hcb : CtxBnd L G)
    {is : List Value} {ts t₁ t₂ : List CValType}
    (hi : ∀ i ∈ is, TypedV (simEnv (BI P hn host)) (.varT "instr" []) i)
    (hb : ∀ t ∈ ts, Round4.tyBnd t = true) (hb₁ : ∀ t ∈ t₁, Round4.tyBnd t = true)
    (hb₂ : ∀ t ∈ t₂, Round4.tyBnd t = true) (hok : ResultOk {} ts)
    (h : DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" []
      (.tuple [ctxLGV L G, .list is, itV (t₁.map tyV) [] (t₂.map tyV)])) :
    DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" []
      (.tuple [ctxLGV L G, .list is, itV ((ts ++ t₁).map tyV) [] ((ts ++ t₂).map tyV)]) := by
  rw [List.map_append, List.map_append]
  exact Instr30.dd_instrsFrame O (ctxT_lg hcb) hi (typedV_vals hb) (typedV_vals hb₁)
    (typedV_vals hb₂) h (resulttypeOkLG_of O hcb hb hok)

/-- **`Instrs_ok/sub` in `ctxLGV L G` at any bounded valid types**: from an `Instrs_ok` fact at
`ps -> rs`, a Core subsumption `ps -> rs <: ps' -> rs'` in `{locals := L, globals := G}` between
bounded valid instruction types without initialised locals gives the fact at `ps' -> rs'`. -/
theorem dd_subW (O : ElseI) {L : List LocalType} {G : List CGlobalType} (hcb : CtxBnd L G)
    {is : List Value} {ps rs ps' rs' : List CValType}
    (hi : ∀ i ∈ is, TypedV (simEnv (BI P hn host)) (.varT "instr" []) i)
    (hb : ItBnd (.plain ps rs)) (hb' : ItBnd (.plain ps' rs'))
    (hs : InstrTypeSub (ctxLoc L G) (.plain ps rs) (.plain ps' rs'))
    (hok : InstrTypeOk (ctxLoc L G) (.plain ps rs)) (hok' : InstrTypeOk (ctxLoc L G) (.plain ps' rs'))
    (hlen : ps.length < 2 ^ 32 ∧ rs.length < 2 ^ 32)
    (h : DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" []
      (.tuple [ctxLGV L G, .list is, instrtypeV (.plain ps rs)])) :
    DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" []
      (.tuple [ctxLGV L G, .list is, instrtypeV (.plain ps' rs')]) := by
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
      (.tuple [ctxLGV L G, itV (ps.map tyV) [] (rs.map tyV), itV (ps'.map tyV) [] (rs'.map tyV)]) :=
    Instr30Y.dd_instrtypeSub O (ctxT_lg hcb) (typedV_vals hb.1) (typedV_vals hb.2)
      (typedV_vals hb'.1) (typedV_vals hb'.2)
      (resulttypeSubLG_of O hcb hb'.1 hb.1 hs.1 hok'.1 hok.1)
      (resulttypeSubLG_of O hcb hb.2 hb'.2 hs.2.1 hok.2.1 hok'.2.1)
  exact Instr30Y.dd_instrsSub O (ctxT_lg hcb) hi hit hit' h hsub (instrtypeOkLG_of O hcb hb' hok')

/-! ## `FragOkW` -/

/-- A `FragOkW` derivation is a Core derivation in `{locals := L, globals := G}`. -/
theorem fragOkW_sound {L : List LocalType} {G : List CGlobalType} {is : List Instr}
    {it : InstrType} (h : FragOkW L G is it) : InstrsOk (ctxLoc L G) is it := by
  induction h with
  | nil => exact .nil
  | instr _ _ _ h => exact .instr h
  | seq _ _ _ ih₁ ih₂ => exact .seq ih₁ (fun _ hx => absurd hx List.not_mem_nil) ih₂
  | frame _ hok _ ih => exact .frame ih hok
  | sub _ _ hs _ hok' _ ih => exact .sub ih hs hok'

/-- A `FragOkW` derivation has bounded types. -/
theorem fragOkW_bnd {L : List LocalType} {G : List CGlobalType} {is : List Instr} {it : InstrType}
    (h : FragOkW L G is it) : ItBnd it := by
  induction h with
  | nil => exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | instr _ hb _ _ => exact hb
  | seq _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | frame hb _ _ ih =>
    exact ⟨fun t ht => (List.mem_append.1 ht).elim (hb t) (ih.1 t),
      fun t ht => (List.mem_append.1 ht).elim (hb t) (ih.2 t)⟩
  | sub _ hb' _ _ _ _ _ => exact hb'

/-- The instructions of a `FragOkW` derivation have typed images. -/
theorem fragOkW_typed {B : Builtins} {L : List LocalType} {G : List CGlobalType} {is : List Instr}
    {it : InstrType} (h : FragOkW L G is it) :
    ∀ v ∈ instrsToV is, TypedV (simEnv B) (.varT "instr" []) v := by
  induction h with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | instr hf _ _ h =>
    intro v hv
    rw [Exn.instrsToV_eq_map] at hv
    obtain rfl := List.mem_singleton.1 hv
    exact Instr30Y.typedV_fragY hf h
  | seq _ _ _ ih₁ ih₂ =>
    intro v hv
    rw [Instr30.instrsToV_append] at hv
    exact (List.mem_append.1 hv).elim (ih₁ v) (ih₂ v)
  | frame _ _ _ ih => exact ih
  | sub _ _ _ _ _ _ ih => exact ih

/-- `Instrs_ok/instr` at a reached instruction, in `ctxLGV L G`. -/
theorem dd_instrW (O : ElseI) {L : List LocalType} {G : List CGlobalType} (hcb : CtxBnd L G)
    {i : Instr} {it : InstrType} (hf : Instr30Y.fragY i = true) (hb : ItBnd it)
    (hp : Instr30Y.ParamOk i it) (h : InstrOk (ctxLoc L G) i it) :
    DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" []
      (.tuple [ctxLGV L G, .list (instrsToV [i]), instrtypeV it]) := by
  rw [Instr30.instrtypeV_eq]
  exact Instr30.dd_instrsInstr O (ctxT_lg hcb) (Instr30Y.typedV_fragY hf h) (typedV_vals hb.1)
    (fun v hv => by
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hv
      obtain ⟨x, rfl⟩ := Instr30Y.inits_fragY hf h n hn
      exact Typing.typedV_idx x)
    (typedV_vals hb.2) (Instr30Y.instrY_preserves O hcb hf hp h)

/-- **`FragOkW` derivations are `Instrs_ok` facts** of `simEnv BI` in `ctxLGV L G`, under every
reading of `otherwise`. -/
theorem fragOkW_dd (O : ElseI) {L : List LocalType} {G : List CGlobalType} (hcb : CtxBnd L G)
    {is : List Instr} {it : InstrType} (h : FragOkW L G is it) :
    DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" []
      (.tuple [ctxLGV L G, .list (instrsToV is), instrtypeV it]) := by
  induction h with
  | nil => exact Instr30.dd_instrsEmpty O (ctxT_lg hcb)
  | instr hf hb hp h => exact dd_instrW O hcb hf hb hp h
  | @seq is₁ is₂ t₁ t₂ t₃ hb h₁ h₂ ih₁ ih₂ =>
    show DDerivesB (simEnv (BI P hn host)) O "Instrs_ok" "%|-%:%" [] (.tuple [ctxLGV L G,
      .list (instrsToV (is₁ ++ is₂)), itV (t₁.map tyV) [] (t₃.map tyV)])
    rw [Instr30.instrsToV_append]
    exact Instr30.dd_instrsSeq O (ctxT_lg hcb) (fragOkW_typed h₁) (fragOkW_typed h₂)
      (typedV_vals (fragOkW_bnd h₁).1) (typedV_vals hb) (typedV_vals (fragOkW_bnd h₂).2) ih₁ ih₂
  | frame hb hok h ih =>
    exact dd_frameW O hcb (fragOkW_typed h) hb (fragOkW_bnd h).1 (fragOkW_bnd h).2 hok ih
  | sub h hb' hs hok hok' hlen ih =>
    exact dd_subW O hcb (fragOkW_typed h) (fragOkW_bnd h) hb' hs hok hok' hlen ih

end Silmaril.Wasm.SpecTec.Institution.Instr30W

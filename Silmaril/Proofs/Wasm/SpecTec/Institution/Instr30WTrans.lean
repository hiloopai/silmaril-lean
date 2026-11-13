module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30WCtx

/-!
# Instruction typing of the wasm-3.0 script, round 6's canonical derivations under locals and globals

`okDX_of`, `subOk2DX_of`, `groupDX_of`, `subDX_of`: round 6's mutual structural recursion
(`Round6.AgreeOk.okD_of` …, `AgreeOk/Trans.lean`), copied with the context `ctxOf Δ` replaced by
`ctxOfX ls gs Δ = {LOCALS ls, GLOBALS gs, RECS Δ.recs}`. Every rule lemma round 6 states for an
arbitrary typed context is reused as it is; the ones that read `RECS` are `Instr30WCtx`'s
restatements. So every canonical validity and subtyping derivation is read by `DDerivesB` in every
context with typed locals and globals, not only in `ctxOf Δ`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30W

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_list natV absV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (CtxT)
open Silmaril.Wasm.SpecTec.Sim.Round4Int (BI)
open Silmaril.Wasm.SpecTec.Sim.Round4 (tyBnd)

variable {B : Builtins} {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Contexts -/

/-- The SpecTec context of `Δ` under locals `ls` and globals `gs`. -/
def ctxOfX (ls gs : List Value) (Δ : TypeCtx) : Value := ctxRX ls gs (Δ.recs.map tyV)

/-- `ctxOfX ls gs Δ` is a typed context when its locals, globals and `RECS` are. -/
theorem ctxT_ofX {ls gs : List Value} (hl : ∀ u ∈ ls, TypedV (simEnv B) (.varT "localtype" []) u)
    (hg : ∀ u ∈ gs, TypedV (simEnv B) (.varT "globaltype" []) u) {Δ : TypeCtx} (h : RecsBnd Δ) :
    CtxT B (ctxOfX ls gs Δ) :=
  typedV_ctxRX hl hg fun w hw => by
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hw
    exact Round5.Pos.tyT_tyV st (h st hst)

/-- A group's own context, at the images. -/
theorem ctxOfX_withRecsA (ls gs : List Value) (Δ : TypeCtx) (sts : List CSubType) :
    ctxOfX ls gs (Round6.RefOkV.withRecsA Δ sts) = ctxRX ls gs (sts.map tyV ++ Δ.recs.map tyV) := by
  simp [ctxOfX, Round6.RefOkV.withRecsA]

/-- **`Deftype_ok`**, from `Rectype_ok2` read in the group's own context. -/
theorem okD_defnX {O : ElseI} {ls gs : List Value} {Δ : TypeCtx} (hc : CtxT B (ctxOfX ls gs Δ))
    {subs : Ty (.list .sub)} {i : Nat} (hb : tyBnd (Ty.defn (.group subs) i : DefType) = true)
    (hi : i < subs.length)
    (hg : DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxOfX ls gs (Round6.RefOkV.withRecsA Δ subs.toList), tyV (Ty.group subs : CRecType),
        .case "OK" (natV 0)])) :
    OkD B O (ctxOfX ls gs Δ) .def (.defn (.group subs) i) := by
  rw [ctxOfX_withRecsA] at hg
  exact dd_deftypeOkX O hc hb hi hg

/-! ## Cases needing more than one rule lemma -/

/-- `REC i <: kind` at a parent-free member, read in `ctxOfX ls gs Δ`. -/
theorem subD_recKindX {O : ElseI} {ls gs : List Value} (hL : ∀ u ∈ ls, TypedV (simEnv B) (.varT "localtype" []) u)
    (hG : ∀ u ∈ gs, TypedV (simEnv B) (.varT "globaltype" []) u) {Δ : TypeCtx} (hR : RecsBnd Δ) {i : Nat} {fin : Bool}
    {ct : CCompType} (h : Δ.recs[i]? = some (.sub fin .nil ct)) :
    SubD B O (ctxOfX ls gs Δ) .heap (.use (.recv i)) (.abs (compAbs ct)) :=
  dd_recKindX O (ctxT_ofX hL hG hR) (tyBnd_sub' (hR.get h)).2 (recs_map h)

/-- `$unrollht_` at a canonically valid type use, read in `ctxOfX ls gs Δ`. -/
theorem applies_unrollhtX {ls gs : List Value} {Δ Δ' : TypeCtx} {u : CTypeUse} {st : CSubType} (hok : TyOkB Δ' u)
    (h : Δ.unrollUse u = some st) :
    Silmaril.SpecTec.Equiv.ExecNumeric.Applies (simEnv (BI P hn host)) "unrollht_"
      [.val (ctxOfX ls gs Δ), .val (tyV u)] (tyV st) := by
  cases u with
  | recv j => exact applies_unrollht_recX (recs_map h)
  | dt d => exact applies_unrollht_dtX h
  | idx x => exact absurd hok TyOkB.not_idx

/-- **`Subtype_ok2` with one supertype**, from the readings of its premises. -/
theorem subOk2D_oneX {O : ElseI} {ls gs : List Value}
    (hL : ∀ u ∈ ls, TypedV (simEnv (BI P hn host)) (.varT "localtype" []) u)
    (hG : ∀ u ∈ gs, TypedV (simEnv (BI P hn host)) (.varT "globaltype" []) u) {Δ : TypeCtx} (hR : RecsBnd Δ) {fin : Bool} {u : CTypeUse}
    {ct ct' : CCompType} {i : Nat} {sups' : Ty (.list .use)} (hok : TyOkB Δ u)
    (hb : tyBnd (Ty.sub fin (.cons u .nil) ct : CSubType) = true) (hbf : before u i = true)
    (hun : Δ.unrollUse u = some (.sub false sups' ct'))
    (dU : OkD (BI P hn host) O (ctxOfX ls gs Δ) .use u) (dC : OkD (BI P hn host) O (ctxOfX ls gs Δ) .comp ct)
    (dS : SubD (BI P hn host) O (ctxOfX ls gs Δ) .comp ct ct') :
    DDerivesB (simEnv (BI P hn host)) O "Subtype_ok2" "%|-%:%" []
      (.tuple [ctxOfX ls gs Δ, tyV (Ty.sub fin (.cons u .nil) ct : CSubType), .case "OK" (natV i)]) :=
  have hbu : tyBnd u = true := (tyBnd_cons_iff.1 (tyBnd_sub' hb).1).1
  have hb' := tyBnd_sub' (tyBnd_unrollUse hR hok hbu hun)
  dd_subtypeOk2One O (ctxT_ofX hL hG hR) fin i hbu (tyBnd_sub' hb).2 hb'.2 hb'.1 hbf
    (applies_unrollhtX hok hun) dU dC dS

/-- **`Rectype_ok2/cons`**, from the readings of its premises. -/
theorem groupD_consX {O : ElseI} {ls gs : List Value} (hL : ∀ u ∈ ls, TypedV (simEnv B) (.varT "localtype" []) u)
    (hG : ∀ u ∈ gs, TypedV (simEnv B) (.varT "globaltype" []) u) {Δ : TypeCtx} (hR : RecsBnd Δ) {st : CSubType}
    {sts : Ty (.list .sub)} {i : Nat} (hb : tyBnd (Ty.group (.cons st sts) : CRecType) = true)
    (h₁ : DDerivesB (simEnv B) O "Subtype_ok2" "%|-%:%" []
      (.tuple [ctxOfX ls gs Δ, tyV st, .case "OK" (natV i)]))
    (h₂ : DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxOfX ls gs Δ, tyV (Ty.group sts : CRecType), .case "OK" (natV (i + 1))])) :
    DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxOfX ls gs Δ, tyV (Ty.group (.cons st sts) : CRecType), .case "OK" (natV i)]) := by
  have hb' := tyBnd_groupCons hb
  rw [tyV_group_eq] at h₂ ⊢
  exact Round6.RefOkB.dderivesB_rectypeOk2Cons O i (ctxT_ofX hL hG hR) (Round5.Pos.tyT_tyV st hb'.1)
    (tyT_elems (Round5.Pos.tyBnd_group.1 hb'.2).2) h₁ h₂

/-! ## The transcription -/

mutual

/-- **A canonical validity derivation is read by `DDerivesB`**, at every sort. -/
theorem okDX_of (O : ElseI) {ls gs : List Value}
    (hL : ∀ u ∈ ls, TypedV (simEnv (BI P hn host)) (.varT "localtype" []) u)
    (hG : ∀ u ∈ gs, TypedV (simEnv (BI P hn host)) (.varT "globaltype" []) u) : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k}, TyOkB Δ t → RecsBnd Δ →
    tyBnd t = true → OkD (BI P hn host) O (ctxOfX ls gs Δ) k t
  | _, _, _, .recv h, hR, _ =>
    dd_typeuseOkRecX O (ctxT_ofX hL hG hR) (Round5.Pos.tyT_tyV _ (hR.get h)) (recs_map h)
  | _, _, _, .dt h, hR, hb =>
    Round6.RefOkB.dderivesB_typeuseOkDef O (ctxT_ofX hL hG hR) (Round6.AgreeSub.defT hb) (okDX_of O hL hG h hR hb)
  | _, _, _, .defn h hi, hR, hb =>
    okD_defnX (ctxT_ofX hL hG hR) hb hi (groupDX_of O hL hG h (hR.withRecsA (tyBnd_defn hb)) hb)
  | _, _, _, .abs a, hR, _ => dderivesB_heaptypeOk_abs O (ctxT_ofX hL hG hR) a
  | _, _, _, .bot, hR, _ => dd_heaptypeOkBot O (ctxT_ofX hL hG hR)
  | _, _, _, .use (u := u) h, hR, hb =>
    Round6.RefOkB.dderivesB_heaptypeOkUse O (ctxT_ofX hL hG hR) (Round5.Pos.tyT_tyV u hb).1 (okDX_of O hL hG h hR hb)
  | _, _, _, .ref (n := n) h, hR, hb =>
    dderivesB_reftypeOk O (ctxT_ofX hL hG hR) (typedV_heaptype hb) n (okDX_of O hL hG h hR hb)
  | _, _, _, .num t, hR, _ => dd_valtypeOkNum O (ctxT_ofX hL hG hR) t
  | _, _, _, .vec t, hR, _ => dd_valtypeOkVec O (ctxT_ofX hL hG hR) t
  | _, _, _, .refv h, hR, hb =>
    Round6.RefOkB.dderivesB_valtypeOkRef O (ctxT_ofX hL hG hR) (typedV_reftype hb) (okDX_of O hL hG h hR hb)
  | _, _, _, .botv, hR, _ => dd_valtypeOkBot O (ctxT_ofX hL hG hR)
  | _, _, _, .val (t := t) h, hR, hb =>
    Round6.RefOkB.dderivesB_storagetypeOkVal O (ctxT_ofX hL hG hR) (Round5.Pos.tyT_tyV t hb).1
      (okDX_of O hL hG h hR hb)
  | _, _, _, .pack p, hR, _ => dd_storagetypeOkPack O (ctxT_ofX hL hG hR) p
  | _, _, _, .field (m := m) (s := s) h, hR, hb =>
    dderivesB_fieldtypeOk O (ctxT_ofX hL hG hR) (Round5.Pos.tyT_tyV s hb) m (okDX_of O hL hG h hR hb)
  | _, _, _, .struct h, hR, hb =>
    okD_struct (ctxT_ofX hL hG hR) (tyBnd_struct' hb) (okDX_of O hL hG h hR (tyBnd_struct' hb))
  | _, _, _, .array (f := f) h, hR, hb =>
    dd_comptypeOkArray O (ctxT_ofX hL hG hR) (Round5.Pos.tyT_tyV f hb) (okDX_of O hL hG h hR hb)
  | _, _, _, .func hp hr, hR, hb =>
    okD_func (ctxT_ofX hL hG hR) (tyBnd_func' hb).1 (tyBnd_func' hb).2
      (okDX_of O hL hG hp hR (tyBnd_func' hb).1) (okDX_of O hL hG hr hR (tyBnd_func' hb).2)
  | _, _, _, .nil, _, _ => okD_nil
  | _, _, _, .cons ha hl, hR, hb =>
    okD_cons (okDX_of O hL hG ha hR (tyBnd_cons_iff.1 hb).1) (okDX_of O hL hG hl hR (tyBnd_cons_iff.1 hb).2)

/-- **A canonical `Subtype_ok2` derivation is read by `DDerivesB`.** -/
theorem subOk2DX_of (O : ElseI) {ls gs : List Value}
    (hL : ∀ u ∈ ls, TypedV (simEnv (BI P hn host)) (.varT "localtype" []) u)
    (hG : ∀ u ∈ gs, TypedV (simEnv (BI P hn host)) (.varT "globaltype" []) u) : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat}, SubOk2B Δ st i →
    RecsBnd Δ → tyBnd st = true →
    DDerivesB (simEnv (BI P hn host)) O "Subtype_ok2" "%|-%:%" []
      (.tuple [ctxOfX ls gs Δ, tyV st, .case "OK" (natV i)])
  | _, .sub fin _ ct, i, .noSuper hct, hR, hb =>
    Round6.RefOkB.dderivesB_subtypeOk2 O fin i (ctxT_ofX hL hG hR) (Round5.Pos.tyT_tyV ct (tyBnd_sub' hb).2)
      (okDX_of O hL hG hct hR (tyBnd_sub' hb).2)
  | _, _, _, .oneSuper hu hbf hun hct hsub, hR, hb =>
    subOk2D_oneX hL hG hR hu hb hbf hun (okDX_of O hL hG hu hR (tyBnd_cons_iff.1 (tyBnd_sub' hb).1).1)
      (okDX_of O hL hG hct hR (tyBnd_sub' hb).2)
      (subDX_of O hL hG hsub hR (tyBnd_sub' hb).2 (tyBnd_sub' (tyBnd_unrollUse hR hu
        (tyBnd_cons_iff.1 (tyBnd_sub' hb).1).1 hun)).2)

/-- **A canonical `Rectype_ok2` derivation is read by `DDerivesB`.** -/
theorem groupDX_of (O : ElseI) {ls gs : List Value}
    (hL : ∀ u ∈ ls, TypedV (simEnv (BI P hn host)) (.varT "localtype" []) u)
    (hG : ∀ u ∈ gs, TypedV (simEnv (BI P hn host)) (.varT "globaltype" []) u) : ∀ {Δ : TypeCtx} {g : CRecType} {i : Nat}, GroupOk2B Δ g i →
    RecsBnd Δ → tyBnd g = true →
    DDerivesB (simEnv (BI P hn host)) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxOfX ls gs Δ, tyV g, .case "OK" (natV i)])
  | _, _, i, .nil, hR, _ => Round6.RefOkB.dderivesB_rectypeOk2Empty O i (ctxT_ofX hL hG hR)
  | _, _, _, .cons h hs, hR, hb =>
    groupD_consX hL hG hR hb (subOk2DX_of O hL hG h hR (tyBnd_groupCons hb).1)
      (groupDX_of O hL hG hs hR (tyBnd_groupCons hb).2)

/-- **A canonical subtyping derivation is read by `DDerivesB`**, at every sort. -/
theorem subDX_of (O : ElseI) {ls gs : List Value}
    (hL : ∀ u ∈ ls, TypedV (simEnv (BI P hn host)) (.varT "localtype" []) u)
    (hG : ∀ u ∈ gs, TypedV (simEnv (BI P hn host)) (.varT "globaltype" []) u) : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k}, SubB Δ a b →
    RecsBnd Δ → tyBnd a = true → tyBnd b = true → SubD (BI P hn host) O (ctxOfX ls gs Δ) k a b
  | _, _, _, _, .heapRefl, hR, ha, _ => Round6.AgreeSub.dderivesB_refl O (ctxT_ofX hL hG hR) (typedV_heaptype ha)
  | _, _, _, _, .heapTrans hbnd hok h₁ h₂, hR, ha, hb =>
    Round6.AgreeSub.dderivesB_trans O (ctxT_ofX hL hG hR) (typedV_heaptype ha) (typedV_heaptype hb)
      (typedV_heaptype hbnd) (okDX_of O hL hG hok hR hbnd) (subDX_of O hL hG h₁ hR ha hbnd)
      (subDX_of O hL hG h₂ hR hbnd hb)
  | _, _, _, _, .eqAny, hR, _, _ => Round6.AgreeSub.dderivesB_axiom O (ctxT_ofX hL hG hR) Round6.AgreeSub.ruleAt_eqAny
  | _, _, _, _, .i31Eq, hR, _, _ => Round6.AgreeSub.dderivesB_axiom O (ctxT_ofX hL hG hR) Round6.AgreeSub.ruleAt_i31Eq
  | _, _, _, _, .structEq, hR, _, _ =>
    Round6.AgreeSub.dderivesB_axiom O (ctxT_ofX hL hG hR) Round6.AgreeSub.ruleAt_structEq
  | _, _, _, _, .arrayEq, hR, _, _ =>
    Round6.AgreeSub.dderivesB_axiom O (ctxT_ofX hL hG hR) Round6.AgreeSub.ruleAt_arrayEq
  | _, _, _, _, .defStruct h, hR, ha, _ => Round6.AgreeSub.dderivesB_defStruct O (ctxT_ofX hL hG hR) ha h
  | _, _, _, _, .defArray h, hR, ha, _ => Round6.AgreeSub.dderivesB_defArray O (ctxT_ofX hL hG hR) ha h
  | _, _, _, _, .defFunc h, hR, ha, _ => Round6.AgreeSub.dderivesB_defFunc O (ctxT_ofX hL hG hR) ha h
  | _, _, _, _, .defDef h, hR, ha, hb =>
    Round6.AgreeSub.dderivesB_def O (ctxT_ofX hL hG hR) ha hb (subDX_of O hL hG h hR ha hb)
  | _, _, _, _, .recStruct h, hR, _, _ => subD_recKindX hL hG hR h
  | _, _, _, _, .recArray h, hR, _, _ => subD_recKindX hL hG hR h
  | _, _, _, _, .recFunc h, hR, _, _ => subD_recKindX hL hG hR h
  | _, _, _, _, .recSub h hj, hR, _, _ => dd_recSubX O (ctxT_ofX hL hG hR) (hR.get h) (recs_map h) hj
  | _, _, _, _, .none hs hne, hR, _, hb =>
    Round6.AgreeSub.dderivesB_botRule O (ctxT_ofX hL hG hR) (typedV_heaptype hb) Round6.AgreeSub.ruleAt_none
      (tyV_ne_bot hne) (subDX_of O hL hG hs hR hb rfl)
  | _, _, _, _, .nofunc hs hne, hR, _, hb =>
    Round6.AgreeSub.dderivesB_botRule O (ctxT_ofX hL hG hR) (typedV_heaptype hb) Round6.AgreeSub.ruleAt_nofunc
      (tyV_ne_bot hne) (subDX_of O hL hG hs hR hb rfl)
  | _, _, _, _, .noexn hs hne, hR, _, hb =>
    Round6.AgreeSub.dderivesB_botRule O (ctxT_ofX hL hG hR) (typedV_heaptype hb) Round6.AgreeSub.ruleAt_noexn
      (tyV_ne_bot hne) (subDX_of O hL hG hs hR hb rfl)
  | _, _, _, _, .noextern hs hne, hR, _, hb =>
    Round6.AgreeSub.dderivesB_botRule O (ctxT_ofX hL hG hR) (typedV_heaptype hb) Round6.AgreeSub.ruleAt_noextern
      (tyV_ne_bot hne) (subDX_of O hL hG hs hR hb rfl)
  | _, _, _, _, .bot, hR, _, hb => dderivesB_heaptypeSub_bot O (ctxT_ofX hL hG hR) (typedV_heaptype hb)
  | _, _, _, _, .refNonNull h, hR, ha, hb =>
    Round6.AgreeSub.dderivesB_nonnull O (ctxT_ofX hL hG hR) (typedV_heaptype ha) (typedV_heaptype hb)
      (subDX_of O hL hG h hR ha hb)
  | _, _, _, _, .refNull (n := n) h, hR, ha, hb =>
    dderivesB_reftypeSub_null O (ctxT_ofX hL hG hR) (typedV_heaptype ha) (typedV_heaptype hb) n
      (subDX_of O hL hG h hR ha hb)
  | _, _, _, _, .num (t := t), hR, _, _ =>
    dd_subsumeSub O (ctxT_ofX hL hG hR) ruleAt_valtypeSubNum (typedV_numtypeV t) (typedV_numtypeV t)
      (dd_leafSub O (ctxT_ofX hL hG hR) ruleAt_numtypeSub (typedV_numtypeV t))
  | _, _, _, _, .vec (t := t), hR, _, _ =>
    dd_subsumeSub O (ctxT_ofX hL hG hR) ruleAt_valtypeSubVec (typedV_vectypeV t) (typedV_vectypeV t)
      (dd_leafSub O (ctxT_ofX hL hG hR) ruleAt_vectypeSub (typedV_vectypeV t))
  | _, _, _, _, .refv h, hR, ha, hb =>
    dd_subsumeSub O (ctxT_ofX hL hG hR) ruleAt_valtypeSubRef (typedV_reftype ha) (typedV_reftype hb)
      (subDX_of O hL hG h hR ha hb)
  | _, _, _, _, .botv, hR, _, hb => dd_valtypeSubBot O (ctxT_ofX hL hG hR) (Round5.Pos.tyT_tyV _ hb).1
  | _, _, _, _, .val (t₁ := t₁) (t₂ := t₂) h, hR, ha, hb =>
    dd_subsumeSub O (ctxT_ofX hL hG hR) ruleAt_storagetypeSubVal (Round5.Pos.tyT_tyV t₁ ha).1
      (Round5.Pos.tyT_tyV t₂ hb).1 (subDX_of O hL hG h hR ha hb)
  | _, _, _, _, .pack (p := p), hR, _, _ =>
    dd_subsumeSub O (ctxT_ofX hL hG hR) ruleAt_storagetypeSubPack (typedV_packtypeV p)
      (typedV_packtypeV p) (dd_leafSub O (ctxT_ofX hL hG hR) ruleAt_packtypeSub (typedV_packtypeV p))
  | _, _, _, _, .fieldConst (z₁ := z₁) (z₂ := z₂) h, hR, ha, hb =>
    dd_fieldtypeSubConst O (ctxT_ofX hL hG hR) (Round5.Pos.tyT_tyV z₁ ha) (Round5.Pos.tyT_tyV z₂ hb)
      (subDX_of O hL hG h hR ha hb)
  | _, _, _, _, .fieldVar (z₁ := z₁) (z₂ := z₂) h₁ h₂, hR, ha, hb =>
    dd_fieldtypeSubVar O (ctxT_ofX hL hG hR) (Round5.Pos.tyT_tyV z₁ ha) (Round5.Pos.tyT_tyV z₂ hb)
      (subDX_of O hL hG h₁ hR ha hb) (subDX_of O hL hG h₂ hR hb ha)
  | _, _, _, _, .struct h, hR, ha, hb =>
    subD_struct (ctxT_ofX hL hG hR) ha hb (subDX_of O hL hG h hR (tyBnd_structApp ha).1 (tyBnd_struct' hb))
  | _, _, _, _, .array (f₁ := f₁) (f₂ := f₂) h, hR, ha, hb =>
    dd_comptypeSubArray O (ctxT_ofX hL hG hR) (Round5.Pos.tyT_tyV f₁ ha) (Round5.Pos.tyT_tyV f₂ hb)
      (subDX_of O hL hG h hR ha hb)
  | _, _, _, _, .func hp hr, hR, ha, hb =>
    subD_func (ctxT_ofX hL hG hR) ha hb (subDX_of O hL hG hp hR (tyBnd_func' hb).1 (tyBnd_func' ha).1)
      (subDX_of O hL hG hr hR (tyBnd_func' ha).2 (tyBnd_func' hb).2)
  | _, _, _, _, .defSuper h hj hs, hR, ha, hb =>
    Round6.AgreeSub.dderivesB_super O (ctxT_ofX hL hG hR) ha hb h hj
      (subDX_of O hL hG hs hR (tyBnd_superOf ha h hj) hb)
  | _, _, _, _, .nil, _, _, _ => subD_nil
  | _, _, _, _, .cons h hl, hR, ha, hb =>
    subD_cons (subDX_of O hL hG h hR (tyBnd_cons_iff.1 ha).1 (tyBnd_cons_iff.1 hb).1)
      (subDX_of O hL hG hl hR (tyBnd_cons_iff.1 ha).2 (tyBnd_cons_iff.1 hb).2)

end

end Silmaril.Wasm.SpecTec.Institution.Instr30W

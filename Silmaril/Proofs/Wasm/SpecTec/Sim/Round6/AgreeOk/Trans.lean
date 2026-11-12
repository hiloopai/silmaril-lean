module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.TransCases

/-!
# Round 6: canonical derivations are read by `DDerivesB`

`okD_of`, `subOk2D_of`, `groupD_of`, `subD_of`: one mutual structural recursion over
`TyOkB`/`SubOk2B`/`GroupOk2B`/`SubB`, rule for rule, in `simEnv (BI P hn host)` (the concrete
builtins answer `$unrolldt`, which `Expand` and `$unrollht_` call), at the SpecTec context
`ctxOf Δ` (`RECS` the images of `Δ.recs`), under every reading of `otherwise`. Every type the
rules quantify over is bounded: the judged types by hypothesis, `Heaptype_sub/trans`'s middles by
`SubB`, and the unrolled supertypes of `Subtype_ok2` because the context and the supertype are.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_list natV absV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.Numerics (Profile)
open Round6.Reading
open Round6.AgreeSub (CtxT)
open Round4Int (BI)
open Round4 (tyBnd)

variable {B : Builtins} {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Cases needing more than one rule lemma -/

/-- An image of a heap type other than `BOT` is not `BOT`'s. -/
theorem tyV_ne_bot {h : CHeapType} (hne : h ≠ .bot) : tyV h ≠ .case "BOT" (.tuple []) := by
  cases h with
  | abs a => exact AgreeSub.absV_ne_bot a
  | bot => exact absurd rfl hne
  | use u => exact fun e => Silmaril.SpecTec.Equiv.Validation.botV_ne_use u e.symm

/-- `REC i <: kind` at a parent-free member, read in `ctxOf Δ`. -/
theorem subD_recKind {O : ElseI} {Δ : TypeCtx} (hR : RecsBnd Δ) {i : Nat} {fin : Bool}
    {ct : CCompType} (h : Δ.recs[i]? = some (.sub fin .nil ct)) :
    SubD B O (ctxOf Δ) .heap (.use (.recv i)) (.abs (compAbs ct)) :=
  dd_recKind O (ctxT_of hR) (tyBnd_sub' (hR.get h)).2 (recs_map h)

/-- `$unrollht_` at a canonically valid type use, read in `ctxOf Δ`. -/
theorem applies_unrollht {Δ Δ' : TypeCtx} {u : CTypeUse} {st : CSubType} (hok : TyOkB Δ' u)
    (h : Δ.unrollUse u = some st) :
    Silmaril.SpecTec.Equiv.ExecNumeric.Applies (simEnv (BI P hn host)) "unrollht_"
      [.val (ctxOf Δ), .val (tyV u)] (tyV st) := by
  cases u with
  | recv j => exact applies_unrollht_rec (recs_map h)
  | dt d => exact applies_unrollht_dt h
  | idx x => exact absurd hok TyOkB.not_idx

/-- **`Subtype_ok2` with one supertype**, from the readings of its premises. -/
theorem subOk2D_one {O : ElseI} {Δ : TypeCtx} (hR : RecsBnd Δ) {fin : Bool} {u : CTypeUse}
    {ct ct' : CCompType} {i : Nat} {sups' : Ty (.list .use)} (hok : TyOkB Δ u)
    (hb : tyBnd (Ty.sub fin (.cons u .nil) ct : CSubType) = true) (hbf : before u i = true)
    (hun : Δ.unrollUse u = some (.sub false sups' ct'))
    (dU : OkD (BI P hn host) O (ctxOf Δ) .use u) (dC : OkD (BI P hn host) O (ctxOf Δ) .comp ct)
    (dS : SubD (BI P hn host) O (ctxOf Δ) .comp ct ct') :
    DDerivesB (simEnv (BI P hn host)) O "Subtype_ok2" "%|-%:%" []
      (.tuple [ctxOf Δ, tyV (Ty.sub fin (.cons u .nil) ct : CSubType), .case "OK" (natV i)]) :=
  have hbu : tyBnd u = true := (tyBnd_cons_iff.1 (tyBnd_sub' hb).1).1
  have hb' := tyBnd_sub' (tyBnd_unrollUse hR hok hbu hun)
  dd_subtypeOk2One O (ctxT_of hR) fin i hbu (tyBnd_sub' hb).2 hb'.2 hb'.1 hbf
    (applies_unrollht hok hun) dU dC dS

/-- **`Rectype_ok2/cons`**, from the readings of its premises. -/
theorem groupD_cons {O : ElseI} {Δ : TypeCtx} (hR : RecsBnd Δ) {st : CSubType}
    {sts : Ty (.list .sub)} {i : Nat} (hb : tyBnd (Ty.group (.cons st sts) : CRecType) = true)
    (h₁ : DDerivesB (simEnv B) O "Subtype_ok2" "%|-%:%" []
      (.tuple [ctxOf Δ, tyV st, .case "OK" (natV i)]))
    (h₂ : DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxOf Δ, tyV (Ty.group sts : CRecType), .case "OK" (natV (i + 1))])) :
    DDerivesB (simEnv B) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxOf Δ, tyV (Ty.group (.cons st sts) : CRecType), .case "OK" (natV i)]) := by
  have hb' := tyBnd_groupCons hb
  rw [tyV_group_eq] at h₂ ⊢
  exact RefOkB.dderivesB_rectypeOk2Cons O i (ctxT_of hR) (Round5.Pos.tyT_tyV st hb'.1)
    (tyT_elems (Round5.Pos.tyBnd_group.1 hb'.2).2) h₁ h₂

/-! ## The transcription -/

mutual

/-- **A canonical validity derivation is read by `DDerivesB`**, at every sort. -/
theorem okD_of (O : ElseI) : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k}, TyOkB Δ t → RecsBnd Δ →
    tyBnd t = true → OkD (BI P hn host) O (ctxOf Δ) k t
  | _, _, _, .recv h, hR, _ =>
    RefOkB.dderivesB_typeuseOkRec O (ctxT_of hR) (Round5.Pos.tyT_tyV _ (hR.get h)) (recs_map h)
  | _, _, _, .dt h, hR, hb =>
    RefOkB.dderivesB_typeuseOkDef O (ctxT_of hR) (AgreeSub.defT hb) (okD_of O h hR hb)
  | _, _, _, .defn h hi, hR, hb =>
    okD_defn (ctxT_of hR) hb hi (groupD_of O h (hR.withRecsA (tyBnd_defn hb)) hb)
  | _, _, _, .abs a, hR, _ => dderivesB_heaptypeOk_abs O (ctxT_of hR) a
  | _, _, _, .bot, hR, _ => dd_heaptypeOkBot O (ctxT_of hR)
  | _, _, _, .use (u := u) h, hR, hb =>
    RefOkB.dderivesB_heaptypeOkUse O (ctxT_of hR) (Round5.Pos.tyT_tyV u hb).1 (okD_of O h hR hb)
  | _, _, _, .ref (n := n) h, hR, hb =>
    dderivesB_reftypeOk O (ctxT_of hR) (typedV_heaptype hb) n (okD_of O h hR hb)
  | _, _, _, .num t, hR, _ => dd_valtypeOkNum O (ctxT_of hR) t
  | _, _, _, .vec t, hR, _ => dd_valtypeOkVec O (ctxT_of hR) t
  | _, _, _, .refv h, hR, hb =>
    RefOkB.dderivesB_valtypeOkRef O (ctxT_of hR) (typedV_reftype hb) (okD_of O h hR hb)
  | _, _, _, .botv, hR, _ => dd_valtypeOkBot O (ctxT_of hR)
  | _, _, _, .val (t := t) h, hR, hb =>
    RefOkB.dderivesB_storagetypeOkVal O (ctxT_of hR) (Round5.Pos.tyT_tyV t hb).1
      (okD_of O h hR hb)
  | _, _, _, .pack p, hR, _ => dd_storagetypeOkPack O (ctxT_of hR) p
  | _, _, _, .field (m := m) (s := s) h, hR, hb =>
    dderivesB_fieldtypeOk O (ctxT_of hR) (Round5.Pos.tyT_tyV s hb) m (okD_of O h hR hb)
  | _, _, _, .struct h, hR, hb =>
    okD_struct (ctxT_of hR) (tyBnd_struct' hb) (okD_of O h hR (tyBnd_struct' hb))
  | _, _, _, .array (f := f) h, hR, hb =>
    dd_comptypeOkArray O (ctxT_of hR) (Round5.Pos.tyT_tyV f hb) (okD_of O h hR hb)
  | _, _, _, .func hp hr, hR, hb =>
    okD_func (ctxT_of hR) (tyBnd_func' hb).1 (tyBnd_func' hb).2
      (okD_of O hp hR (tyBnd_func' hb).1) (okD_of O hr hR (tyBnd_func' hb).2)
  | _, _, _, .nil, _, _ => okD_nil
  | _, _, _, .cons ha hl, hR, hb =>
    okD_cons (okD_of O ha hR (tyBnd_cons_iff.1 hb).1) (okD_of O hl hR (tyBnd_cons_iff.1 hb).2)

/-- **A canonical `Subtype_ok2` derivation is read by `DDerivesB`.** -/
theorem subOk2D_of (O : ElseI) : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat}, SubOk2B Δ st i →
    RecsBnd Δ → tyBnd st = true →
    DDerivesB (simEnv (BI P hn host)) O "Subtype_ok2" "%|-%:%" []
      (.tuple [ctxOf Δ, tyV st, .case "OK" (natV i)])
  | _, .sub fin _ ct, i, .noSuper hct, hR, hb =>
    RefOkB.dderivesB_subtypeOk2 O fin i (ctxT_of hR) (Round5.Pos.tyT_tyV ct (tyBnd_sub' hb).2)
      (okD_of O hct hR (tyBnd_sub' hb).2)
  | _, _, _, .oneSuper hu hbf hun hct hsub, hR, hb =>
    subOk2D_one hR hu hb hbf hun (okD_of O hu hR (tyBnd_cons_iff.1 (tyBnd_sub' hb).1).1)
      (okD_of O hct hR (tyBnd_sub' hb).2)
      (subD_of O hsub hR (tyBnd_sub' hb).2 (tyBnd_sub' (tyBnd_unrollUse hR hu
        (tyBnd_cons_iff.1 (tyBnd_sub' hb).1).1 hun)).2)

/-- **A canonical `Rectype_ok2` derivation is read by `DDerivesB`.** -/
theorem groupD_of (O : ElseI) : ∀ {Δ : TypeCtx} {g : CRecType} {i : Nat}, GroupOk2B Δ g i →
    RecsBnd Δ → tyBnd g = true →
    DDerivesB (simEnv (BI P hn host)) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxOf Δ, tyV g, .case "OK" (natV i)])
  | _, _, i, .nil, hR, _ => RefOkB.dderivesB_rectypeOk2Empty O i (ctxT_of hR)
  | _, _, _, .cons h hs, hR, hb =>
    groupD_cons hR hb (subOk2D_of O h hR (tyBnd_groupCons hb).1)
      (groupD_of O hs hR (tyBnd_groupCons hb).2)

/-- **A canonical subtyping derivation is read by `DDerivesB`**, at every sort. -/
theorem subD_of (O : ElseI) : ∀ {Δ : TypeCtx} {k : TKind} {a b : Ty k}, SubB Δ a b →
    RecsBnd Δ → tyBnd a = true → tyBnd b = true → SubD (BI P hn host) O (ctxOf Δ) k a b
  | _, _, _, _, .heapRefl, hR, ha, _ => AgreeSub.dderivesB_refl O (ctxT_of hR) (typedV_heaptype ha)
  | _, _, _, _, .heapTrans hbnd hok h₁ h₂, hR, ha, hb =>
    AgreeSub.dderivesB_trans O (ctxT_of hR) (typedV_heaptype ha) (typedV_heaptype hb)
      (typedV_heaptype hbnd) (okD_of O hok hR hbnd) (subD_of O h₁ hR ha hbnd)
      (subD_of O h₂ hR hbnd hb)
  | _, _, _, _, .eqAny, hR, _, _ => AgreeSub.dderivesB_axiom O (ctxT_of hR) AgreeSub.ruleAt_eqAny
  | _, _, _, _, .i31Eq, hR, _, _ => AgreeSub.dderivesB_axiom O (ctxT_of hR) AgreeSub.ruleAt_i31Eq
  | _, _, _, _, .structEq, hR, _, _ =>
    AgreeSub.dderivesB_axiom O (ctxT_of hR) AgreeSub.ruleAt_structEq
  | _, _, _, _, .arrayEq, hR, _, _ =>
    AgreeSub.dderivesB_axiom O (ctxT_of hR) AgreeSub.ruleAt_arrayEq
  | _, _, _, _, .defStruct h, hR, ha, _ => AgreeSub.dderivesB_defStruct O (ctxT_of hR) ha h
  | _, _, _, _, .defArray h, hR, ha, _ => AgreeSub.dderivesB_defArray O (ctxT_of hR) ha h
  | _, _, _, _, .defFunc h, hR, ha, _ => AgreeSub.dderivesB_defFunc O (ctxT_of hR) ha h
  | _, _, _, _, .defDef h, hR, ha, hb =>
    AgreeSub.dderivesB_def O (ctxT_of hR) ha hb (subD_of O h hR ha hb)
  | _, _, _, _, .recStruct h, hR, _, _ => subD_recKind hR h
  | _, _, _, _, .recArray h, hR, _, _ => subD_recKind hR h
  | _, _, _, _, .recFunc h, hR, _, _ => subD_recKind hR h
  | _, _, _, _, .recSub h hj, hR, _, _ => dd_recSub O (ctxT_of hR) (hR.get h) (recs_map h) hj
  | _, _, _, _, .none hs hne, hR, _, hb =>
    AgreeSub.dderivesB_botRule O (ctxT_of hR) (typedV_heaptype hb) AgreeSub.ruleAt_none
      (tyV_ne_bot hne) (subD_of O hs hR hb rfl)
  | _, _, _, _, .nofunc hs hne, hR, _, hb =>
    AgreeSub.dderivesB_botRule O (ctxT_of hR) (typedV_heaptype hb) AgreeSub.ruleAt_nofunc
      (tyV_ne_bot hne) (subD_of O hs hR hb rfl)
  | _, _, _, _, .noexn hs hne, hR, _, hb =>
    AgreeSub.dderivesB_botRule O (ctxT_of hR) (typedV_heaptype hb) AgreeSub.ruleAt_noexn
      (tyV_ne_bot hne) (subD_of O hs hR hb rfl)
  | _, _, _, _, .noextern hs hne, hR, _, hb =>
    AgreeSub.dderivesB_botRule O (ctxT_of hR) (typedV_heaptype hb) AgreeSub.ruleAt_noextern
      (tyV_ne_bot hne) (subD_of O hs hR hb rfl)
  | _, _, _, _, .bot, hR, _, hb => dderivesB_heaptypeSub_bot O (ctxT_of hR) (typedV_heaptype hb)
  | _, _, _, _, .refNonNull h, hR, ha, hb =>
    AgreeSub.dderivesB_nonnull O (ctxT_of hR) (typedV_heaptype ha) (typedV_heaptype hb)
      (subD_of O h hR ha hb)
  | _, _, _, _, .refNull (n := n) h, hR, ha, hb =>
    dderivesB_reftypeSub_null O (ctxT_of hR) (typedV_heaptype ha) (typedV_heaptype hb) n
      (subD_of O h hR ha hb)
  | _, _, _, _, .num (t := t), hR, _, _ =>
    dd_subsumeSub O (ctxT_of hR) ruleAt_valtypeSubNum (typedV_numtypeV t) (typedV_numtypeV t)
      (dd_leafSub O (ctxT_of hR) ruleAt_numtypeSub (typedV_numtypeV t))
  | _, _, _, _, .vec (t := t), hR, _, _ =>
    dd_subsumeSub O (ctxT_of hR) ruleAt_valtypeSubVec (typedV_vectypeV t) (typedV_vectypeV t)
      (dd_leafSub O (ctxT_of hR) ruleAt_vectypeSub (typedV_vectypeV t))
  | _, _, _, _, .refv h, hR, ha, hb =>
    dd_subsumeSub O (ctxT_of hR) ruleAt_valtypeSubRef (typedV_reftype ha) (typedV_reftype hb)
      (subD_of O h hR ha hb)
  | _, _, _, _, .botv, hR, _, hb => dd_valtypeSubBot O (ctxT_of hR) (Round5.Pos.tyT_tyV _ hb).1
  | _, _, _, _, .val (t₁ := t₁) (t₂ := t₂) h, hR, ha, hb =>
    dd_subsumeSub O (ctxT_of hR) ruleAt_storagetypeSubVal (Round5.Pos.tyT_tyV t₁ ha).1
      (Round5.Pos.tyT_tyV t₂ hb).1 (subD_of O h hR ha hb)
  | _, _, _, _, .pack (p := p), hR, _, _ =>
    dd_subsumeSub O (ctxT_of hR) ruleAt_storagetypeSubPack (typedV_packtypeV p)
      (typedV_packtypeV p) (dd_leafSub O (ctxT_of hR) ruleAt_packtypeSub (typedV_packtypeV p))
  | _, _, _, _, .fieldConst (z₁ := z₁) (z₂ := z₂) h, hR, ha, hb =>
    dd_fieldtypeSubConst O (ctxT_of hR) (Round5.Pos.tyT_tyV z₁ ha) (Round5.Pos.tyT_tyV z₂ hb)
      (subD_of O h hR ha hb)
  | _, _, _, _, .fieldVar (z₁ := z₁) (z₂ := z₂) h₁ h₂, hR, ha, hb =>
    dd_fieldtypeSubVar O (ctxT_of hR) (Round5.Pos.tyT_tyV z₁ ha) (Round5.Pos.tyT_tyV z₂ hb)
      (subD_of O h₁ hR ha hb) (subD_of O h₂ hR hb ha)
  | _, _, _, _, .struct h, hR, ha, hb =>
    subD_struct (ctxT_of hR) ha hb (subD_of O h hR (tyBnd_structApp ha).1 (tyBnd_struct' hb))
  | _, _, _, _, .array (f₁ := f₁) (f₂ := f₂) h, hR, ha, hb =>
    dd_comptypeSubArray O (ctxT_of hR) (Round5.Pos.tyT_tyV f₁ ha) (Round5.Pos.tyT_tyV f₂ hb)
      (subD_of O h hR ha hb)
  | _, _, _, _, .func hp hr, hR, ha, hb =>
    subD_func (ctxT_of hR) ha hb (subD_of O hp hR (tyBnd_func' hb).1 (tyBnd_func' ha).1)
      (subD_of O hr hR (tyBnd_func' ha).2 (tyBnd_func' hb).2)
  | _, _, _, _, .defSuper h hj hs, hR, ha, hb =>
    AgreeSub.dderivesB_super O (ctxT_of hR) ha hb h hj
      (subD_of O hs hR (tyBnd_superOf ha h hj) hb)
  | _, _, _, _, .nil, _, _, _ => subD_nil
  | _, _, _, _, .cons h hl, hR, ha, hb =>
    subD_cons (subD_of O h hR (tyBnd_cons_iff.1 ha).1 (tyBnd_cons_iff.1 hb).1)
      (subD_of O hl hR (tyBnd_cons_iff.1 ha).2 (tyBnd_cons_iff.1 hb).2)

end

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

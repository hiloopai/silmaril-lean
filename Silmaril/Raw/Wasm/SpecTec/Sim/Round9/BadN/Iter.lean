module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.BadN.Check

/-!
# Round 9, RE: indexed list iterations across erasure (unrefined)

`iterN_fwd`: an iterated premise `pr^(k<eₙ)` (`DPremB.iterListN`) goes to the erased side when its
body iterates over lists only. The bound `eₙ` and the domains go across by round 8's
`NxDer.exp_fwd` and `doms_fwd`; erasure keeps the bound's number (`Swap.asNat?_eraseV`), the
domain lists' shapes and the rows up to `eraseP` (`EraseAll.iterRows_erase`, which allows an
index); each row extends the context (`pCtx_rowN`, round 7's `NxFlow.rowScope_list` with the
index as a counter), and the body goes across by round 8's `NxDer.dpremB_fwd`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadN

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0 premAuxR)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT premX)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseA)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp xPrem eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round8.NxDer (PCtx)
open Round6.Reading (DDerivesB DPremB conclAlts otherwiseB)

variable {B : Builtins}

/-- The rows of an indexed list iteration extend a context. -/
theorem pCtx_rowN {Γ : List (String × AT)} {ρq : VarEnv} (hc : PCtx B Γ ρq) {ds : List Dom}
    {xvs : List (IL.Id × Value)} (hnd : nodupB (ds.map domVar) = true)
    (htd : tyOkD sigX tsigFixed Γ ds = true) (had : auxD ctx0 ds = true)
    (hd : EvalDoms (utf8Env B) ρq ds xvs) {dls : List (IL.Id × List Value)}
    (hl : domLists xvs = some dls) {k : Nat} (hlen : ∀ d ∈ dls, d.2.length = k) {eₙ : Exp}
    {ido : Option IL.Id} {r : List (IL.Id × Value)} (hr : r ∈ iterRows dls ido k) :
    PCtx B (iterΓ sigX Γ (.listN eₙ ido) ds) (ρq.bindVals r) := by
  obtain ⟨m, hm⟩ := hd
  have hE := (expAt (utf8Env B) m).doms sigX tsigFixed Γ ctx0 ρq ds xvs hc.vt (hc.nc m).callH
    htd had hm
  simp only [iterRows, List.mem_map, List.mem_range] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  exact ⟨rowScope_list hc.vt hnd hE (by cases ido <;> rfl) hl hlen hi,
    fun n => (hc.nc n).bindVals _⟩

section Iter

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
  {O₁ O' : ElseI} (hO : ∀ x args i v, O₁ x args i v → O' x (args.map eraseA) i (eraseV v))
include hB H hO

/-- **An indexed list iteration goes to the erased side.** -/
theorem iterN_fwd {els els' : Prop} {Γ : List (String × AT)} {ρq ρ : VarEnv} {pr : Prem}
    {eₙ : Exp} {ido : Option IL.Id} {ds : List Dom} (hc : PCtx B Γ ρq)
    (hag : VarEnv.AgreeOn (freePrem (.iterPr pr (.mk (.listN eₙ ido) ds))) ρ ρq)
    (ht : premTy sigX tsigFixed Γ (.iterPr pr (.mk (.listN eₙ ido) ds)) = true)
    (ha : premAuxR (.iterPr pr (.mk (.listN eₙ ido) ds)) = true)
    (hX : premX ctx0 (.iterPr pr (.mk (.listN eₙ ido) ds)) = true)
    (hb : badPr sigX Γ (.iterPr pr (.mk (.listN eₙ ido) ds)) = 0)
    (hx : xPrem grE gdE (.iterPr pr (.mk (.listN eₙ ido) ds)) = true)
    (hl : Round8.NxDer.listIter pr = true) (hels : els → els')
    (h : DPremB (utf8Env B) O₁ els ρ (.iterPr pr (.mk (.listN eₙ ido) ds))) :
    DPremB (utf8Env B) O' els' (eraseScope ρ) (.iterPr pr (.mk (.listN eₙ ido) ds)) := by
  match h with
  | .iterList hit _ _ _ _ _ => rcases hit with h | ⟨h, _⟩ <;> cases h
  | .iterListN (xvs := xvs) (dls := dls) (k := k) hd he hk hdl hlen hp =>
    simp only [premTy, Bool.and_eq_true] at ht
    simp only [premAuxR, Bool.and_eq_true] at ha
    simp only [premX, Bool.and_eq_true] at hX
    simp only [badPr] at hb
    simp only [xPrem, Bool.and_eq_true] at hx
    have hagd := hag.mono (EraseDer.sub_iter_doms pr _ ds)
    have hd' := Round8.NxDer.doms_fwd H hc hagd ht.2 ha.2 hX.2 (by omega) hx.2 hd
    have hagn := hag.mono (EraseDer.sub_iter_n pr eₙ ido ds)
    have he' := Round8.NxDer.exp_fwd H hc hagn (by simpa [tyOkI] using ht.1.2)
      (by simpa [auxI] using ha.1.2) (by simpa [NxErase.auxXI] using hX.1.2)
      (by simp only [badI] at hb; omega) (by simpa [EraseAll.xIter] using hx.1.2) he
    have hdq : EvalDoms (utf8Env B) ρq ds xvs := by
      obtain ⟨n, hn⟩ := hd
      exact ⟨n, by rw [← evalDoms_agreeOn hagd]; exact hn⟩
    have hdl' : domLists (xvs.map eraseP) = some (dls.map fun p => (p.1, p.2.map eraseV)) := by
      rw [EraseDer.domLists_erase, hdl]; rfl
    refine .iterListN hd' he' (by rw [Swap.asNat?_eraseV]; exact hk) hdl'
      (EraseDer.lens_erase hlen) fun r' hr' => ?_
    rw [EraseAll.iterRows_erase] at hr'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hr'
    rw [← EraseAll.eraseScope_bindVals]
    have hkeys : r.map Prod.fst = ds.map domVar ++ ido.toList := by
      rw [EraseDer.map_fst_row hlen hr, EraseDer.map_fst_domLists hdl,
        EraseDer.map_fst_EvalDoms hd]
    have hag' : VarEnv.AgreeOn (freePrem pr) (ρ.bindVals r) (ρq.bindVals r) :=
      EvalFree.agreeOn_body hag
        (EraseDer.bound_sub_rowSet hkeys (EvalFree.boundIter_listN_subset_keySet eₙ ido))
        (EraseDer.sub_iter_body pr _)
    exact Round8.NxDer.dpremB_fwd hB H hO (pCtx_rowN hc ha.1.1.2 ht.2 ha.2 hdq hdl hlen hr) hag'
      ht.1.1 ha.1.1.1 hX.1.1 (by omega) hx.1.1 hl hels (hp r hr)

end Iter

end Silmaril.Wasm.SpecTec.Sim.Round9.BadN

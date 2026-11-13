module

public import Silmaril.Wasm.Auto2.Summ.Defs
public import Silmaril.Wasm.Auto.Bridge.Thms
public import Silmaril.Wasm.Auto.EquivUnroll.Thms

/-!
# Summaries with unrolled loops: total specifications and behaviour sets (unrefined)

`tfspecU_of_sumOfU`: a function instance with a summary of the unrolling executor (`sumOfU`)
has the total specification "called from the store `s₀` on typed arguments `vs`, its outcome is
that of `fnOutX F vs`" at every profile and host relation: the equiv forward rule for the
unrolling executor (`EquivUnroll.wp_xsexecU`) in the total reading, from the call frame, the
store's globals and memory `0`, as `Bridge.tfspecX_of_sumOfX` does for `xsexec`.
`behaviours_of_fnSumU`: the behaviour set of every accepted invocation of a summarised export is
`{(fnOutX F vs).toBehaviour}`.

The proofs follow `Silmaril.Raw.Wasm.Auto.BridgeX.Func` line by line with the executor replaced.
New proofs (unrefined: valid, not yet in Isar style).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Summ

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm.Auto.Equiv (Env envOfVals TypedVals den)
open Silmaril.Wasm.Auto.Bridge (scalarInt? intTy? mapM_length locals_zero typedVals_of_forall₂
  export_expand)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Game (ScalarType ScalarInstance FnType)
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Auto.Front (addrOf)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fuel : Nat}

/-- What a summary records. -/
theorem sumOfU_inv {s : Store H} {ft : FnType} {fi : FuncInst H} {F : FnSumX}
    (h : sumOfU fuel s ft fi = some F) :
    ∃ code ps rs ls A, fi.code = .wasm code ∧ ft.params.mapM scalarInt? = some ps ∧
      ft.results.mapM scalarInt? = some rs ∧ code.locals.mapM intTy? = some ls ∧
      Silmaril.Wasm.Auto.EquivUnroll.xsexecU (memOf s fi.module).isSome fuel
        (fnInitX ps ls (globsUsed s fi.module).2.2) code.body =
        some A ∧ A.stack.map (·.1) = rs.reverse ∧
      F = ⟨ps, rs, (globsUsed s fi.module).2.1, bytesOf (memOf s fi.module), A⟩ := by
  unfold sumOfU at h
  split at h
  · rename_i code hcode
    split at h
    · rename_i ps rs ls hps hrs hls
      dsimp only at h
      split at h
      · rename_i A hA
        split at h
        · exact ⟨code, ps, rs, ls, A, hcode, hps, hrs, hls, hA, by assumption,
            (Option.some.inj h).symm⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem guardsOk_iff {ρ : Env} {B0 : ByteArray} {G : List (Guard × XState)} :
    guardsOk ρ B0 G = true ↔ firstFail ρ B0 G = none := by
  rw [firstFail_none_iff]
  simp [guardsOk]

/-- **A summary is a total specification**, at every profile and host relation. -/
theorem tfspecU_of_sumOfU {s₀ : Store H} {ft : FnType} {fi : FuncInst H} {F : FnSumX}
    (h : sumOfU fuel s₀ ft fi = some F) {a : Nat} (hfi : s₀.funcs[a]? = some fi)
    (he : Expand fi.type ft.toComp) : TFSpecAt P host a (sumSpecX F s₀) := by
  obtain ⟨code, ps, rs, ls, A, hcode, hps, hrs, hls, hA, hty, hF⟩ := sumOfU_inv h
  have hFp : F.params = ps := by rw [hF]
  have hFf : F.final = A := by rw [hF]
  have hFb : F.bytes = bytesOf (memOf s₀ fi.module) := by rw [hF]
  refine TFSpecAt.of_body (fi := fi) (code := code) (hfi := fun s _ hp => hp.1 ▸ hfi)
    hcode he (fun _ args hp => ?_) (fun s args hp f vs₀ => ?_)
  · show args.length = (Ty.ofList (ft.params.map ScalarType.toC)).length
    rw [Ty.length_ofList, List.length_map, hp.2.1, hFp, ← mapM_length hps]
  · obtain ⟨rfl, htv⟩ := hp
    rw [hFp] at htv
    have hFg : F.gvals = (globsUsed s fi.module).2.1 := by rw [hF]
    let c := ctxOf s fi.module args code.locals (envX F args)
    have hc : c.Good (memOf s fi.module).isSome := good_ctxOf _ _ _ _ _
    have hgl : (fnInitX ps ls (globsUsed s fi.module).2.2).globs.length = c.ga.length := by
      have hg := globsUsed_ok s fi.module
      simp only [fnInitX, List.length_mapIdx, c, ctxOf]
      rw [← hg.typed.1, ← mapM_length hg.vals]
    have hw := Silmaril.Wasm.Auto.EquivUnroll.wp_xsexecU (m := .total) (P := P) (host := host) hc []
      (fun _ h => by simp at h) []
      (bodyPostT P host (Ty.ofList (ft.results.map ScalarType.toC)).length f vs₀
        (callPost f vs₀ ((sumSpecX F s).post s args))) fuel code.body hgl rfl hA
    have hρ : envX F args = envOfVals (args ++ (globsUsed s fi.module).2.1) := by
      rw [envX, hFg]
    have hs : c.storeOf (memOf s fi.module).isSome (fnInitX ps ls (globsUsed s fi.module).2.2) =
        s := by
      simp only [c]
      rw [hρ]
      exact storeOf_init htv s fi.module
    have hf : c.frameOf (fnInitX ps ls (globsUsed s fi.module).2.2) =
        Frame.forCall fi.module args code.locals := by
      simp only [c]
      rw [hρ]
      exact frameOf_init htv hls s fi.module
    have hst : c.stackOf (fnInitX ps ls (globsUsed s fi.module).2.2) = [] := rfl
    rw [hs, hf, hst] at hw
    have hb : c.mi.bytes = F.bytes := (bytes_ctxOf _ _ _ _ _).trans hFb.symm
    have hx : XOut .total P host c (memOf s fi.module).isSome A [] []
        (bodyPostT P host (Ty.ofList (ft.results.map ScalarType.toC)).length f vs₀
          (callPost f vs₀ ((sumSpecX F s).post s args))) := by
      unfold XOut
      split
      · rename_i T hT
        have hng : guardsOk (envX F args) F.bytes A.guards = false := by
          cases hk : guardsOk (envX F args) F.bytes A.guards
          · rfl
          · rw [guardsOk_iff, ← hb] at hk
            exact absurd (hk.symm.trans hT) (by simp)
        refine ⟨rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
        show Outcome.trap = resOutcome (fnOutX F args)
        simp only [fnOutX, outAt, hFf, hng]
        rfl
      · rename_i hT
        have hok : guardsOk (envX F args) F.bytes A.guards = true := by
          rw [guardsOk_iff, ← hb]
          exact hT
        rw [List.nil_append, List.append_nil]
        refine Wp.of_vals ?_
        have hlen : (c.stackOf A).reverse.length =
            (Ty.ofList (ft.results.map ScalarType.toC)).length := by
          have h₁ : A.stack.length = rs.length := by simpa using congrArg List.length hty
          rw [Ty.length_ofList, List.length_map, ← mapM_length hrs, ← h₁]
          simp [XCtx.stackOf]
        refine ⟨by simpa using hlen, rfl, Or.inl ⟨_, rfl, ?_⟩⟩
        show Outcome.normal _ = resOutcome (fnOutX F args)
        simp only [fnOutX, outAt, hFf, hok, ↓reduceIte, resOutcome, XCtx.stackOf, hb]
        rfl
    have hw' := hw.mpr hx
    simpa [expression, TWP] using hw'

/-! ## Exports of computed instances -/

theorem fnSumU?_inv {m : Module} {j : Nat} {F : FnSumX} (h : fnSumU? fuel m j = some F) :
    ∃ mt I ft fi, instance? m = some (mt, I) ∧ I.exports[j]? = some ft ∧
      I.store.funcs[I.addrs.getD j 0]? = some fi ∧ sumOfU fuel I.store ft fi = some F := by
  unfold fnSumU? at h
  split at h
  · rename_i mt I hI
    unfold fnSumUI at h
    split at h
    · rename_i ft fi hft hfi
      exact ⟨mt, I, ft, fi, hI, hft, hfi, h⟩
    · cases h
  · cases h

/-- Accepted arguments of a summarised export are typed. -/
theorem typedVals_of_invokeOkU {s : Store Nat} {a : Nat} {ft : FnType} {fi : FuncInst Nat}
    {F : FnSumX} (h : sumOfU fuel s ft fi = some F) (hfi : s.funcs[a]? = some fi)
    (he : Expand fi.type ft.toComp) {vs : List Val} (hvs : InvokeOk s a vs) :
    TypedVals F.params vs := by
  obtain ⟨fi', ps, rs, hfi', he', hf⟩ := hvs
  have : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  subst this
  have hc := Expand.func_eq he' he
  simp only [Silmaril.Wasm.Game.FnType.toComp] at hc
  injection hc with hc₁ hc₂
  rw [hc₁, Ty.toList_ofList] at hf
  obtain ⟨code, ps', rs', ls, A, -, hps, -, -, -, -, rfl⟩ := sumOfU_inv h
  exact typedVals_of_forall₂ hps hf

/-- The behaviour set of a summarised export on typed arguments. -/
theorem behaviours_of_fnSumU_typed {m : Module} {j : Nat} {F : FnSumX} (h : fnSumU? fuel m j = some F)
    {vs : List Val} (htv : TypedVals F.params vs) :
    behaviours P SingleThreaded.Det.noHost (instOf m).store (addrOf m j) vs =
      {(fnOutX F vs).toBehaviour} := by
  obtain ⟨mt, I, ft, fi, hI, hft, hfi, hs⟩ := fnSumU?_inv h
  have hinst : instOf m = I := by simp [instOf, hI]
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, hinst]
  rw [hinst, haddr]
  refine behaviours_eq_res_of_tfspec ?_ (tfspecU_of_sumOfU hs hfi (export_expand hI hft hfi))
    ⟨rfl, htv⟩ (fun _ _ ho => ho)
  intro x hx
  simp only [fnOutX, outAt] at hx
  split at hx <;> cases hx

/-- Typed arguments of a summarised export. -/
theorem typedVals_of_fnSumU {m : Module} {j : Nat} {F : FnSumX} (h : fnSumU? fuel m j = some F)
    {vs : List Val} (hvs : InvokeOk (instOf m).store (addrOf m j) vs) :
    TypedVals F.params vs := by
  obtain ⟨mt, I, ft, fi, hI, hft, hfi, hs⟩ := fnSumU?_inv h
  have hinst : instOf m = I := by simp [instOf, hI]
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, hinst]
  rw [hinst, haddr] at hvs
  exact typedVals_of_invokeOkU hs hfi (export_expand hI hft hfi) hvs

/-- **The behaviour set of a summarised export**: every accepted invocation terminates, and
returns or traps as `fnOutX F vs` says, at every profile. -/
theorem behaviours_of_fnSumU {m : Module} {j : Nat} {F : FnSumX} (h : fnSumU? fuel m j = some F)
    {vs : List Val} (hvs : InvokeOk (instOf m).store (addrOf m j) vs) :
    behaviours P SingleThreaded.Det.noHost (instOf m).store (addrOf m j) vs =
      {(fnOutX F vs).toBehaviour} :=
  behaviours_of_fnSumU_typed h (typedVals_of_fnSumU h hvs)

end Silmaril.Wasm.Auto2.Summ

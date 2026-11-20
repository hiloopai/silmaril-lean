module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.Simple
public import Silmaril.Proofs.Wasm.Component.Reference.LinkExp

/-!
# R3 for a simple exporter: the read-back of its core activation

`simple_bwd`: `simpleData` meets `RefData.Bwd`. The boundary of R3 is the core activation of an
export (`RefData.startCfg`), not the `canon lower`/`canon lift` wrapper around it, so the
read-back is a core-level backward simulation and the machine's core phase:

* `exp_back1`: `exp_run` (`LinkExp`) without the importer's part: a core run of the exporter's
  invocation in the shared store, renamed by any `g`, whose store relates to the exporter's
  store `π` by the exporter's `PartRel` alone, is the image of a run of the exporter from `π`
  (`reach_link_back`); it never stops at a callout; a return of values has the flat result
  types and is a returned call (`RetAt`) when its lift succeeds and a trapped call (`TrapAt`)
  when it fails; a core trap is a trapped call;
* `coreCfg_steps_inv2`: `coreCfg_steps_inv` keeping the machine run of the core phase up to the
  exit, and the exit step;
* `simple_bwd`: every machine run from `startCfg` is still in the core phase, or passed through
  a return of R2's shape (`Ends`, for the step `ret` or `trap` of the specification), or ended
  in a core trap, the specification step `trap` holding at the trapped core store.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Runs of the core phase, with their prefix -/

section Generic

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-- **Runs of a core activation** (`coreCfg_steps_inv`), keeping the machine run up to the
exit and the exit step. -/
theorem coreCfg_steps_inv2 {B : Config E σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {x : CoreSt E} {tr : List (Label E σ)} {m' : Config E σ}
    (h : Steps prof hr dispatch (coreCfg B th K segs rest x) tr m') :
    (∃ y, Relation.ReflTransGen (CoreStep E) x y ∧ m' = coreCfg B th K segs rest y) ∨
      ∃ y pre l m₁ tr₂, Relation.ReflTransGen (CoreStep E) x y ∧
        Steps prof hr dispatch (coreCfg B th K segs rest x) pre (coreCfg B th K segs rest y) ∧
        tr = pre ++ l :: tr₂ ∧ CoreExit B th K segs rest y l m₁ ∧
        Step prof hr dispatch (coreCfg B th K segs rest y) l m₁ ∧
        Steps prof hr dispatch m₁ tr₂ m' := by
  generalize hm : coreCfg B th K segs rest x = m at h
  induction h generalizing x with
  | refl => exact .inl ⟨x, .refl, hm.symm⟩
  | cons s r ih =>
    subst hm
    rcases coreCfg_step_inv s with ⟨rfl, y, hy, rfl⟩ | hx
    · rcases ih rfl with ⟨z, hz, e⟩ | ⟨z, pre, l, m₁, tr₂, hz, hp, e, hx, s', r'⟩
      · exact .inl ⟨z, .head hy hz, e⟩
      · exact .inr ⟨z, .core :: pre, l, m₁, tr₂, .head hy hz, .cons s hp, by rw [e]; rfl, hx, s',
          r'⟩
    · exact .inr ⟨x, [], _, _, _, .refl, .refl _, rfl, hx, s, r⟩

end Generic

/-! ## The exporter's runs in the shared store, without the importer -/

variable {P : Profile}

/-- **`exp_run` without the importer's part.** A core run, renamed by `g`, of the invocation of
export `x` of `I` (well formed at `π`) on the lowered `vs`, from a shared store related to the
exporter's store `π` by `PartRel` (the exporter's function owned), is the image of a run of the
exporter to `π'` (with `LinkSt`, the relation growing and touching only what the exporter owns,
the functions kept); it never stops at a callout; a return of values has the flat result types,
is a returned call when its lift succeeds and a trapped call when it fails; a core trap is a
trapped call. -/
theorem exp_back1 {c : Simple} {I : SInst} (hI : c.mod.IsInst I) {x : SimpleExport}
    (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat)) {vs : List IVal}
    (typed : ValTy.checkList x.ty.params vs = true) {π : Store Nat} (hw : I.WellFormed π)
    {ρ : Ren} {O : Own} (g : CanonHost (E3 P) → Nat) {σ : Store (CanonHost (E3 P))}
    (hR : PartRel ρ O π (Store.mapH g σ)) (hF : FnPre ({} : Store Nat) (Store.mapH g σ) π)
    (hO : O.fn (I.addrs.getD x.core 0)) {e : CoreSt (E3 P)}
    (he : Relation.ReflTransGen (CoreStep (E3 P))
      (σ, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) e) :
    ∃ (π' : Store Nat) (t' : STh) (ρ' : Ren) (O' : Own),
      LinkSt ({} : Store Nat) ρ' O' (π', t') (Store.mapH g e.1, e.2) ∧
      PartRel ρ' O' π' (Store.mapH g e.1) ∧ Grow ρ O ρ' O' (Store.mapH g σ) ∧
      Touch ρ O (Store.mapH g σ) (Store.mapH g e.1) ∧ π'.funcs = π.funcs ∧
      (∀ h ys, (E3 P).status e.1 e.2 ≠ .callout h ys) ∧
      (∀ zs, (E3 P).status e.1 e.2 = .returned (.values zs) →
        zs.map (·.type) = ValTy.flatList x.ty.results ∧
        (∀ ws, liftArgs x.ty.results zs = some ws → RetAt P c I x vs π ws π') ∧
        (liftArgs x.ty.results zs = none → TrapAt P c I x vs π π')) ∧
      ((E3 P).status e.1 e.2 = .returned .trap → TrapAt P c I x vs π π') := by
  obtain ⟨nm, hcx⟩ := hcore
  have hk : x.core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcx).1
  have hL₀ := exp_invoke hR hF hO (lowerArgs x.ty.params vs)
  obtain ⟨ts, htyped, -⟩ := Silmaril.Wasm.Game.ScalarInstance.invoke_typed hw
    (opAt hI hk (exp_hxs hcx typed hk))
  have hrun : Silmaril.Wasm.Game.Reach P (Store.mapH g σ,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) (Store.mapH g e.1, e.2) :=
    reach_mapH g (coreSteps_internalP he)
  obtain ⟨⟨π', t'⟩, ρ', O', prun, hL, hgr, htc, hs', ht'⟩ :=
    reach_link_back hrun hL₀ hw.storeOk htyped
  have B : ExpBack P c I x vs π π' t' (Store.mapH g e.1, e.2) :=
    ⟨hI, ⟨nm, hcx⟩, typed, hw, prun, ⟨ρ', O', hL⟩, hs', ⟨ts, ht'⟩⟩
  have hcode : ((e.2).config (Store.mapH g e.1)).code = ((e.2).config e.1).code :=
    config_code_mapH g e.1 e.2
  have hrel : PartRel ρ' O' π' (Store.mapH g e.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store, reloc_empty] at h
  refine ⟨π', t', ρ', O', hL, hrel, hgr, htc, reach_funcs' prun, ?_, ?_, ?_⟩
  · intro h ys hst
    obtain ⟨E, a', h', args', hd⟩ := status_callout hst
    obtain ⟨E', hd'⟩ := decompose?_mapH g hd
    exact B.no_callout (hcode ▸ hd')
  · intro zs hst
    obtain ⟨cvs, hc, hm⟩ := status_values hst
    obtain ⟨hty, -, hret⟩ := B.values (hcode ▸ hc) hm
    refine ⟨hty, fun ws hws => (hret ws hws).1, fun hn => ?_⟩
    obtain ⟨vs', hv', hmap⟩ := values_back P hL hs' ht' (hcode ▸ hc)
    have hvv : vs'.map (linkMap ({} : Store Nat) ρ').val = vs' :=
      map_val_flat _ (show (vs'.map (linkMap ({} : Store Nat) ρ').val).mapM
        Silmaril.Wasm.SingleThreaded.toFlat? = some zs by rw [hmap]; exact hm)
    have hcv : vs' = cvs := hvv.symm.trans hmap
    refine ⟨typed, t', .values cvs, prun, hcv ▸ hv', ?_⟩
    simp only [coreRes, hm, liftOutcome, hn]
  · intro hst
    rcases status_trap hst with hc | ⟨b, hc⟩
    · exact ⟨typed, t', .trap, prun, trap_back P hL hs' ht' (hcode ▸ hc), rfl⟩
    · exact (throwing_back P hL hs' ht' (hcode ▸ hc)).elim

/-! ## R3 -/

/-- **R3 for a simple exporter**: every machine run of its core activation (without host
events, in any frame and on any thread) is still in the core phase, or passed through a return
of R2's shape for the step `ret` (results that lift) or `trap` (results that do not), or ended in
a core trap, where the step `trap` holds at the trapped core store. -/
theorem simple_bwd {c : Simple} (hc : c.Good) {I : SInst} (hI : c.mod.IsInst I) :
    (simpleData P c I).Bwd := by
  intro pl s w vs x hx htyped S F hH σ prof impl M th K segs rest hM hlock _ tr m' run _
  subst hM
  have hwx := List.getElem?_eq_some_iff.mp hx
  have hwl : w < c.exports.length := by
    have := hwx.1
    rwa [LinkedG.ofSimple_length] at this
  have hxty : x.ty = c.exports[w].ty := by
    rw [← hwx.2]
    exact LinkedG.ofSimple_ty c hwx.1 hwl
  have hxm : c.exports[w] ∈ c.exports := List.getElem_mem hwl
  have haddr : sAddr c I w = I.addrs.getD c.exports[w].core 0 := by
    simp [sAddr, List.getElem?_eq_getElem hwl]
  obtain ⟨ρ, O, hR, hO, rfl⟩ := hH.rel
  have hRg : PartRel ρ O s (Store.mapH (hIdx M.core) M.core) := partRel_mapH hR
  have hFg : FnPre ({} : Store Nat) (Store.mapH (hIdx M.core) M.core) s :=
    fnPre_mapH hH.free hH.fn
  have hOw : O.fn (I.addrs.getD c.exports[w].core 0) := hO ▸ owned_init hc hI _ hxm
  obtain ⟨nm, hcx⟩ := hc.core _ hxm
  have typed : ValTy.checkList c.exports[w].ty.params vs = true := hxty ▸ htyped
  have hstart : (simpleData P c I).startCfg pl w x vs M th K segs rest =
      coreCfg M th K segs rest (M.core, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
        (I.addrs.getD c.exports[w].core 0) (lowerArgs c.exports[w].ty.params vs)) := by
    show { M with ctl := ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (sAddr c I w)
      (lowerArgs x.ty.params vs)) K, segs⟩ :: rest } = _
    rw [haddr, hxty]
    rfl
  rw [hstart] at run ⊢
  rcases coreCfg_steps_inv2 run with ⟨y, -, rfl⟩ |
      ⟨y, pre, l, m₁, tr₂, hy, hpre, rfl, hxit, st, r₂⟩
  · exact .inl ⟨List.cons_ne_nil _ _, hlock⟩
  obtain ⟨π', t', ρ', O', hL, hrel, hgr, htc, hfπ, hnco, hval, htrap⟩ :=
    exp_back1 hI ⟨nm, hcx⟩ typed hH.wf (hIdx M.core) hRg hFg hOw hy
  have hfe : (y.1 : Store (CanonHost (E3 P))).funcs = (M.core : Store _).funcs :=
    coreSteps_funcs hy
  have hW := within_of_touch' htc hfe
  have hG := grows_of_grow (grow_unmapH hgr)
  rcases hxit with ⟨zs, hzs, rfl, rfl⟩ | ⟨htr, rfl, rfl⟩ | ⟨h, ys, hco⟩
  · obtain ⟨hty, hret, hnl⟩ := hval zs hzs
    have hty' : zs.map (·.type) = ValTy.flatList x.ty.results := by rw [hxty]; exact hty
    have r₁ := Adequacy.steps_append hpre (.cons st (.refl _))
    cases hus : liftArgs c.exports[w].ty.results zs with
    | some ws =>
      have hRA := hret ws hus
      have hH' := shold_after hH hO hL hrel hgr hfπ (RetAt.wellFormed hI ⟨nm, hcx⟩ hH.wf hRA)
      refine .inr (.inl ⟨pre ++ [.tau], tr₂, _, some (.vals ws), π', by simp, r₁, r₂,
        .ret hwl hRA, .inl ⟨{ M.ref with core := y.1 }, M.conts, zs, img ρ' O', rfl, hty',
          ?_, storeExt_core c I pl M.ref y.1, hH', hW, hG⟩, List.cons_ne_nil _ _⟩)
      show liftArgs x.ty.results zs = some ws
      rw [hxty]
      exact hus
    | none =>
      have hT := hnl hus
      have hH' := shold_after hH hO hL hrel hgr hfπ (hT.wellFormed hI ⟨nm, hcx⟩ hH.wf)
      refine .inr (.inl ⟨pre ++ [.tau], tr₂, _, none, π', by simp, r₁, r₂,
        .trap hwl hT, .inl ⟨{ M.ref with core := y.1 }, M.conts, zs, img ρ' O', rfl, hty',
          ?_, storeExt_core c I pl M.ref y.1, hH', hW, hG⟩, List.cons_ne_nil _ _⟩)
      show liftArgs x.ty.results zs = none
      rw [hxty]
      exact hus
  · have hT := htrap htr
    have hH' := shold_after hH hO hL hrel hgr hfπ (hT.wellFormed hI ⟨nm, hcx⟩ hH.wf)
    rw [steps_of_locked rfl rfl r₂]
    exact .inr (.inr ⟨rfl, fun _ => ⟨π', { M.ref with core := y.1 }, img ρ' O', .trap hwl hT,
      rfl, rfl, hH'⟩⟩)
  · exact (hnco h ys hco).elim

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef

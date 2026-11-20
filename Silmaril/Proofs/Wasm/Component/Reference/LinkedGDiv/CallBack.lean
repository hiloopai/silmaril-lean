module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.Classify
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.Call
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.Sess

/-!
# Diverging linked calls through an abstract exporter, backward: calls and sessions

* `linkDiv_invB`: from a configuration between calls (`ReadyB`), a diverging top-level call of
  the importer's export `j` on typed arguments is a round that never answers
  (`LinkedG.RoundDiv`): the host's invocation and the importer's `canon lift` are a live run to
  its core activation (`call_atG`), which diverges; `ldiv_classifyG` classifies the divergence.
  Its fourth case, an exit of the importer's activation other than a callout, does not diverge
  here: the importer's results are lifted and the call resolves with the host in control
  (`CallAtG.ret`), or the lift traps (`CallAtG.trap`), or the activation trapped;
* `sessDivL_invB`: a diverging resumable session from a configuration between calls (no waiting
  thread) is a specification session (`linkCall_invB` per call) ending in a round that never
  answers;
* `divRefToSpecG`: from instantiation (`instBehavioursG_toRef`, `readyB_init`),
  `LinkedG.refDivs ⊆ LinkedG.sessDivs`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload checkLower sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-- A specification trap is a trap. -/
theorem trapsFrom_of_S {M : Machine.Config (E3 P) σ} {c : (E3 P).Store (CanonHost (E3 P))}
    (H : TrapsAtS prof P impl M c) : TrapsFrom prof P impl M := by
  obtain ⟨tr, mT, r, -, h₁, hl, hu, -⟩ := H
  exact ⟨tr, mT, r, h₁, hl, hu⟩

section Call

variable {lg : LinkedG} {d : lg.exp.RefData P} {pl : d.Pl} {ii : Nat} {Ii : SInst}
  {s₀ ui : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {fs : List (CFuncInst (core3P P))}
  {jf : Nat → Nat}

/-- **A diverging linked call between calls is a specification round that never answers.** -/
theorem linkDiv_invB (ST : StatB P lg d pl ii Ii s₀ ui F₀ g tr Oc₀ fs jf) (hFr : d.Frame)
    (hB : d.Bounded) (hDv : d.Div) {m : Machine.Config (E3 P) σ} {s : lg.exp.St}
    {u : Store Nat} {k : Nat} (R : ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m s u k)
    (j : Fin lg.imp.exports.length) {vs : List IVal}
    (hvs : ValTy.checkList lg.imp.exports[j].ty.params vs = true)
    (hcd : CallDiverges prof (fun _ _ => false) (DI P impl) m ⟨k⟩ ⟨jf j⟩ (vs.map toRefVal)) :
    LinkedG.RoundDiv P lg Ii u s j vs := by
  have SI := ST.imp
  have hx : lg.imp.exports[j] ∈ lg.imp.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcore⟩ := SI.good.core _ hx
  have hk : lg.imp.exports[j].core < lg.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hflat : lg.imp.mod.exports[lg.imp.exports[j].core] = (nm, lg.imp.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : (lowerArgs lg.imp.exports[j].ty.params vs).map (·.type) =
      lg.imp.mod.exports[lg.imp.exports[j].core].2.params := by
    rw [hflat]
    exact lowerList_types _ _ hvs
  obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI SI.inst hk hxs
  have hft' : Ii.exports.get f.1 = fnOf lg.imp.exports[j].ty.flat := by rw [hft, hflat]
  obtain ⟨hmax, hmaxr, hres⟩ := ST.wire.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := ST.wire.floats.1 _ hx
  have ha : Ii.addrs.getD lg.imp.exports[j].core 0 = Ii.addr f.1 := by
    rw [← hf₁]
    rfl
  have hfj : m.store.funcs[jf j]? = some (.lifted (s₀.funcs.length + Ii.addr f.1)
      (liftedFt lg.imp.exports[j]) {} ⟨ii⟩) := by
    rw [R.funcs, ← ha]
    exact ST.lifted j
  have hck : checkLower lg.imp.exports[j].ty.params vs =
      some (lowerArgs lg.imp.exports[j].ty.params vs) := by
    simp only [checkLower, hvs, ↓reduceIte]
  obtain ⟨ιi, hii, hth, hleave⟩ := R.imp
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atG (impl := impl) prof m R.lock k
    (jf j) _ ii lg.imp.exports[j] vs hpf hvs hmax hres hmaxr hrf hii hth hfj
  -- the invariants at the start of the importer's core activation
  have hR₀ : LReadyG d pl Ii s₀ ui F₀ g Oc₀ M₀.ref s u := by
    refine lready_frame hFr R.inv hat.core (by show M₀.store.funcs = _; rw [hat.store]; rfl) ?_
    intro i hi
    show M₀.store.insts[i]? = _
    rw [hat.store]
    exact List.getElem?_set_ne (fun h => ST.out (by rw [h]; exact hi))
  obtain ⟨F, hI₀⟩ := linv_readyG hR₀ ST.own (f := f) hf₂
  have SIu : ImpStatG P lg.imp Ii u F₀ g tr := ⟨SI.good, SI.inst, R.inv.wfI, SI.tramp, SI.inv⟩
  obtain ⟨F₁, -, -, -, -, -, -, hH₀⟩ := R.inv.rel
  have hFG₀ : FrameG d pl ii th M₀.store := by
    refine ⟨by rw [hat.store]; exact R.lock, ?_, ?_, ST.out, ?_⟩
    · rw [hat.store, hat.thread]
      have h₁ : ArenaField.threads.get? (storeG₃ m.store lg.imp.exports[j] ii
          (enterInst ιi ⟨m.store.threads.length⟩) k (vs.map toRefVal))
          ⟨m.store.threads.length⟩ = some ((thread₁ m.store.tasks).withIndex 1) :=
        threads_get_last rfl
      have h₂ : ArenaField.tasks.get? (storeG₃ m.store lg.imp.exports[j] ii
          (enterInst ιi ⟨m.store.threads.length⟩) k (vs.map toRefVal))
          ((thread₁ m.store.tasks).withIndex 1).task =
          some ((taskG₁ lg.imp.exports[j] ii m.store.callers
            ⟨m.store.threads.length⟩).withState .started) :=
        tasks_get_last rfl
      simp only [instOfThread?, h₁, h₂, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
    · rw [hat.store]
      exact ⟨enterInst ιi ⟨m.store.threads.length⟩, List.getElem?_set_self (lt_of_getElem? hii),
        hleave⟩
    · intro w hw
      obtain ⟨xe, hxe⟩ := hw
      obtain ⟨-, hblk⟩ := hFr.lifted pl s m.ref F₁ w xe hH₀ hxe
      rw [hat.store]
      show ∃ ι, (List.set m.store.insts ii (enterInst ιi ⟨m.store.threads.length⟩))[d.inst pl w]? =
        some ι ∧ _
      have hne : ii ≠ d.inst pl w := fun h => ST.out (by rw [h]; exact hblk)
      rw [List.getElem?_set_ne hne]
      exact R.exp w ⟨xe, hxe⟩
  have hM₀ : M₀ = coreCfg M₀ th K segs rest (M₀.ref.core,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs lg.imp.exports[j].ty.params vs)) := eq_coreCfg hat.ctl
  -- the divergence
  obtain ⟨m₂, st, d₂⟩ := hcd
  have hm₂ : m₂ = invokedG m k (jf j) (vs.map toRefVal) := by
    cases st
    rfl
  subst hm₂
  have d₀ := hpre.diverges d₂
  rw [hM₀] at d₀
  let z₀ : DStG P σ lg.exp := ⟨M₀.conts, M₀.ref, F, (M₀.core,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs lg.imp.exports[j].ty.params vs)), (u, Ii.initThread f), s⟩
  obtain ⟨ρc₀, Oc₀', hL₀, hfn₀, hgl₀, hD₀⟩ := hI₀.rel
  have hz₀ : DInvG prof impl d pl ii Ii s₀ u F₀ g Oc₀ f th K segs rest M₀
      (footUnion F (img ρc₀ Oc₀')) M₀.core z₀ :=
    ⟨d₀, hI₀, hFG₀, callExt_refl _, relT_start hL₀ hfn₀ hgl₀ hD₀⟩
  obtain ⟨cs, dss, z, trc, hpath, hrel, hexp, hz, -, -, hsrc⟩ :=
    ldiv_classifyG SIu ST.wire hFr hDv hB hz₀
  have hround : ∀ (src : Linked2.DivB P z.x.1 z.x.2 ∨ LinkedG.DivA P lg Ii f z.x.1 z.x.2 z.s ∨
      LinkedG.Chatter P lg Ii f z.x.1 z.x.2 z.s), LinkedG.RoundDiv P lg Ii u s j vs :=
    fun src => ⟨⟨j, vs, f, cs, dss⟩, z.x.1, z.x.2, z.s, rfl, rfl, ⟨_, hck, hf₁, hf₂, hrel⟩,
      .cons (.call u f) hpath, hexp, src⟩
  rcases hsrc with h | h | h | hX
  · exact hround (.inl h)
  · exact hround (.inr (.inl h))
  · exact hround (.inr (.inr h))
  -- an exit of the importer's activation does not diverge
  exfalso
  obtain ⟨y₁, x₁, lb, m₁, -, -, hI₁, -, hnco, hx, d₁⟩ := hX
  have hXc : CallExt d pl M₀.ref { z.S with core := y₁.1 } :=
    callExt_trans hz.ext (callExt_refl _)
  have hlS : ({ z.S with core := y₁.1 } : RefStore (E3 P)).lockdown = false := hz.frame.lock
  obtain ⟨ρc, Oc, hL, -⟩ := hI₁.rel
  obtain ⟨ts, hst', htt⟩ := linvG_typed SIu hI₁
  rcases hx with ⟨zs, hst, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨h', ys', hc'⟩
  · -- the importer returned values
    obtain ⟨cvs, hcode, hm⟩ := status_values hst
    have hc : (y₁.2.config (Store.mapH g y₁.1)).code = Silmaril.Wasm.Execution.Core.vals cvs :=
      (config_code_mapH g y₁.1 y₁.2).trans hcode
    obtain ⟨vs', hv, hvm⟩ := values_back P hL hst' htt hc
    have hm' : (vs'.map (linkMap s₀ ρc).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? =
        some zs := by
      rw [hvm]
      exact hm
    have hvs' : vs' = cvs := (map_val_of_mapM _ hm').symm.trans hvm
    have hr : Silmaril.Wasm.Game.ResultAt x₁.1 x₁.2 (.values cvs) := hvs' ▸ hv
    obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run SIu.wf
      (valEnv_throwsBelow Ii _) hI₁.run hr
    have hty : zs.map (·.type) = ValTy.flatList lg.imp.exports[j].ty.results :=
      results_typed hft' hw hm
    cases hl : liftArgs lg.imp.exports[j].ty.results zs with
    | none =>
      exact TrapsFrom.not_diverges (trapsFrom_of_S
        (hat.trap z.S.toCStore z.C y₁ zs hlS hty hl)) d₁
    | some ws =>
      have hM₀s : M₀.ref.toCStore = _ := hat.store
      obtain ⟨RT, hRT⟩ := prefix_concat_split (hM₀s ▸ hXc.tasks)
      obtain ⟨RH, hRH⟩ := prefix_concat_split (hM₀s ▸ hXc.threads)
      obtain ⟨CL, hCL⟩ := prefix_concat_split (hM₀s ▸ hXc.callers)
      have hIi : ({ z.S with core := y₁.1 } : RefStore (E3 P)).insts[ii]? =
          some (enterInst ιi ⟨m.store.threads.length⟩) := by
        rw [hXc.insts_out ii ST.out, hM₀s]
        exact List.getElem?_set_self (lt_of_getElem? hii)
      obtain ⟨tr₃, mE, hlr, hmE⟩ := hat.ret z.S.toCStore z.C RT RH CL y₁ zs ws hRT
        hRH hCL hIi hlS hty hl
      have hmEc : mE.ctl = [] := by rw [hmE]
      exact not_diverges_of_ctl_nil hmEc (hlr.diverges d₁)
  · exact not_diverges_trapCfg _ d₁
  · exact hnco h' ys' hc'

/-- **Reference sessions ending in a diverging call are specification sessions ending in a round
that never answers**, between calls. -/
theorem sessDivL_invB (ST : StatB P lg d pl ii Ii s₀ ui F₀ g tr Oc₀ fs jf) (hFr : d.Frame)
    (hBw : d.BwdF) (hRes : d.Resume) (hB : d.Bounded) (hDv : d.Div)
    (j : Fin lg.imp.exports.length) {vs : List IVal}
    (hvs : ValTy.checkList lg.imp.exports[j].ty.params vs = true) :
    ∀ (calls : List (Fin lg.imp.exports.length × List IVal)) (m : Machine.Config (E3 P) σ)
      (s : lg.exp.St) (u : Store Nat) (k : Nat) (outs : List (Option (List RVal))),
      ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m s u k → m.store.waiting = [] →
      SimpleI.TypedCalls lg.imp calls →
      SessDiv prof (linkHost impl) m k (callArgsG lg jf calls) outs ⟨jf j⟩ (vs.map toRefVal) →
      ∃ (outs' : List (Option (List IVal))) (u' : Store Nat) (s' : lg.exp.St),
        LinkedG.SessSpec P lg Ii u s calls outs' u' s' ∧ outs = refOuts outs' ∧
        LinkedG.RoundDiv P lg Ii u' s' j vs
  | [], m, s, u, k, outs, R, _, _, hS => by
    change SessDiv prof (linkHost impl) m k [] outs ⟨jf j⟩ (vs.map toRefVal) at hS
    cases hS with
    | div hd => exact ⟨[], u, s, .nil u s, rfl, linkDiv_invB ST hFr hB hDv R j hvs hd⟩
  | (j', vs') :: calls, m, s, u, k, outs, R, hwt, ht, hS => by
    have hvs' : ValTy.checkList lg.imp.exports[j'].ty.params vs' = true :=
      ht _ List.mem_cons_self
    have ht' : SimpleI.TypedCalls lg.imp calls := fun q hq => ht q (List.mem_cons_of_mem _ hq)
    change SessDiv prof (linkHost impl) m k
      ((⟨jf j'⟩, vs'.map toRefVal) :: callArgsG lg jf calls) outs ⟨jf j⟩ (vs.map toRefVal) at hS
    cases hS with
    | ret hcall hS' =>
      obtain ⟨dr, u₁, s₁, o, rfl, rfl, hok, hpath, hexp, hans, hback⟩ :=
        linkCall_invB ST hFr hBw hRes hB R hwt j' hvs' hcall
      cases o with
      | none => exact absurd hback.1 (by simp)
      | some ws =>
        obtain ⟨hout, R₁, hw₁⟩ := hback
        cases hout
        obtain ⟨outs', u', s', hspec, rfl, hd⟩ :=
          sessDivL_invB ST hFr hBw hRes hB hDv j hvs calls _ s₁ u₁ (k + 1) _ R₁ (hw₁.trans hwt)
            ht' hS'
        exact ⟨some ws :: outs', u', s', .round dr hok hpath hexp hans hspec, rfl, hd⟩
    | trap hcall hS' =>
      obtain ⟨dr, u₁, s₁, o, rfl, rfl, hok, hpath, hexp, hans, hback⟩ :=
        linkCall_invB ST hFr hBw hRes hB R hwt j' hvs' hcall
      cases o with
      | some ws => exact absurd hback.1 (by simp)
      | none =>
        obtain ⟨-, R₁⟩ := hback
        obtain ⟨outs', u', s', hspec, rfl, hd⟩ :=
          sessDivL_invB ST hFr hBw hRes hB hDv j hvs calls _ s₁ u₁ (k + 1) _ R₁ hwt ht' hS'
        exact ⟨none :: outs', u', s', .round dr hok hpath hexp hans hspec, rfl, hd⟩

end Call

/-! ## From instantiation -/

variable {lg : LinkedG}

/-- **Reference divergence of a linked component with an abstract exporter is specification
divergence**: for an exporter meeting R1, R3 (`BwdF`), R4 (`InitUX`), R5, R6 and R7, an importer
as in `Linked2`, typed calls and a typed pending call, `LinkedG.refDivs ⊆ LinkedG.sessDivs`. -/
theorem divRefToSpecG (P : Profile) (prof : ProfileKind) {d : lg.exp.RefData P}
    (hInit : d.InitUX) (hFr : d.Frame) (hBw : d.BwdF) (hRes : d.Resume) (hB : d.Bounded)
    (hDv : d.Div) (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree) (hS : Linked2.ModSplitOk lg.imp.mod.mod)
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) (calls : List (Fin lg.imp.exports.length × List IVal))
    (j : Fin lg.imp.exports.length) (vs : List IVal) (ht : SimpleI.TypedCalls lg.imp calls)
    (hvs : ValTy.checkList lg.imp.exports[j].ty.params vs = true) {Ii : SInst}
    (hI : lg.imp.mod.IsInst Ii) :
    LinkedG.refDivs P prof lg impl h₀ calls j vs ⊆ LinkedG.sessDivs P lg Ii calls j vs := by
  intro outs hout
  obtain ⟨m₁, pl, F, es, r, hA, hrs, hh, hall⟩ :=
    instBehavioursG_toRef hInit hFr hW hIg hIi hIa ⟨hS.data, hS.elems⟩ hNI hI prof impl h₀
  obtain ⟨m₀, inst, es', fs, f, hr, hfs, hf, hSq⟩ := hout
  rw [hall] at hr
  obtain ⟨rfl, rfl, rfl⟩ := InstResult.instance.inj (Set.mem_singleton_iff.1 hr)
  have hfs' : fs = calls.map fun q => (⟨m₁.store.funcs.length + q.1⟩ : FuncId) :=
    Option.some.inj (hfs.symm.trans (mapM_lookupG hIg _ calls))
  have hf' : f = ⟨m₁.store.funcs.length + j⟩ :=
    Option.some.inj (hf.symm.trans (exportMapG_lookup hIg _ j))
  subst hfs' hf'
  rw [zip_callArgsG'] at hSq
  have ST := statB_init hW hn hIg hIa hff hI hA.toInitAtX hh
  have R := readyB_init hFr hB hW hn hI hS hA.toInitAtX rfl rfl rfl hrs hh
  obtain ⟨outs', u', s', hspec, he, hd⟩ :=
    sessDivL_invB ST hFr hBw hRes hB hDv j hvs calls _ _ _ 0 _ R (afterG_waiting hA) ht hSq
  obtain rfl := SessionAdequacy.refOuts_inj he
  exact ⟨u', s', hspec, hd⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv

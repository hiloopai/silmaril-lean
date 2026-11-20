module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv.Bwd

/-!
# The importer's side of the read-back against an abstract exporter

* `first_stop`: every run to a configuration that is not live passes, without host events,
  through a first configuration that is not live (host events need an empty control chain);
* `tick_back`: a tick from a configuration ready for the host with no waiting thread returns
  to it through a live run;
* `linvG_typed`, `linvG_reach_back`, `linvG_callout_back`: the backward counterparts of
  `LInvG.reach_fwd`/`LInvG.callout_fwd` (`LInv.reach`/`LInv.callout` of `LinkSeg` with the
  exporter's half replaced by `d.Hold`): a core run of the shared thread is the image of a run of
  the importer's part, keeping `LInvG` (R1 for the exporter's relation); a callout of the
  shared thread is a typed import question of the part, to the trampoline `tr k`;
* `impRel_linkG`: `impRel_link` for any importer.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Runs up to the first stop -/

section Generic

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-- A step from a live configuration is not a host event. -/
theorem not_host_of_live {m m' : Machine.Config E σ} {l : Label E σ} (hl : Live m)
    (s : Step prof hr dispatch m l m') : ∀ ev, l ≠ .host ev := by
  intro ev e
  subst e
  exact hl.1 (Step.host_ready s).1

/-- **The first stop of a run**: a run to a configuration that is not live passes, without host
events, through a configuration that is not live. -/
theorem first_stop {m m' : Machine.Config E σ} {tr : List (Label E σ)}
    (r : Steps prof hr dispatch m tr m') (hm : ¬ Live m') :
    ∃ tr₁ tr₂ M, tr = tr₁ ++ tr₂ ∧ Steps prof hr dispatch m tr₁ M ∧ ¬ Live M ∧
      (∀ ev, Label.host ev ∉ tr₁) ∧ Steps prof hr dispatch M tr₂ m' := by
  induction r with
  | refl m₀ =>
    refine ⟨[], [], m₀, rfl, Steps.refl _, hm, ?_, Steps.refl _⟩
    intro ev h
    simp at h
  | @cons m₁ m₂ m₃ l tr s r ih =>
    by_cases hl : Live m₁
    · obtain ⟨tr₁, tr₂, M, rfl, r₁, hM, hh, r₂⟩ := ih hm
      refine ⟨l :: tr₁, tr₂, M, rfl, .cons s r₁, hM, ?_, r₂⟩
      intro ev hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact not_host_of_live hl s ev h.symm
      · exact hh ev h
    · refine ⟨[], l :: tr, m₁, rfl, Steps.refl _, hl, ?_, Steps.cons s r⟩
      intro ev h
      simp at h

/-- A host-free run from a configuration whose control chain is empty is empty. -/
theorem steps_nil_of_ctl {m m' : Machine.Config E σ} {tr : List (Label E σ)}
    (hc : m.ctl = []) (r : Steps prof hr dispatch m tr m') (hh : ∀ ev, Label.host ev ∉ tr) :
    m' = m := by
  cases r with
  | refl => rfl
  | cons s _ =>
    obtain ⟨ev, rfl⟩ := Step.host_of_ctl_nil hc s
    exact absurd List.mem_cons_self (hh ev)

end Generic

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-- **A tick from a configuration ready for the host with no waiting thread** returns to it. -/
theorem tick_back {m m₁ : Machine.Config (E3 P) σ} (hl : m.store.lockdown = false)
    (hw : m.store.waiting = [])
    (hs : Step prof (fun _ _ => false) (DI P impl) m (.host .tick) m₁) :
    ∃ trT, LRun prof (fun _ _ => false) (DI P impl) m₁ trT m := by
  cases hs with
  | hostTick hR =>
    have hc : m.ctl = [] := hR.1
    have hcand : (enterHostSt m.store).candidates (fun _ => false) = [] := by
      simp [CStore.candidates, enterHostSt, hw]
    apply Exists.intro
    apply LRun.prog rfl (fun _ _ e => by cases e) (by exact hl) (Step.modify rfl)
    apply LRun.prog rfl (fun _ _ e => by cases e) (by exact hl) (Step.get rfl)
    apply LRun.prog rfl (fun _ _ e => by cases e) (by exact hl) (Step.hostGet rfl)
    simp only [hcand]
    apply LRun.prog rfl (fun _ _ e => by cases e) (by exact hl) (Step.modify rfl)
    apply LRun.prog rfl (fun _ _ e => by cases e) (by exact hl) (Step.hostDone rfl)
    convert LRun.refl _ using 1
    obtain ⟨st, h, co, ctl, pe, re, ca⟩ := m
    simp only at hc
    subst hc
    rfl

/-! ## The importer's part, backward -/

section Inv

variable {b : SimpleI} {Ii : SInst} {u₀ s₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))}
  {g : CanonHost (E3 P) → Nat} {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {f : Ii.F.Op}
  {e : ExpSpec} {d : e.RefData P} {pl : d.Pl}

/-- The importer's part thread is typed. -/
theorem linvG_typed (SI : ImpStatG P b Ii u₀ F₀ g tr) {s : e.St} {S : RefStore (E3 P)}
    {F : CoreFoot} {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s S F y x) :
    ∃ ts, Silmaril.Wasm.Execution.Core.StoreOk x.1 ∧
      Silmaril.Wasm.SingleThreaded.ThreadOk x.1 x.2 ts := by
  obtain ⟨ts, hg₀⟩ := SEnvTyping.good_invoke SI.wf f
  have hg := SEnvTyping.good_ssteps (P := P) SI.wf (valEnv_throwsBelow Ii _)
    (x := (_, ())) (y := (x.2.config x.1, ())) hg₀ hI.run
  have hs : Silmaril.Wasm.Execution.Core.StoreOk (x.2.config x.1).store :=
    Silmaril.Wasm.SingleThreaded.ConfigOk.storeOk hg.ok
  rw [Silmaril.Wasm.SingleThreaded.Thread.config_store] at hs
  exact ⟨ts, hs, hg.ok⟩

/-- **A core run of the shared thread is the image of a run of the importer's part**, `LInvG`
holding at its end with the same exporter state and footprint (R1). -/
theorem linvG_reach_back (SI : ImpStatG P b Ii u₀ F₀ g tr) (hFr : d.Frame) {s : e.St}
    {M : RefStore (E3 P)} {F : CoreFoot} {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M F y x) {y' : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P)) y y') :
    ∃ x', LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s { M with core := y'.1 } F y' x' ∧
      Silmaril.Wasm.Game.Reach P x x' := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD⟩ := hI.rel
  obtain ⟨ts, hs, ht⟩ := linvG_typed SI hI
  have hrun := reach_mapH g (coreSteps_internalP hy)
  obtain ⟨x', ρc', Oc', prun, hL', hgr, htc, -, -⟩ := reach_link_back hrun hL hs ht
  have hfy : y'.1.funcs = y.1.funcs := reach_funcs' (coreSteps_internalP hy)
  have hag : F.Agree (M.core : Store (CanonHost (E3 P))) y'.1 := by
    rw [hI.core]
    exact agree_of_touch hD htc hfy
  exact ⟨x', ⟨⟨ρc', Oc', hL', hgr.fn.trans hfn, hgr.gl.trans hgl, hD.after_part hgr htc⟩,
    hFr.agree pl s M _ F hI.hold hag (List.prefix_refl _) (fun _ _ => rfl), rfl,
    hfy.trans hI.funcs, hI.run.trans (reach_ssteps prun)⟩, prun⟩

/-- **A callout of the shared thread is a typed import question of the importer's part**, to
the trampoline `tr k` of the import `k`. -/
theorem linvG_callout_back (SI : ImpStatG P b Ii u₀ F₀ g tr) {s : e.St} {M : RefStore (E3 P)}
    {F : CoreFoot} {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M F y x) {h : CanonHost (E3 P)} {ys : List Flat}
    (hst : (E3 P).status y.1 y.2 = .callout h ys) :
    ∃ (k : Nat) (args : List Silmaril.Wasm.Execution.Core.Val) (q : Ii.E.Op),
      Silmaril.Wasm.Game.CalloutAt x.1 x.2 k args ∧ Ii.importOp? k args = some q ∧
      h = tr k := by
  obtain ⟨E', A, args', hd, -⟩ := status_callout_redex hst
  obtain ⟨fi, -, -, -, hf, hcode, -⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  rw [hI.funcs] at hf
  have htr : tr (g h) = h := SI.tramp A fi h hf hcode
  generalize hk : g h = k at htr
  subst htr
  have hg : g (tr k) = k := hk
  have hdm : Silmaril.Wasm.SingleThreaded.decompose? (Store.mapH g y.1)
      (y.2.config (Store.mapH g y.1)).code = some (E', A, k, args') := by
    refine (decompose?_config_mapH g y.1 y.2).trans ?_
    rw [hd]
    simp only [Option.map_some, mapR, hg]
  obtain ⟨ρc, Oc, hL, -⟩ := hI.rel
  obtain ⟨ts, hs, ht⟩ := linvG_typed SI hI
  obtain ⟨E, a, args, hdx, -, -, -⟩ := callout_back P hL hs ht hdm
  have hdx' : Silmaril.Wasm.SingleThreaded.decompose? (x.2.config x.1).store
      (x.2.config x.1).code = some (E, a, k, args) := by
    rw [Silmaril.Wasm.SingleThreaded.Thread.config_store]
    exact hdx
  obtain ⟨q, he⟩ := SEnvTyping.sstep_callout_typed SI.wf (valEnv_throwsBelow Ii _) hI.run hdx'
  exact ⟨k, args, q, ⟨E, a, hdx⟩, he, rfl⟩

end Inv

/-- **A nested call is a component import call related to its round** (`impRel_link` for any
importer `b`). -/
theorem impRel_linkG {b : SimpleI} {Ii : SInst} {q : Ii.E.Op} {k : Nat} {nm : String}
    {p : FuncTy} (hk : b.imports[k]? = some (nm, p)) (hek : q.1.val = k)
    {args : List Silmaril.Wasm.Execution.Core.Val} (hea : q.2.1 = args) {ys : List Flat}
    (hm : args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys) {ws us : List IVal}
    (hws : liftArgs p.params ys = some ws) (hus : ValTy.checkList p.results us = true)
    (wv : Ii.E.Ar q)
    (hwv : Silmaril.Wasm.Game.Answer.toResult wv =
      .values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)) :
    Silmaril.Wasm.Component.Reference.ImpRel b Ii ⟨q, wv⟩
      [⟨(⟨q.1.val, hek ▸ (List.getElem?_eq_some_iff.mp hk).1⟩, .vals ws), some (.vals us)⟩] := by
  have hk' : b.imports[q.1.val]? = some (nm, p) := hek ▸ hk
  have hup : (some (Payload.vals us)).bind (Silmaril.Wasm.Component.Adapter.lower p).up =
      some (.flat (lowerArgs p.results us)) := by
    simp only [Option.bind_some, Silmaril.Wasm.Component.Adapter.up,
      Silmaril.Wasm.Component.checkLower, hus, ite_true, Option.map_some]
  refine ⟨nm, p, _, hk', payloadAnswer_flat hwv, ?_⟩
  show match liftArgs p.params (q.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
    | none => _ | some ws => _
  rw [hea, filterMap_of_mapM hm, hws]
  exact ⟨_, some (.vals us), rfl, hup.symm⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv

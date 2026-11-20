module

public import Silmaril.Wasm.Component.Reference.LinkedGDiv.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Rounds
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv.Round

/-!
# Diverging rounds through an abstract exporter, forward

The forward half of `LinkedSessionDiv.{Round, Call}` for `LinkedG` with an exporter given by
reference data `d` (R1, R2, R6, and R7 forward for source (ii)), from the importer's core
activation (`coreCfg M th K segs rest y`, `LInvG` relating it to the importer's part and the
exporter's state, the importer's frame `FrameG`):

* `roundsPre_fwdB`: the prefix variant of `rounds_fwdB`: a path of the importer's instance from
  `.running f` along `callMoves rs` to `.running f s t`, its import calls answered by the
  exporter (`ExpRun`), is a machine run without host events back to the importer's core
  activation (non-empty when `rs` is), `LInvG` holding at the exporter's end state; unless an
  import call was answered by a trap (or its arguments did not lift), in which case the part is
  `Doomed` at `(s, t)`;
* `divB_coreG` (**(i) the importer diverges host-free**): `link_inf` through `LInvG`;
* `divA_coreG` (**(ii) the exporter's served call diverges**): the importer's run to the callout
  (`LInvG.reach_fwd`, `LInvG.callout_fwd`), the nested `canon lower`/`canon lift` into the
  exporter (`nest_atX`), and R7 forward at the exporter's activation;
* `chatter_coreG` (**(iii) chatter**): each served import call is a non-empty machine run back to
  the importer's core activation (`roundsPre_fwdB` on one call); `diverges_of_segs`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

section Round

variable {lg : LinkedG} {Ii : SInst} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {f : Ii.F.Op} {d : lg.exp.RefData P} {pl : d.Pl}
  {ii : Nat}

/-- **A prefix of a round against the exporter is a machine run** back to the importer's core
activation, or the importer's part is doomed. -/
theorem roundsPre_fwdB (SI : ImpStatG P lg.imp Ii u₀ F₀ g tr) (W : WireG lg d pl tr ii)
    (hFr : d.Frame) (hFw : d.Fwd) (hB : d.Bounded) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) :
    ∀ (rs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Σ _ : (sigN lg.imp.imports.length).Op, Option Payload)))
      (M : Machine.Config (E3 P) σ) (s s₁ : lg.exp.St) (F : CoreFoot) (y : CoreSt (E3 P))
      (x : Store Nat × STh) (sB : Store Nat) (tB : STh),
      LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M.ref F y x → FrameG d pl ii th M.store →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii) rs dss →
      LinkedG.ExpRun P lg s dss.flatten s₁ →
      Ii.Path P (.running f x.1 x.2) (callMoves rs) (.running f sB tB) →
      (∃ (trc : List (Label (E3 P) σ)) (C' : List (Option (Activation (E3 P) σ)))
          (S'' : RefStore (E3 P)) (F' : CoreFoot) (yc : CoreSt (E3 P)),
        Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) trc
          (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest yc) ∧
        (∀ ev, Label.host ev ∉ trc) ∧ (rs = [] ∨ trc ≠ []) ∧
        LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s₁ S'' F' yc (sB, tB) ∧ FrameG d pl ii th S''.toCStore) ∨
      Doomed sB tB
  | [], dss, M, s, s₁, F, y, x, sB, tB, hI, hFG, hrel, hexp, hpath => by
    cases hrel
    cases hexp
    cases hpath
    refine .inl ⟨[], M.conts, M.ref, F, y, .refl _, ?_, Or.inl rfl, hI, hFG⟩
    intro ev h
    cases h
  | ⟨eq, v⟩ :: rs, dss₀, M, s, s₁, F, y, x, sB, tB, hI, hFG, hrel, hexp, hpath => by
    obtain ⟨ds, dss, hd, hrel', rfl⟩ : ∃ ds dss,
        Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii ⟨eq, v⟩ ds ∧
        List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii) rs dss ∧
        dss₀ = ds :: dss := by
      cases hrel with
      | cons h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩
    obtain ⟨s', t', k, args, run, co, op, hpath'⟩ := path_round_inv (rest := callMoves rs)
      (by simpa [callMoves] using hpath)
    -- after a trapped import call the thread is doomed
    have hdoom : v = .trap → Doomed sB tB := by
      intro hv
      subst hv
      cases rs with
      | nil =>
        cases hpath'
        exact doomed_resume co
      | cons r rs =>
        obtain ⟨e', v'⟩ := r
        exact (doomed_no_ask (doomed_resume co) hpath').elim
    obtain ⟨y₁, hy₁, hI₁⟩ := LInvG.reach_fwd SI hFr hI run
    let M₁ : Machine.Config (E3 P) σ := { M with core := y₁.1 }
    have hFG₁ : FrameG d pl ii th M₁.store := hFG
    obtain ⟨tr₀, htr₀, r₀⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
      (dispatch := DI P impl) (B := M) (th := th) (K := K) (segs := segs) (rest := rest) hy₁
    have r₀' : Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) tr₀
        (coreCfg M₁ th K segs rest y₁) := r₀
    obtain ⟨nm, p, ys, E, a, hk, hdx, hys, hst, hyty⟩ := hI₁.callout_fwd SI co op
    obtain ⟨wi, xe, hwire, hxe, hty, htr⟩ := W.site k nm p hk
    have hek := ifaceOp?_some op
    obtain ⟨nm', ft, A, hk', hA, hm⟩ := hd
    have hA' : payloadAnswer (Ii.imports.get eq.1) A = v := hA
    have hft : ft = p := by
      rw [hek.1, hk] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq] at hk'
      exact hk'.2.symm
    subst hft
    have hfilt : eq.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
      hek.2 ▸ filterMap_of_mapM hys
    have hmi : (nm, ft) ∈ lg.imp.imports := List.mem_of_getElem? hk
    obtain ⟨hmaxp, hmaxr, hres⟩ := W.arity.2 _ hmi
    obtain ⟨hpf, hrf⟩ := W.floats.2 _ hmi
    rw [hfilt] at hm
    split at hm
    · -- the arguments do not lift
      obtain ⟨rfl, rfl⟩ := hm
      exact .inr (hdoom hA.symm)
    · next ws hws =>
      obtain ⟨hkl, R, rfl, hAR⟩ := hm
      have hexp' : LinkedG.ExpRun P lg s
          (⟨(⟨eq.1.val, hkl⟩, .vals ws), R⟩ :: dss.flatten) s₁ := by
        simpa only [List.flatten_cons, List.singleton_append] using hexp
      cases hexp' with
      | @step _ s₂ _ _ _ _ _ w₂ hwire' hstep hrest =>
        have hw₂ : w₂.val = wi := by
          rw [hek.1, hwire] at hwire'
          exact (Option.some.inj hwire').symm
        rw [hw₂] at hstep
        rcases call_stepB (prof := prof) (impl := impl) SI hFr hFw hB hI₁ th hFG₁ co op hk hxe
            hty htr K segs rest hpf hmaxp hres hrf hmaxr hys hws hstep with
          ⟨us, rfl, hck, trc, C', S'', F', hrun, hnh, -, hI₂, hFG₂, -, hne⟩ | ⟨rfl, -⟩
        · have hv : Silmaril.Wasm.Game.Answer.toResult v =
              .values ((lowerArgs ft.results us).map Silmaril.Wasm.SingleThreaded.ofFlat) := by
            rw [← hA', hAR]
            have hup : (some (Payload.vals us)).bind (Silmaril.Wasm.Component.Adapter.lower ft).up =
                some (.flat (lowerArgs ft.results us)) := by
              simp only [Option.bind_some, Silmaril.Wasm.Component.Adapter.up,
                Silmaril.Wasm.Component.checkLower, hck, ite_true, Option.map_some]
            rw [hup, payloadAnswer_flat (w := .values ⟨_, SI.resAnswer hk hek.1 hck⟩) rfl]
            rfl
          rw [hv] at hpath'
          rcases roundsPre_fwdB SI W hFr hFw hB th K segs rest rs dss
              { M₁ with conts := C', store := S''.toCStore, core := S''.core } s₂ s₁ F' _ _ sB tB hI₂ hFG₂ hrel' hrest
              hpath' with
            ⟨trc', C'', S''', F'', yc, hrun', hnh', -, hIc, hFG'⟩ | hdm
          · refine .inl ⟨tr₀ ++ (trc ++ trc'), C'', S''', F'', yc,
              Adequacy.steps_append r₀' (Adequacy.steps_append hrun hrun'), ?_, .inr ?_, hIc,
              hFG'⟩
            · intro ev hm
              rcases List.mem_append.mp hm with hm | hm
              · exact (Quiet.of_core htr₀).1 ev hm
              · rcases List.mem_append.mp hm with hm | hm
                · exact hnh ev hm
                · exact hnh' ev hm
            · intro h
              exact hne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).2).1
          · exact .inr hdm
        · exact .inr (hdoom (by rw [← hA', hAR]; rfl))

/-! ## The three sources at the importer's core activation -/

/-- **(i) The importer diverges host-free**: the machine diverges in its core activation. -/
theorem divB_coreG (SI : ImpStatG P lg.imp Ii u₀ F₀ g tr) {s : lg.exp.St}
    {S : RefStore (E3 P)} {F : CoreFoot} {y : CoreSt (E3 P)} {sB : Store Nat} {tB : STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s S F y (sB, tB)) (hd : Linked2.DivB P sB tB)
    (M : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) :
    Machine.Diverges prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) := by
  obtain ⟨gr, hg0, hg⟩ := hd
  obtain ⟨ρc, Oc, hL, -⟩ := hI.rel
  exact SessionDiv.coreCfg_diverges_of
    (link_inf g tr hg (SI.hostsSat hI.funcs) (hg0 ▸ hL))

/-- **(ii) The exporter's served call diverges**: the machine diverges in the nested activation
of the exporter's export (R7 forward). -/
theorem divA_coreG (SI : ImpStatG P lg.imp Ii u₀ F₀ g tr) (W : WireG lg d pl tr ii)
    (hFr : d.Frame) (hDv : d.Div) {s : lg.exp.St} {M : Machine.Config (E3 P) σ}
    {F : CoreFoot} {y : CoreSt (E3 P)} {sB : Store Nat} {tB : STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M.ref F y (sB, tB)) (th : Option ThreadId)
    (hFG : FrameG d pl ii th M.store) (hd : LinkedG.DivA P lg Ii f sB tB s)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) :
    Machine.Diverges prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) := by
  obtain ⟨e, s', t', nm, ft, ws, w, hpath, himp, hlift, hwire, hdiv⟩ := hd
  obtain ⟨k, args, x₁, run, co, op⟩ : ∃ (k : Nat) (args : List Silmaril.Wasm.Execution.Core.Val)
      (x₁ : Store Nat × STh), Silmaril.Wasm.Game.Reach P (sB, tB) x₁ ∧
        Silmaril.Wasm.Game.CalloutAt x₁.1 x₁.2 k args ∧ Ii.importOp? k args = some e := by
    cases hpath with
    | cons h₁ _ =>
      cases h₁ with
      | ucall run co op => exact ⟨_, _, _, run, co, op⟩
  obtain ⟨y₁, hy₁, hI₁⟩ := LInvG.reach_fwd SI hFr hI run
  let M₁ : Machine.Config (E3 P) σ := { M with core := y₁.1 }
  have hFG₁ : FrameG d pl ii th M₁.store := hFG
  obtain ⟨tr₀, htr₀, r₀⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
    (dispatch := DI P impl) (B := M) (th := th) (K := K) (segs := segs) (rest := rest) hy₁
  have r₀' : Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) tr₀
      (coreCfg M₁ th K segs rest y₁) := r₀
  obtain ⟨nm', p, ys, E, a, hk, hdx, hys, hst, hyty⟩ := hI₁.callout_fwd SI co op
  obtain ⟨wi, xe, hwire', hxe, hty, htr⟩ := W.site k nm' p hk
  have hek := ifaceOp?_some op
  have hft : ft = p := by
    rw [hek.1, hk] at himp
    simp only [Option.some.injEq, Prod.mk.injEq] at himp
    exact himp.2.symm
  subst hft
  have hfilt : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
    hek.2 ▸ filterMap_of_mapM hys
  rw [hfilt] at hlift
  have hw₂ : w.val = wi := by
    rw [hek.1, hwire'] at hwire
    exact (Option.some.inj hwire).symm
  rw [hw₂] at hdiv
  have hmi : (nm', ft) ∈ lg.imp.imports := List.mem_of_getElem? hk
  obtain ⟨hmaxp, hmaxr, hres⟩ := W.arity.2 _ hmi
  obtain ⟨hpf, hrf⟩ := W.floats.2 _ hmi
  -- the nested `canon lower`/`canon lift` into the exporter (as in `call_stepB'`)
  have hentry : calloutEntry M₁.store th (tr k) = none := by
    rw [htr]
    exact hFG₁.entry _ _ _
  have hl : M₁.store.lockdown = false := hFG₁.lock
  obtain ⟨ιi, hi, hleave⟩ := hFG₁.imp
  obtain ⟨ιe, hie, hth⟩ := hFG₁.exp wi ⟨xe, hxe⟩
  rw [htr] at hst hentry
  obtain ⟨hf, -⟩ := hFr.lifted pl s M₁.ref F wi xe hI₁.hold hxe
  rw [hty] at hf
  let ie := d.inst pl wi
  let t : ThreadId := ⟨M₁.store.threads.length⟩
  have hadd : ιe.addThread? t = some (1, enterInst ιe t) := addThread?_ok hth t
  have hrem : (enterInst ιe t).removeThread? 1 =
      some (t, InstState.removeThread 1 (enterInst ιe t)) := removeThread?_enter ιe t
  obtain ⟨pos, M₂, K', segs', rest', tr₁, h₁, hc₁, hst₁, hcore₂, -, -, -, -, hinst₁, -, -⟩ :=
    nest_atX (prof := prof) (impl := impl) ie ii M₁ hl ιe (enterInst ιe t) th K segs rest y₁
      ⟨d.fid pl wi⟩ (d.addr pl wi) ft ys ιi ws hst hentry hi hleave hf hie hadd hrem hpf hyty hmaxp
      hlift hres hrf hmaxr
  have hS₁ : M₂.store = nstore M₁.store { inst := ⟨ii⟩, state := .started }
      (lowerRec ⟨M₁.store.subtasks.length⟩ ⟨ii⟩ ys ft pos)
      ((ntask₁G ie M₁.store ft).withState .started)
      ((thread₁ M₁.store.tasks).withIndex 1) (M₁.store.insts.set ie (enterInst ιe t)) :=
    hst₁.trans (nstoreCore_eqG _ _ _ _ _ _ _)
  have hH₁ : d.Hold pl s M₂.ref F :=
    hold_threads hFr hI₁.hold hie _ (hcore₂.trans hI₁.core.symm)
      (by show M₂.store.funcs = _; rw [hS₁]; rfl) (by show M₂.store.insts = _; rw [hS₁]; rfl)
  have hl₁ : M₂.store.lockdown = false := by rw [hS₁]; exact hl
  have htyped : ValTy.checkList xe.ty.params ws = true := by
    rw [hty]
    exact Silmaril.Wasm.Component.checkList_of_liftArgs hlift
  have hdM := (hDv pl s wi ws xe hxe htyped M₂.ref F hH₁ prof impl M₂ (some t) K' segs' rest'
    rfl hl₁ hinst₁).1 hdiv
  have hstart : d.startCfg pl wi xe ws M₂ (some t) K' segs' rest' = M₂ := by
    show { M₂ with ctl := _ } = M₂
    rw [hty, ← hc₁]
  rw [hstart] at hdM
  have hlive₂ : Live M₂ := ⟨by rw [hc₁]; exact List.cons_ne_nil _ _, hl₁⟩
  have hq₁ := Quiet.of_lrun h₁ hlive₂
  exact steps_diverges (Adequacy.steps_append r₀' h₁.steps)
    (fun ev hm => (List.mem_append.mp hm).elim ((Quiet.of_core htr₀).1 ev) (hq₁.1 ev)) hdM

/-- **(iii) Chatter**: infinitely many served import calls are a divergence of the machine. -/
theorem chatter_coreG (SI : ImpStatG P lg.imp Ii u₀ F₀ g tr) (W : WireG lg d pl tr ii)
    (hFr : d.Frame) (hFw : d.Fwd) (hB : d.Bounded) {s : lg.exp.St}
    {M : Machine.Config (E3 P) σ} {F : CoreFoot} {y : CoreSt (E3 P)} {sB : Store Nat}
    {tB : STh} (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M.ref F y (sB, tB))
    (th : Option ThreadId) (hFG : FrameG d pl ii th M.store)
    (hd : LinkedG.Chatter P lg Ii f sB tB s)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) :
    Machine.Diverges prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) := by
  obtain ⟨q, c, ds, st, hq0, hst0, hc⟩ := hd
  refine diverges_of_segs (fun m => ∃ (k : Nat) (M' : Machine.Config (E3 P) σ) (F' : CoreFoot)
      (y' : CoreSt (E3 P)) (x : Store Nat × STh),
      m = coreCfg M' th K segs rest y' ∧ q k = .running f x.1 x.2 ∧
      LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f (st k) M'.ref F' y' x ∧ FrameG d pl ii th M'.store) ?_
    ⟨0, M, F, y, (sB, tB), rfl, hq0, hst0 ▸ hI, hFG⟩
  rintro m ⟨k, M', F', y', x, rfl, hqk, hIk, hFGk⟩
  obtain ⟨hpath, hrel, hexp⟩ := hc k
  rw [hqk] at hpath
  -- the state after the call is running
  obtain ⟨s₁, t₁, hq₁⟩ : ∃ s₁ t₁, q (k + 1) = .running f s₁ t₁ := by
    generalize q (k + 1) = q' at hpath
    obtain ⟨e, v⟩ := c k
    obtain ⟨s', t', -, -, -, -, -, hp⟩ :=
      path_round_inv (rest := []) (by simpa [callMoves] using hpath)
    cases hp
    exact ⟨_, _, rfl⟩
  rw [hq₁] at hpath
  have hexp' : LinkedG.ExpRun P lg (st k) [ds k].flatten (st (k + 1)) := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hexp
  rcases roundsPre_fwdB (prof := prof) (impl := impl) SI W hFr hFw hB th K segs rest [c k]
      [ds k] M' (st k) (st (k + 1)) F' y' x s₁ t₁ hIk hFGk (.cons hrel .nil) hexp' hpath with
    ⟨trc, C', S'', F'', yc, hrun, hnh, hne, hIc, hFG'⟩ | hdm
  · have htr : trc ≠ [] := hne.resolve_left (List.cons_ne_nil _ _)
    exact ⟨trc, _, hrun, htr, hnh, k + 1,
      { M' with conts := C', store := S''.toCStore, core := S''.core }, F'', yc,
      (s₁, t₁), rfl, hq₁, hIc, hFG'⟩
  · have h₂ := (hc (k + 1)).1
    rw [hq₁] at h₂
    exact (doomed_no_call hdm h₂).elim

end Round

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv

module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Track
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv.Phase

/-!
# The importer's core activation read back, with its footprint tracked

`phase_backB` of `LinkedGInv` with `RelT` of `Track` along the round (`phase_backT`, `PhaseT`).
For R3 of a linked component (`RefData.BwdF`) the read-back must also give the run **up to** the
importer's exit from its core activation (R3's middle case splits the trace there), so `PhaseT`
records that prefix (`coreCfg_steps_inv''`: `coreCfg_steps_inv'` with the run of its core
prefix), and the footprint discipline at the exit (`RelT`) and at a trapped end (`TrapT`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv
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

/-- **`coreCfg_steps_inv'` with the run of its core prefix.** -/
theorem coreCfg_steps_inv'' {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
    {dispatch : Call E → Canon.P E σ (Ret E)} {B : Machine.Config E σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {x : CoreSt E} {tr : List (Label E σ)}
    {m' : Machine.Config E σ} (h : Steps prof hr dispatch (coreCfg B th K segs rest x) tr m') :
    (∃ y, Relation.ReflTransGen (CoreStep E) x y ∧ m' = coreCfg B th K segs rest y) ∨
      ∃ y pre l m₁ tr₂, Relation.ReflTransGen (CoreStep E) x y ∧
        Steps prof hr dispatch (coreCfg B th K segs rest x) pre (coreCfg B th K segs rest y) ∧
        tr = pre ++ l :: tr₂ ∧
        Step prof hr dispatch (coreCfg B th K segs rest y) l m₁ ∧
        CoreExit B th K segs rest y l m₁ ∧ Steps prof hr dispatch m₁ tr₂ m' := by
  generalize hm : coreCfg B th K segs rest x = m at h
  induction h generalizing x with
  | refl => exact .inl ⟨x, .refl, hm.symm⟩
  | cons s r ih =>
    subst hm
    rcases coreCfg_step_inv s with ⟨rfl, y, hy, rfl⟩ | hx
    · rcases ih rfl with ⟨z, hz, e⟩ | ⟨z, pre, l, m₁, tr₂, hz, rp, e, s', hx, r'⟩
      · exact .inl ⟨z, .head hy hz, e⟩
      · exact .inr ⟨z, .core :: pre, l, m₁, tr₂, .head hy hz, .cons s rp, by rw [e]; rfl, s',
          hx, r'⟩
    · exact .inr ⟨x, [], _, _, _, .refl, .refl _, rfl, s, hx, r⟩

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

section Reach

variable {b : SimpleI} {Ii : SInst} {u₀ s₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))}
  {g : CanonHost (E3 P) → Nat} {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {f : Ii.F.Op}
  {e : ExpSpec} {d : e.RefData P} {pl : d.Pl} {Fc : CoreFoot} {σ₀ : Store (CanonHost (E3 P))}

/-- **A core run of the shared thread read back, tracked**: `linvG_reach_back` keeping `RelT`. -/
theorem RelT.reach_back (SI : ImpStatG P b Ii u₀ F₀ g tr) (hFr : d.Frame) {s : e.St}
    {M : RefStore (E3 P)} {F : CoreFoot} {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M F y x) (hT : RelT s₀ g Oc₀ Fc σ₀ F y x)
    {y' : CoreSt (E3 P)} (hy : Relation.ReflTransGen (CoreStep (E3 P)) y y') :
    ∃ x', LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s { M with core := y'.1 } F y' x' ∧
      Silmaril.Wasm.Game.Reach P x x' ∧ RelT s₀ g Oc₀ Fc σ₀ F y' x' := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD, hW, hU⟩ := hT
  obtain ⟨ts, hs, ht⟩ := linvG_typed SI hI
  have hrun := reach_mapH g (coreSteps_internalP hy)
  obtain ⟨x', ρc', Oc', prun, hL', hgr, htc, -, -⟩ := reach_link_back hrun hL hs ht
  have hfy : y'.1.funcs = y.1.funcs := reach_funcs' (coreSteps_internalP hy)
  have hag : F.Agree (M.core : Store (CanonHost (E3 P))) y'.1 := by
    rw [hI.core]
    exact agree_of_touch hD htc hfy
  have hD' : FootDisj F ρc' Oc' y'.1 := hD.after_part hgr htc
  have hWi : (footUnion F (img ρc Oc)).Within y.1 y'.1 :=
    within_union_right (within_of_touchH g htc hfy)
  exact ⟨x', ⟨⟨ρc', Oc', hL', hgr.fn.trans hfn, hgr.gl.trans hgl, hD'⟩,
    hFr.agree pl s M _ F hI.hold hag (List.prefix_refl _) (fun _ _ => rfl), rfl,
    hfy.trans hI.funcs, hI.run.trans (reach_ssteps prun)⟩, prun,
    ρc', Oc', hL', hgr.fn.trans hfn, hgr.gl.trans hgl, hD', within_trans hW hU hWi,
    under_grows hU (grows_union (grows_refl F _) (grows_of_growH g hgr)) hW.structs_len
      hW.arrays_len⟩

end Reach

/-- **`PhaseB` with the run up to the importer's exit and the footprint tracked**: at the exit,
the trace splits at the exit step after a run `tr₁` from the start, and `RelT` holds there; at a
trapped end, `TrapT` holds at its core store. -/
def PhaseT (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ) {lg : LinkedG}
    (d : lg.exp.RefData P) (pl : d.Pl) (ii : Nat) (Ii : SInst) (s₀ u₀ : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat) (Oc₀ : Own)
    (Fc : CoreFoot) (σ₀ : Store (CanonHost (E3 P)))
    (f : Ii.F.Op) (M : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (y : CoreSt (E3 P)) (x : Store Nat × STh)
    (s : lg.exp.St) (trr : List (Label (E3 P) σ)) (E : Machine.Config (E3 P) σ) : Prop :=
  ∃ (rs : List (Σ q : Ii.E.Op, Ii.E.Ar q))
    (dss : List (List (Σ _ : (sigN lg.imp.imports.length).Op, Option Payload)))
    (s₁ : lg.exp.St) (x' : Store Nat × STh),
    List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii) rs dss ∧
    LinkedG.ExpRun P lg s dss.flatten s₁ ∧
    ((∃ (tr₁ tr₂ : List (Label (E3 P) σ)) (C' : List (Option (Activation (E3 P) σ)))
        (S'' : RefStore (E3 P)) (F' : CoreFoot) (yc : CoreSt (E3 P)) (l : Label (E3 P) σ)
        (m₁ : Machine.Config (E3 P) σ),
        trr = tr₁ ++ l :: tr₂ ∧
        Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) tr₁
          (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest yc) ∧
        (∀ h ys, (E3 P).status yc.1 yc.2 ≠ .callout h ys) ∧
        CoreExit { M with conts := C', store := S''.toCStore } th K segs rest yc l m₁ ∧
        Machine.Steps prof (fun _ _ => false) (DI P impl) m₁ tr₂ E ∧
        LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s₁ S'' F' yc x' ∧ RelT s₀ g Oc₀ Fc σ₀ F' yc x' ∧
        FrameG d pl ii th S'' ∧ CallExt d pl M.ref S'' ∧
        ∀ (mv : List (Move Ii.E Ii.F)) (q : Ii.HState),
          (∀ a t, Silmaril.Wasm.Game.Reach P (a, t) x' → Ii.Path P (.running f a t) mv q) →
          Ii.Path P (.running f x.1 x.2) (callMoves rs ++ mv) q) ∨
     (E.store.lockdown = true ∧ E.ctl = [] ∧
        TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ f M.store s₁ E.core x'.1 ∧
        TrapT d pl s₀ g Oc₀ Fc σ₀ M.store s₁ E.core x'.1 ∧
        Ii.Path P (.running f x.1 x.2) (callMoves rs ++ [.inr (.ans f .trap)]) (.idle x'.1)))

section Phase

variable {lg : LinkedG} {Ii : SInst} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {f : Ii.F.Op} {d : lg.exp.RefData P} {pl : d.Pl}
  {ii : Nat} {Fc : CoreFoot} {σ₀ : Store (CanonHost (E3 P))}

/-- **The importer's core activation, read back and tracked** (`PhaseT`). -/
theorem phase_backT (SI : ImpStatG P lg.imp Ii u₀ F₀ g tr) (W : WireG lg d pl tr ii)
    (hFr : d.Frame) (hBw : d.BwdF) (hB : d.Bounded) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) :
    ∀ (n : Nat) (M : Machine.Config (E3 P) σ) (s : lg.exp.St) (F : CoreFoot)
      (y : CoreSt (E3 P)) (x : Store Nat × STh) (trr : List (Label (E3 P) σ))
      (E : Machine.Config (E3 P) σ),
      trr.length ≤ n → LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M.ref F y x →
      RelT s₀ g Oc₀ Fc σ₀ F y x → FrameG d pl ii th M.store →
      Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) trr E →
      (∀ ev, Label.host ev ∉ trr) → ¬ Live E →
      (E.store.lockdown = true → E.ctl = [] → ∀ msg, Label.trap (.internal msg) ∉ trr) →
      PhaseT prof P impl d pl ii Ii s₀ u₀ F₀ g Oc₀ Fc σ₀ f M th K segs rest y x s trr E := by
  intro n
  induction n with
  | zero =>
    intro M s F y x trr E hn _ _ hFG r _ hE _
    have htr : trr = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst htr
    cases r
    exact absurd ⟨List.cons_ne_nil _ _, hFG.lock⟩ hE
  | succ n ih =>
    intro M s F y x trr E hn hI hT hFG r hh hE hni
    rcases coreCfg_steps_inv'' r with ⟨y', -, rfl⟩ |
      ⟨y', pre, l, m₁, tr₂, hy, rpre, rfl, st, hx, r₂⟩
    · exact absurd ⟨List.cons_ne_nil _ _, hFG.lock⟩ hE
    obtain ⟨x₁, hI₁, hr₁, hT₁⟩ := RelT.reach_back SI hFr hI hT hy
    let M' : Machine.Config (E3 P) σ := { M with core := y'.1 }
    have hFG₁ : FrameG d pl ii th M'.store := hFG
    have hh₂ : ∀ ev, Label.host ev ∉ l :: tr₂ :=
      fun ev hm => hh ev (List.mem_append_right _ hm)
    by_cases hco : ∃ h ys, (E3 P).status y'.1 y'.2 = .callout h ys
    swap
    · -- the importer exits its core activation
      refine ⟨[], [], s, x₁, .nil, .nil s, .inl ⟨pre, tr₂, M.conts, { M.store with core := y'.1 },
        F, y', l, m₁, rfl, rpre, fun h ys e => hco ⟨h, ys, e⟩, hx, r₂, hI₁, hT₁, hFG₁,
        callExt_refl _, ?_⟩⟩
      intro mv q hk
      exact hk x.1 x.2 hr₁
    obtain ⟨h, ys, hst⟩ := hco
    obtain ⟨k, args, q, co, op, rfl⟩ := linvG_callout_back SI hI₁ hst
    obtain ⟨nm, p, ys', E', a, hk, hdx, hys, hst', hyty⟩ := hI₁.callout_fwd SI co op
    have hyy : ys' = ys := by
      rw [hst] at hst'
      cases hst'
      rfl
    subst hyy
    obtain ⟨wi, xe, hwire, hxe, hty, htr⟩ := W.site k nm p hk
    have hek := ifaceOp?_some op
    have hmi : (nm, p) ∈ lg.imp.imports := List.mem_of_getElem? hk
    obtain ⟨hmaxp, hmaxr, hres⟩ := W.arity.2 _ hmi
    obtain ⟨hpf, hrf⟩ := W.floats.2 _ hmi
    have r' : Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M' th K segs rest y')
        (l :: tr₂) E := .cons st r₂
    have hk₂ : lg.imp.imports[q.1.val]? = some (nm, p) := hek.1 ▸ hk
    have hkl : q.1.val < lg.imp.imports.length := (List.getElem?_eq_some_iff.mp hk₂).1
    have hfilt : q.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys' :=
      hek.2 ▸ filterMap_of_mapM hys
    have hwl : wi < lg.exp.comp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
    have hpath_trap : Ii.Path P (.running f x.1 x.2)
        [.inl (.ask q), .inl (.ans q .trap), .inr (.ans f .trap)] (.idle x₁.1) :=
      path_trap_round hdx op x.1 x.2 hr₁
    cases hws : liftArgs p.params ys' with
    | none =>
      -- the arguments do not lift: a trap at the callout, no component import call
      obtain ⟨ιi, hi, hleave⟩ := hFG₁.imp
      obtain ⟨ιe, hie, hth⟩ := hFG₁.exp wi ⟨xe, hxe⟩
      obtain ⟨hf, -⟩ := hFr.lifted pl s M'.ref F wi xe hI₁.hold hxe
      rw [hty] at hf
      rw [htr] at hst'
      rcases nest_trap_args_backG (prof := prof) (impl := impl) (d.inst pl wi) ii M' hFG₁.lock ιe
          _ th K segs rest y' ⟨d.fid pl wi⟩ (d.addr pl wi) p ys' ιi hst' (hFG₁.entry _ _ _) hi
          hleave hf hie (addThread?_ok hth _) hpf hyty hmaxp hws r' with hl' |
        ⟨mT, rr, -, rfl, hcT, -⟩
      · exact absurd hl' hE
      have hds : Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii ⟨q, .trap⟩ [] := by
        refine ⟨nm, p, none, hk₂, rfl, ?_⟩
        show match liftArgs p.params (q.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
          | none => _ | some ws => _
        rw [hfilt, hws]
        exact ⟨rfl, rfl⟩
      refine ⟨[⟨q, .trap⟩], [[]], s, x₁, .cons hds .nil, .nil s,
        .inr ⟨rfl, rfl, ?_, ?_, hpath_trap⟩⟩
      · show TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ f M.store s mT.core x₁.1
        rw [hcT]
        exact trapAt_of_linv hI₁ rfl
      · show TrapT d pl s₀ g Oc₀ Fc σ₀ M.store s mT.core x₁.1
        rw [hcT]
        exact trapT_of_linv hI₁ hT₁ rfl
    | some ws =>
      have hn' : ∀ msg, E.store.lockdown = true → E.ctl = [] →
          Label.trap (.internal msg) ∉ l :: tr₂ :=
        fun msg hlk hct hm => hni hlk hct msg (List.mem_append_right _ hm)
      rcases call_backB' (prof := prof) (impl := impl) SI hFr hBw (M := M') hI₁ th hFG₁ co op hk
          hxe hty htr K segs rest hpf hmaxp hres hrf hmaxr hys hws r' hh₂ hE
          (fun hlk hct msg => hn' msg hlk hct) with
        ⟨us, s', trc, tr₃, C', S'', F', hstep, hck, etr, hne, rtrc, r₃, hH, hwi, hgr, hFG₂, hX⟩ |
        ⟨s', hstep, hlock, hctl, S', F', hc', hfS, hH, hwi, hgr⟩
      · -- a returning step: read back the rest of the round
        have hBH := hB pl _ S'' F' hH
        have hI₂ := LInvG.resume_fwd SI hI₁ hk hdx op hck hH hwi hgr hBH
        have hT₂ := RelT.resume (p := p) hI₁ hT₁ hdx us hwi hgr hBH
        have hlen : tr₃.length ≤ n := by
          have h₁ : (pre ++ l :: tr₂).length ≤ n + 1 := hn
          have h₂ : (l :: tr₂).length = trc.length + tr₃.length := by
            rw [etr, List.length_append]
          have h₃ : 0 < trc.length := List.length_pos_iff.mpr hne
          simp only [List.length_append, List.length_cons] at h₁ h₂
          omega
        have hh₃ : ∀ ev, Label.host ev ∉ tr₃ :=
          fun ev hm => hh₂ ev (etr ▸ List.mem_append_right _ hm)
        have hni₃ : E.store.lockdown = true → E.ctl = [] →
            ∀ msg, Label.trap (.internal msg) ∉ tr₃ :=
          fun hlk hct msg hm => hn' msg hlk hct (etr ▸ List.mem_append_right _ hm)
        obtain ⟨rs, dss, s₁, x', hrel, hexp, hend⟩ := ih { M' with conts := C', store := S''.toCStore, core := S''.core } s'
          F' _ _ tr₃ E hlen hI₂ hT₂ hFG₂ r₃ hh₃ hE hni₃
        have hrel₁ := impRel_linkG (b := lg.imp) (Ii := Ii) hk hek.1 hek.2 hys hws hck
          (.values ⟨_, SI.resAnswer hk hek.1 hck⟩) rfl
        have hw' : lg.wire[q.1.val]? = some wi := hek.1 ▸ hwire
        have hexp' : LinkedG.ExpRun P lg s
            ([⟨(⟨q.1.val, hkl⟩, .vals ws), some (.vals us)⟩] :: dss).flatten s₁ :=
          .step ⟨wi, hwl⟩ hw' hstep hexp
        have hX' : CallExt d pl M.ref S'' := callExt_trans (callExt_refl _) hX
        refine ⟨_ :: rs, _ :: dss, s₁, x', .cons hrel₁ hrel, hexp', ?_⟩
        rcases hend with ⟨tr₄, tr₅, C'', S''', F'', yc, l', m₂, etr₄, r₄, hnco, hx', r₅, hIc,
            hTc, hFGc, hXc, hpath⟩ | ⟨hlk, hct, hTA, hTT, hpath⟩
        · refine .inl ⟨pre ++ (trc ++ tr₄), tr₅, C'', S''', F'', yc, l', m₂, ?_,
            Adequacy.steps_append rpre (Adequacy.steps_append rtrc r₄), hnco, hx', r₅, hIc, hTc,
            hFGc, callExt_trans hX' hXc, ?_⟩
          · rw [etr, etr₄]
            simp only [List.append_assoc]
          · intro mv q' hk'
            exact .cons (.ucall hr₁ co op) (.cons (.uret _) (hpath mv q' hk'))
        · refine .inr ⟨hlk, hct, hTA.funcs_congr (callExt_funcs hX'),
            hTT.funcs_congr (callExt_funcs hX'), ?_⟩
          exact .cons (.ucall hr₁ co op) (.cons (.uret _) hpath)
      · -- a trapping step: the round answers a trap
        have hBH := hB pl _ S' F' hH
        have hds := LinkedSessionIR.impRel_trap hk₂ (hfilt ▸ hws)
        have hw' : lg.wire[q.1.val]? = some wi := hek.1 ▸ hwire
        have hwi' : F.Within (M'.core : Store (CanonHost (E3 P))) S'.core := hc' ▸ hwi
        have hTA := (trapAt_of_within hI₁ hH hfS hwi' hgr hBH).funcs_congr (S₁ := M.store) rfl
        have hTT := (trapT_of_within hI₁ hT₁ hH hfS hwi' hgr hBH).funcs_congr (S₁ := M.store) rfl
        rw [hc'] at hTA hTT
        exact ⟨[⟨q, .trap⟩], [[⟨(⟨q.1.val, hkl⟩, .vals ws), none⟩]], s', x₁, .cons hds .nil,
          .step ⟨wi, hwl⟩ hw' hstep (.nil s'), .inr ⟨hlock, hctl, hTA, hTT, hpath_trap⟩⟩

end Phase

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain

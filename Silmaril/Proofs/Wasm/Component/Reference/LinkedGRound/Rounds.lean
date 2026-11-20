module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Step

/-!
# The importer's core activation in a round against an abstract exporter

The machine counterpart of `rounds_fwd`/`lseg_run` of `LinkedSessionFwd` for an exporter given
by reference data `d` (R1, R2, R6): the importer's round (its instance path along `callMoves rs`
and the answer `w`, the component import calls `dss` related by `ImpRel` and answered by an
`ExpRun` of the exporter's specification) is followed by the machine from the importer's core
activation, iterating `call_stepB` along the importer's part (`LInvG.reach_fwd` between calls):

* `WireG lg d pl tr ii`: the importer's static wiring: each import `k` (of type `p`) is wired
  to an export `w` of the exporter of type `p` whose `canon lift` the trampoline `tr k` lowers
  (instance `ii`); the importer's arities and float-freedom (`SimpleI.Arity`, `FloatFree`);
* `RoundEndB`: the machine runs without host events or `internal` traps either to the
  importer's core activation at its result (`LInvG` at the exporter's state after the round,
  the importer's frame again, the store a `CallExt` of the round's), or to a trapped end whose
  parts are related at the trapped core store (`TrapAtG`), the round answering a trap;
* `rounds_fwdB`: the round ends as `RoundEndB`. Its trapped ends are a callout whose arguments
  do not lift (`nest_trap_argsG`) and an exporter step answering a trap (`call_stepB`: the
  exporter's trapped `Ends`, or results that do not lift). A trap of the importer's own core
  activation is left to the caller: the first case returns the importer's result `r`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
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

/-! ## Quiet traces up to non-`internal` traps -/

/-- The trace has no host event and no `internal` trap. -/
def NoHI (tr : List (Label (E3 P) σ)) : Prop :=
  (∀ ev, Label.host ev ∉ tr) ∧ ∀ msg, Label.trap (.internal msg) ∉ tr

theorem NoHI.append {tr₁ tr₂ : List (Label (E3 P) σ)} (h₁ : NoHI tr₁) (h₂ : NoHI tr₂) :
    NoHI (tr₁ ++ tr₂) :=
  ⟨fun ev hm => (List.mem_append.mp hm).elim (h₁.1 ev) (h₂.1 ev),
    fun msg hm => (List.mem_append.mp hm).elim (h₁.2 msg) (h₂.2 msg)⟩

theorem NoHI.of_core {tr : List (Label (E3 P) σ)} (h : ∀ l ∈ tr, l = .core) : NoHI tr :=
  ⟨(Quiet.of_core h).1, fun _ => (Quiet.of_core h).2 _⟩

theorem TrapEnd.stepsI {M M' : Machine.Config (E3 P) σ} {tr : List (Label (E3 P) σ)}
    {c : (E3 P).Store (CanonHost (E3 P))}
    (h : Machine.Steps prof (fun _ _ => false) (DI P impl) M tr M') (hq : NoHI tr)
    (h' : TrapEnd prof P impl M' c) : TrapEnd prof P impl M c := by
  obtain ⟨tr', m', r, hh, hi, hl, hc⟩ := h'
  exact ⟨tr ++ tr', m', Adequacy.steps_append h r, (hq.append ⟨hh, hi⟩).1,
    (hq.append ⟨hh, hi⟩).2, hl, hc⟩

/-! ## The importer's wiring -/

/-- **The importer's wiring to the exporter's data `d` at placement `pl`**: each import `k` of
type `p` is wired to an export `w` of type `p` whose lifted record the trampoline `tr k` lowers
from instance `ii`; the importer's arities and float-freedom. -/
structure WireG (lg : LinkedG) (d : lg.exp.RefData P) (pl : d.Pl) (tr : Nat → CanonHost (E3 P))
    (ii : Nat) : Prop where
  site : ∀ (k : Nat) (nm : String) (p : FuncTy), lg.imp.imports[k]? = some (nm, p) →
    ∃ (w : Nat) (xe : Export), lg.wire[k]? = some w ∧ lg.exp.comp.exports[w]? = some xe ∧
      xe.ty = p ∧ tr k = .lowered ⟨d.fid pl w⟩ (witFt p) {} ⟨ii⟩
  arity : lg.imp.Arity
  floats : lg.imp.FloatFree

theorem TrapAtG.funcs_congr {e : ExpSpec} {d : e.RefData P} {pl : d.Pl} {Ii : SInst}
    {s₀ u₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
    {Oc₀ : Own} {f : Ii.F.Op} {S₀ S₁ : CStore (E3 P)} {s : e.St}
    {c : (E3 P).Store (CanonHost (E3 P))} {u : Store Nat}
    (h : TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ f S₀ s c u) (hf : S₀.funcs = S₁.funcs) :
    TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ f S₁ s c u := by
  obtain ⟨⟨S', F', h₁, h₂, h₃, h₄⟩, h₅, h₆, h₇⟩ := h
  exact ⟨⟨S', F', h₁, h₂.trans hf, h₃, h₄⟩, h₅, h₆, h₇⟩

/-! ## The end of a round -/

/-- **How the importer's core activation ends in a round**, from `coreCfg M th K segs rest y`:
at its result (the importer's part at `(u₁, t')` with result `r` answering `w`, `LInvG` at the
exporter's state `s₁`, the frame again, the store a `CallExt` of `M.store`), or in a trapped
end with the parts related at the trapped core store, the round answering a trap. -/
def RoundEndB (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ) {e : ExpSpec}
    (d : e.RefData P) (pl : d.Pl) (ii : Nat) (Ii : SInst) (s₀ u₀ : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat) (Oc₀ : Own)
    (f : Ii.F.Op) (M : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (y : CoreSt (E3 P)) (s₁ : e.St) (u₁ : Store Nat)
    (w : Ii.F.Ar f) : Prop :=
  (∃ (trc : List (Label (E3 P) σ)) (C' : List (Option (Activation (E3 P) σ)))
      (S'' : RefStore (E3 P)) (F' : CoreFoot) (yc : CoreSt (E3 P)) (t' : STh)
      (r : Silmaril.Wasm.Execution.Core.Result),
    Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) trc
      (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest yc) ∧ NoHI trc ∧
    LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s₁ S'' F' yc (u₁, t') ∧
    Silmaril.Wasm.Game.ResultAt u₁ t' r ∧
    Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) r = some w ∧
    FrameG d pl ii th S'' ∧ CallExt d pl M.ref S'') ∨
  (∃ c, TrapEnd prof P impl (coreCfg M th K segs rest y) c ∧
    TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ f M.store s₁ c u₁ ∧
    Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) .trap = some w)

/-! ## A round -/

section Round

variable {lg : LinkedG} {Ii : SInst} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {f : Ii.F.Op} {d : lg.exp.RefData P} {pl : d.Pl}
  {ii : Nat}

/-- **A round of the importer against the exporter is a machine run** ending as `RoundEndB`. -/
theorem rounds_fwdB (SI : ImpStatG P lg.imp Ii u₀ F₀ g tr) (W : WireG lg d pl tr ii)
    (hFr : d.Frame) (hFw : d.Fwd) (hB : d.Bounded) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) {w : Ii.F.Ar f} :
    ∀ (rs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Σ _ : (sigN lg.imp.imports.length).Op, Option Payload)))
      (M : Machine.Config (E3 P) σ) (s s₁ : lg.exp.St) (F : CoreFoot) (y : CoreSt (E3 P))
      (x : Store Nat × STh) (u₁ : Store Nat),
      LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M.ref F y x → FrameG d pl ii th M.store →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii) rs dss →
      LinkedG.ExpRun P lg s dss.flatten s₁ →
      Ii.Path P (.running f x.1 x.2) (callMoves rs ++ [.inr (.ans f w)]) (.idle u₁) →
      RoundEndB prof P impl d pl ii Ii s₀ u₀ F₀ g Oc₀ f M th K segs rest y s₁ u₁ w
  | [], dss, M, s, s₁, F, y, x, u₁, hI, hFG, hrel, hexp, hpath => by
    cases hrel
    cases hexp
    obtain ⟨s', t', r, run, final, hw, hq⟩ := path_ret_inv (by simpa [callMoves] using hpath)
    cases hq
    obtain ⟨yc, hy, hIc⟩ := LInvG.reach_fwd SI hFr hI run
    obtain ⟨tr₀, htr₀, r₀⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
      (dispatch := DI P impl) (B := M) (th := th) (K := K) (segs := segs) (rest := rest) hy
    exact .inl ⟨tr₀, M.conts, { M.store with core := yc.1 }, F, yc, t', r, r₀,
      NoHI.of_core htr₀, hIc, final, hw, hFG.core _, callExt_refl _⟩
  | ⟨eq, v⟩ :: rs, dss₀, M, s, s₁, F, y, x, u₁, hI, hFG, hrel, hexp, hpath => by
    obtain ⟨ds, dss, hd, hrel', rfl⟩ : ∃ ds dss,
        Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii ⟨eq, v⟩ ds ∧
        List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii) rs dss ∧
        dss₀ = ds :: dss := by
      cases hrel with
      | cons h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩
    obtain ⟨s', t', k, args, run, co, op, hpath'⟩ := path_round_inv (rest := callMoves rs ++
      [.inr (.ans f w)]) (by simpa [callMoves] using hpath)
    obtain ⟨y₁, hy₁, hI₁⟩ := LInvG.reach_fwd SI hFr hI run
    let M₁ : Machine.Config (E3 P) σ := { M with core := y₁.1 }
    have hFG₁ : FrameG d pl ii th M₁.store := hFG
    obtain ⟨tr₀, htr₀, r₀⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
      (dispatch := DI P impl) (B := M) (th := th) (K := K) (segs := segs) (rest := rest) hy₁
    have r₀' : Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) tr₀
        (coreCfg M₁ th K segs rest y₁) := r₀
    have hX₁ : CallExt d pl M.ref M₁.ref := callExt_refl _
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
      next hws =>
      obtain ⟨rfl, rfl⟩ := hm
      have hv : v = .trap := hA.symm
      subst hv
      obtain ⟨rfl, rfl, hw'⟩ := path_doomed co hpath'
      cases hrel'
      cases hexp
      obtain ⟨ιi, hi, hleave⟩ := hFG₁.imp
      obtain ⟨ιe, hie, hth⟩ := hFG₁.exp wi ⟨xe, hxe⟩
      obtain ⟨hf, -⟩ := hFr.lifted pl s M₁.ref F wi xe hI₁.hold hxe
      rw [hty] at hf
      rw [htr] at hst
      have hT := (nest_trap_argsG (prof := prof) (impl := impl) (d.inst pl wi) ii M₁ hFG₁.lock ιe
        _ th K segs rest y₁ ⟨d.fid pl wi⟩ (d.addr pl wi) ft ys ιi hst (hFG₁.entry _ _ _) hi
        hleave hf hie (addThread?_ok hth _) hpf hyty hmaxp hws).toS.trapEnd
      exact .inr ⟨y₁.1, TrapEnd.steps r₀' (Quiet.of_core htr₀) hT, trapAt_of_linv hI₁ rfl, hw'⟩
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
          ⟨us, rfl, hck, trc, C', S'', F', hrun, hnh, hni, hI₂, hFG₂, hX, -⟩ | ⟨rfl, c, hT, hTA⟩
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
          have hX₂ : CallExt d pl M.ref S'' := callExt_trans hX₁ hX
          rcases rounds_fwdB SI W hFr hFw hB th K segs rest rs dss
              { M₁ with conts := C', store := S''.toCStore, core := S''.core } s₂ s₁ F' _ _ u₁ hI₂ hFG₂ hrel' hrest
              hpath' with
            ⟨trc', C'', S''', F'', yc, t'', r, hrun', hq', hIc, final, hw'', hFG', hX'⟩ |
            ⟨c, hT, hTA, hw''⟩
          · exact .inl ⟨tr₀ ++ (trc ++ trc'), C'', S''', F'', yc, t'', r,
              Adequacy.steps_append r₀' (Adequacy.steps_append hrun hrun'),
              (NoHI.of_core htr₀).append ((show NoHI trc from ⟨hnh, hni⟩).append hq'), hIc,
              final, hw'', hFG', callExt_trans hX₂ hX'⟩
          · exact .inr ⟨c, TrapEnd.stepsI (Adequacy.steps_append r₀' hrun)
              ((NoHI.of_core htr₀).append ⟨hnh, hni⟩) hT, hTA.funcs_congr (callExt_funcs hX₂),
              hw''⟩
        · have hv : v = .trap := by
            rw [← hA', hAR]
            rfl
          subst hv
          obtain ⟨rfl, rfl, hw'⟩ := path_doomed co hpath'
          cases hrel'
          cases hrest
          exact .inr ⟨c, TrapEnd.steps r₀' (Quiet.of_core htr₀) hT, hTA.funcs_congr rfl, hw'⟩

end Round

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound

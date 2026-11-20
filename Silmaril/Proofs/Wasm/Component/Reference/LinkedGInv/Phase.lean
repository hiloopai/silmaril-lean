module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv.Step

/-!
# The importer's core activation in a round, read back

`lsegs_inv`/`lseg_path` of `Linked2` against `LInvG` and an abstract exporter: every host-free
run of the importer's core activation to a configuration that is not live is a round of the
importer's instance whose component import calls are an `ExpRun` of the exporter
(`phase_backB`, `PhaseB`):

* the importer's core runs are runs of its part (`linvG_reach_back`);
* at a callout, the part is stopped at a typed import question of import `k`, the trampoline
  `tr k` (`linvG_callout_back`), wired to an export `w` of the exporter (`WireG`); arguments that
  do not lift trap at the callout's core store (`nest_trap_args_backG`), with no component import
  call; otherwise the call is read back by `call_backB`: a returning step of the exporter resumes
  the importer, from where the run is read back again (on a shorter trace); a trapped step ends
  the round with a trap;
* the round ends at the importer's exit from its core activation (`CoreExit`, not a callout),
  with `LInvG`, the frame and `CallExt` there, or locked down with an empty control chain where
  the parts are related at its core store (`TrapAtG`) and the round answers a trap.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
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

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-- **How a host-free run of the importer's core activation ends at a configuration `E` that is
not live**, from `coreCfg M th K segs rest y` with the importer's part at `x` and the exporter's
state `s`: a round of rounds `rs`, related by `ImpRel` to component import calls `dss` answered by
an `ExpRun` of the exporter from `s` to `s₁`, the part at `x'` at its end; and either the
importer's exit from its core activation (`CoreExit`, not a callout, the rest of the run from the
exit host-free) with `LInvG`, the frame and `CallExt` there and the round a prefix of the
instance's play, or `E` locked down with an empty control chain, the parts related at its core
store and the round a play answering a trap. -/
def PhaseB (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ) {lg : LinkedG}
    (d : lg.exp.RefData P) (pl : d.Pl) (ii : Nat) (Ii : SInst) (s₀ u₀ : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat) (Oc₀ : Own)
    (f : Ii.F.Op) (M : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (x : Store Nat × STh) (s : lg.exp.St)
    (E : Machine.Config (E3 P) σ) : Prop :=
  ∃ (rs : List (Σ q : Ii.E.Op, Ii.E.Ar q))
    (dss : List (List (Σ _ : (sigN lg.imp.imports.length).Op, Option Payload)))
    (s₁ : lg.exp.St) (x' : Store Nat × STh),
    List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii) rs dss ∧
    LinkedG.ExpRun P lg s dss.flatten s₁ ∧
    ((∃ (tr₂ : List (Label (E3 P) σ)) (C' : List (Option (Activation (E3 P) σ)))
        (S'' : RefStore (E3 P)) (F' : CoreFoot) (yc : CoreSt (E3 P)) (l : Label (E3 P) σ)
        (m₁ : Machine.Config (E3 P) σ),
        (∀ ev, Label.host ev ∉ tr₂) ∧ (∀ h ys, (E3 P).status yc.1 yc.2 ≠ .callout h ys) ∧
        CoreExit { M with conts := C', store := S''.toCStore } th K segs rest yc l m₁ ∧
        Machine.Steps prof (fun _ _ => false) (DI P impl) m₁ tr₂ E ∧
        LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s₁ S'' F' yc x' ∧ FrameG d pl ii th S'' ∧
        CallExt d pl M.ref S'' ∧
        ∀ (mv : List (Move Ii.E Ii.F)) (q : Ii.HState),
          (∀ a t, Silmaril.Wasm.Game.Reach P (a, t) x' → Ii.Path P (.running f a t) mv q) →
          Ii.Path P (.running f x.1 x.2) (callMoves rs ++ mv) q) ∨
     (E.store.lockdown = true ∧ E.ctl = [] ∧
        TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ f M.store s₁ E.core x'.1 ∧
        Ii.Path P (.running f x.1 x.2) (callMoves rs ++ [.inr (.ans f .trap)]) (.idle x'.1)))

section Phase

variable {lg : LinkedG} {Ii : SInst} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {f : Ii.F.Op} {d : lg.exp.RefData P} {pl : d.Pl}
  {ii : Nat}

/-- **The importer's core activation, read back** (`PhaseB`). -/
theorem phase_backB (SI : ImpStatG P lg.imp Ii u₀ F₀ g tr) (W : WireG lg d pl tr ii)
    (hFr : d.Frame) (hBw : d.BwdF) (hB : d.Bounded) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) :
    ∀ (n : Nat) (M : Machine.Config (E3 P) σ) (s : lg.exp.St) (F : CoreFoot)
      (y : CoreSt (E3 P)) (x : Store Nat × STh) (trr : List (Label (E3 P) σ))
      (E : Machine.Config (E3 P) σ),
      trr.length ≤ n → LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M.ref F y x →
      FrameG d pl ii th M.store →
      Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) trr E →
      (∀ ev, Label.host ev ∉ trr) → ¬ Live E →
      (E.store.lockdown = true → E.ctl = [] → ∀ msg, Label.trap (.internal msg) ∉ trr) →
      PhaseB prof P impl d pl ii Ii s₀ u₀ F₀ g Oc₀ f M th K segs rest x s E := by
  intro n
  induction n with
  | zero =>
    intro M s F y x trr E hn _ hFG r _ hE _
    have htr : trr = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst htr
    cases r
    exact absurd ⟨List.cons_ne_nil _ _, hFG.lock⟩ hE
  | succ n ih =>
    intro M s F y x trr E hn hI hFG r hh hE hni
    rcases coreCfg_steps_inv' r with ⟨y', -, rfl⟩ | ⟨y', pre, l, m₁, tr₂, hy, rfl, st, hx, r₂⟩
    · exact absurd ⟨List.cons_ne_nil _ _, hFG.lock⟩ hE
    obtain ⟨x₁, hI₁, hr₁⟩ := linvG_reach_back SI hFr hI hy
    let M' : Machine.Config (E3 P) σ := { M with core := y'.1 }
    have hFG₁ : FrameG d pl ii th M'.store := hFG
    have hh₂ : ∀ ev, Label.host ev ∉ l :: tr₂ :=
      fun ev hm => hh ev (List.mem_append_right _ hm)
    by_cases hco : ∃ h ys, (E3 P).status y'.1 y'.2 = .callout h ys
    swap
    · -- the importer exits its core activation
      refine ⟨[], [], s, x₁, .nil, .nil s, .inl ⟨tr₂, M.conts, { M.store with core := y'.1 },
        F, y', l, m₁, fun ev hm => hh₂ ev (List.mem_cons_of_mem _ hm),
        fun h ys e => hco ⟨h, ys, e⟩, hx, r₂, hI₁, hFG₁, callExt_refl _, ?_⟩⟩
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
      refine ⟨[⟨q, .trap⟩], [[]], s, x₁, .cons hds .nil, .nil s, .inr ⟨rfl, rfl, ?_, hpath_trap⟩⟩
      show TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ f M.store s mT.core x₁.1
      rw [hcT]
      exact trapAt_of_linv hI₁ rfl
    | some ws =>
      have hn' : ∀ msg, E.store.lockdown = true → E.ctl = [] →
          Label.trap (.internal msg) ∉ l :: tr₂ :=
        fun msg hlk hct hm => hni hlk hct msg (List.mem_append_right _ hm)
      rcases call_backB (prof := prof) (impl := impl) SI hFr hBw hB (M := M') hI₁ th hFG₁ co op hk
          hxe hty htr K segs rest hpf hmaxp hres hrf hmaxr hys hws r' hh₂ hE
          (fun hlk hct msg => hn' msg hlk hct) with
        ⟨us, s', trc, tr₃, C', S'', F', hstep, hck, etr, hne, r₃, hI₂, hFG₂, hX⟩ |
        ⟨s', hstep, hlock, hctl, hTA⟩
      · -- a returning step: read back the rest of the round
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
          F' _ _ tr₃ E hlen hI₂ hFG₂ r₃ hh₃ hE hni₃
        have hrel₁ := impRel_linkG (b := lg.imp) (Ii := Ii) hk hek.1 hek.2 hys hws hck
          (.values ⟨_, SI.resAnswer hk hek.1 hck⟩) rfl
        have hw' : lg.wire[q.1.val]? = some wi := hek.1 ▸ hwire
        have hexp' : LinkedG.ExpRun P lg s
            ([⟨(⟨q.1.val, hkl⟩, .vals ws), some (.vals us)⟩] :: dss).flatten s₁ :=
          .step ⟨wi, hwl⟩ hw' hstep hexp
        have hX' : CallExt d pl M.ref S'' := callExt_trans (callExt_refl _) hX
        refine ⟨_ :: rs, _ :: dss, s₁, x', .cons hrel₁ hrel, hexp', ?_⟩
        rcases hend with ⟨tr₄, C'', S''', F'', yc, l', m₂, hh₄, hnco, hx', r₄, hIc, hFGc, hXc,
            hpath⟩ | ⟨hlk, hct, hTA, hpath⟩
        · refine .inl ⟨tr₄, C'', S''', F'', yc, l', m₂, hh₄, hnco, hx', r₄, hIc, hFGc,
            callExt_trans hX' hXc, ?_⟩
          intro mv q' hk'
          exact .cons (.ucall hr₁ co op) (.cons (.uret _) (hpath mv q' hk'))
        · refine .inr ⟨hlk, hct, hTA.funcs_congr (callExt_funcs hX'), ?_⟩
          exact .cons (.ucall hr₁ co op) (.cons (.uret _) hpath)
      · -- a trapping step: the round answers a trap
        have hds := LinkedSessionIR.impRel_trap hk₂ (hfilt ▸ hws)
        have hw' : lg.wire[q.1.val]? = some wi := hek.1 ▸ hwire
        refine ⟨[⟨q, .trap⟩], [[⟨(⟨q.1.val, hkl⟩, .vals ws), none⟩]], s', x₁, .cons hds .nil,
          .step ⟨wi, hwl⟩ hw' hstep (.nil s'), .inr ⟨hlock, hctl, hTA.funcs_congr rfl,
            hpath_trap⟩⟩

end Phase

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv

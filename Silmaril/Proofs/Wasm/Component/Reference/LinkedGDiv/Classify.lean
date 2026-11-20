module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.Back
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedG.Main
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Back

/-!
# Classifying a divergence of the importer's core activation

From the importer's core activation of a linked call, the machine diverging there and `LInvG`
relating it to the importer's part and the exporter's state (`DInvG`):

* `ldiv_roundG`: one round: (i) the importer's part runs host-free forever (`Linked2.DivB`,
  `link_inf_back`); (ii) the importer calls out and the served call diverges (`LinkedG.DivA`,
  `call_divB`); (iv) the importer's activation exits otherwise and the machine diverges after the
  exit (`ExitDivG`); or (iii) one served import call, back to `DInvG` by a host-free run. A
  callout whose arguments do not lift traps (`nest_trap_argsG`) and does not diverge;
* `ldiv_classifyG`: by classical case analysis on whether a finite chain of served calls reaches
  a state of (i), (ii) or (iv), and otherwise by dependent choice (`seq_of_step`), a divergence
  is a finite chain of served calls followed by (i), (ii), (iv) or chatter
  (`LinkedG.Chatter`).

At a linked call between calls, (iv) does not diverge (`Call`): the importer's results are
lifted and the call resolves, or it traps.
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
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain
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

variable {P : Profile} {σ : Type}

theorem noHost_nil : ∀ ev, Label.host ev ∉ ([] : List (Label (E3 P) σ)) :=
  fun _ h => nomatch h

/-- A state of a diverging linked call inside the importer's core activation: the continuation
slots `C` and the store `S` of the frame (the rest of the configuration is the call's start), the
exporter's footprint `F`, the shared thread `y`, the importer's part `x` and the exporter's
state `s`. -/
structure DStG (P : Profile) (σ : Type) (e : ExpSpec) where
  C : List (Option (Activation (E3 P) σ))
  S : RefStore (E3 P)
  F : CoreFoot
  y : CoreSt (E3 P)
  x : Store Nat × STh
  s : e.St

variable (prof : ProfileKind) (impl : HostImpl (E3 P) σ) {lg : LinkedG}
  (d : lg.exp.RefData P) (pl : d.Pl) (ii : Nat) (Ii : SInst) (s₀ u₀ : Store Nat)
  (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat) (Oc₀ : Own)
  (f : Ii.F.Op) (th : Option ThreadId) (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
  (segs : List (Seg (E3 P) σ)) (rest : List (Activation (E3 P) σ))
  (M₀ : Machine.Config (E3 P) σ) (Fc : CoreFoot) (σ₀ : Store (CanonHost (E3 P)))

/-- **The invariant of a diverging linked call**: the machine diverges from the importer's core
activation at `z`, `LInvG` and the importer's frame hold, and the store extends `M₀`'s by the
calls so far; the footprint is tracked (`RelT`: changes since `σ₀` inside `Fc`). -/
structure DInvG (z : DStG P σ lg.exp) : Prop where
  div : Machine.Diverges prof (fun _ _ => false) (DI P impl)
    (coreCfg { M₀ with conts := z.C, store := z.S.toCStore, core := z.S.core } th K segs rest z.y)
  inv : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f z.s z.S z.F z.y z.x
  frame : FrameG d pl ii th z.S.toCStore
  ext : CallExt d pl M₀.ref z.S
  track : RelT s₀ g Oc₀ Fc σ₀ z.F z.y z.x

/-- **(iv) The importer's core activation exits otherwise and the machine diverges after the
exit**: its core run to `y₁` (its part's run to `x₁`), a status that is not a callout, the exit
step to `m₁`, from which the machine diverges. -/
def ExitDivG (z : DStG P σ lg.exp) : Prop :=
  ∃ (y₁ : CoreSt (E3 P)) (x₁ : Store Nat × STh) (lb : Label (E3 P) σ)
    (m₁ : Machine.Config (E3 P) σ),
    Relation.ReflTransGen (CoreStep (E3 P)) z.y y₁ ∧ Silmaril.Wasm.Game.Reach P z.x x₁ ∧
    LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f z.s { z.S with core := y₁.1 } z.F y₁ x₁ ∧
    RelT s₀ g Oc₀ Fc σ₀ z.F y₁ x₁ ∧
    (∀ h ys, (E3 P).status y₁.1 y₁.2 ≠ .callout h ys) ∧
    CoreExit { M₀ with conts := z.C, store := z.S.toCStore, core := z.S.core } th K segs rest y₁ lb m₁ ∧
    Machine.Diverges prof (fun _ _ => false) (DI P impl) m₁

variable {prof impl d pl ii Ii s₀ u₀ F₀ g Oc₀ f th K segs rest M₀ Fc σ₀}
  {tr : Nat → CanonHost (E3 P)}

/-- **One round of a diverging linked call**: (i), (ii), (iv), or a served import call back to
the invariant. -/
theorem ldiv_roundG (SI : ImpStatG P lg.imp Ii u₀ F₀ g tr) (W : WireG lg d pl tr ii)
    (hFr : d.Frame) (hDv : d.Div) (hB : d.Bounded) {z : DStG P σ lg.exp}
    (hz : DInvG prof impl d pl ii Ii s₀ u₀ F₀ g Oc₀ f th K segs rest M₀ Fc σ₀ z) :
    Linked2.DivB P z.x.1 z.x.2 ∨ LinkedG.DivA P lg Ii f z.x.1 z.x.2 z.s ∨
      ExitDivG prof impl d pl Ii s₀ u₀ F₀ g Oc₀ f th K segs rest M₀ Fc σ₀ z ∨
      ∃ (c : Σ e : Ii.E.Op, Ii.E.Ar e)
        (ds : List (Σ _ : (sigN lg.imp.imports.length).Op, Option Payload))
        (z' : DStG P σ lg.exp) (trc : List (Label (E3 P) σ)),
        Ii.Path P (.running f z.x.1 z.x.2) (callMoves [c]) (.running f z'.x.1 z'.x.2) ∧
        Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii c ds ∧
        LinkedG.ExpRun P lg z.s ds z'.s ∧
        DInvG prof impl d pl ii Ii s₀ u₀ F₀ g Oc₀ f th K segs rest M₀ Fc σ₀ z' ∧
        Machine.Steps prof (fun _ _ => false) (DI P impl)
          (coreCfg { M₀ with conts := z.C, store := z.S.toCStore, core := z.S.core } th K segs rest z.y) trc
          (coreCfg { M₀ with conts := z'.C, store := z'.S.toCStore, core := z'.S.core } th K segs rest z'.y) ∧
        (∀ ev, Label.host ev ∉ trc) := by
  rcases z with ⟨C, S, F, y, x, s⟩
  obtain ⟨hd, hI, hFG, hX, hT⟩ := hz
  dsimp only at hd hI hFG hX hT ⊢
  let M : Machine.Config (E3 P) σ := { M₀ with conts := C, store := S.toCStore, core := S.core }
  change Machine.Diverges prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) at hd
  change LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M.ref F y x at hI
  change FrameG d pl ii th M.store at hFG
  rcases coreCfg_diverges_step hd with hinf | ⟨y₁, lb, m₁, hy, hx, dy₁, d₁⟩
  · -- (i) the importer's core activation runs forever
    left
    obtain ⟨ρc, Oc, hL, -⟩ := hI.rel
    obtain ⟨ts, hs, ht⟩ := linvG_typed SI hI
    exact link_inf_back g hinf hL hs ht
  obtain ⟨x₁, hI₁, hr₁, hT₁⟩ := RelT.reach_back SI hFr hI hT hy
  by_cases hco : ∃ h ys, (E3 P).status y₁.1 y₁.2 = .callout h ys
  swap
  · -- (iv) an exit that is not a callout
    exact .inr (.inr (.inl ⟨y₁, x₁, lb, m₁, hy, hr₁, hI₁, hT₁, fun h ys e => hco ⟨h, ys, e⟩, hx,
      d₁⟩))
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
  have hk₂ : lg.imp.imports[q.1.val]? = some (nm, p) := hek.1 ▸ hk
  have hkl : q.1.val < lg.imp.imports.length := (List.getElem?_eq_some_iff.mp hk₂).1
  have hfilt : q.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys' :=
    hek.2 ▸ filterMap_of_mapM hys
  have hwl : wi < lg.exp.comp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
  let M' : Machine.Config (E3 P) σ := { M with core := y₁.1 }
  have hFG₁ : FrameG d pl ii th M'.store := hFG
  have dy₁' : Machine.Diverges prof (fun _ _ => false) (DI P impl)
      (coreCfg M' th K segs rest y₁) := dy₁
  cases hws : liftArgs p.params ys' with
  | none =>
    -- the arguments do not lift: a trap at the callout, which does not diverge
    obtain ⟨ιi, hi, hleave⟩ := hFG₁.imp
    obtain ⟨ιe, hie, hth⟩ := hFG₁.exp wi ⟨xe, hxe⟩
    obtain ⟨hf, -⟩ := hFr.lifted pl s M'.ref F wi xe hI₁.hold hxe
    rw [hty] at hf
    rw [htr] at hst'
    exact absurd dy₁' (TrapsFrom.not_diverges (trapsFrom_of_SH (nest_trap_argsG (prof := prof)
      (impl := impl) (d.inst pl wi) ii M' hFG₁.lock ιe _ th K segs rest y₁ ⟨d.fid pl wi⟩
      (d.addr pl wi) p ys' ιi hst' (hFG₁.entry _ _ _) hi hleave hf hie (addThread?_ok hth _) hpf
      hyty hmaxp hws)))
  | some ws =>
    rcases call_divB (prof := prof) (impl := impl) SI hFr hDv hB (M := M') hI₁ th hFG₁ co op hk
        hxe hty htr K segs rest hpf hmaxp hres hrf hmaxr hys hws dy₁' with
      hD | ⟨us, s', trc, C', S'', F', hstep, hck, hrun, hnh, dres, hH₂, hwi₂, hgr₂, hI₂, hFG₂, hX₂⟩
    · -- (ii) the served call diverges
      right; left
      refine ⟨q, x₁.1, x₁.2, nm, p, ws, ⟨wi, hwl⟩, .cons (.ucall hr₁ co op) (.nil _), hk₂, ?_,
        hek.1 ▸ hwire, hD⟩
      rw [hfilt]
      exact hws
    · -- (iii) one served import call
      right; right; right
      obtain ⟨tr₀, htr₀, r₀⟩ := Adequacy.coreCfg_steps_of (prof := prof)
        (hr := fun _ _ => false) (dispatch := DI P impl) (B := M) (th := th) (K := K)
        (segs := segs) (rest := rest) hy
      have r₀' : Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y)
          tr₀ (coreCfg M' th K segs rest y₁) := r₀
      have hrel₁ := impRel_linkG (b := lg.imp) (Ii := Ii) hk hek.1 hek.2 hys hws hck
        (.values ⟨_, SI.resAnswer hk hek.1 hck⟩) rfl
      have hw' : lg.wire[q.1.val]? = some wi := hek.1 ▸ hwire
      refine ⟨⟨q, .values ⟨_, SI.resAnswer hk hek.1 hck⟩⟩, _,
        ⟨C', S'', F',
          (S''.core, (E3 P).resume S''.core y₁.2 (.values (lowerArgs p.results us))),
          (x₁.1, Silmaril.Wasm.SingleThreaded.resumeResult x₁.1 x₁.2
            (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))), s'⟩,
        tr₀ ++ trc, .cons (.ucall hr₁ co op) (.cons (.uret _) (.nil _)), hrel₁,
        .step ⟨wi, hwl⟩ hw' hstep (.nil s'),
        ⟨dres, hI₂, hFG₂, callExt_trans hX (callExt_trans (callExt_refl _) hX₂),
          RelT.resume (p := p) hI₁ hT₁ hdx us hwi₂ hgr₂ (hB pl _ S'' F' hH₂)⟩,
        Adequacy.steps_append r₀' hrun, ?_⟩
      intro ev hm
      rcases List.mem_append.mp hm with hm | hm
      · exact (Quiet.of_core htr₀).1 ev hm
      · exact hnh ev hm

/-- **A divergence from the importer's core activation** is a finite chain of served import
calls, reached by a host-free run, followed by (i), (ii), (iv) or chatter. -/
theorem ldiv_classifyG (SI : ImpStatG P lg.imp Ii u₀ F₀ g tr) (W : WireG lg d pl tr ii)
    (hFr : d.Frame) (hDv : d.Div) (hB : d.Bounded) {z₀ : DStG P σ lg.exp}
    (hz₀ : DInvG prof impl d pl ii Ii s₀ u₀ F₀ g Oc₀ f th K segs rest M₀ Fc σ₀ z₀) :
    ∃ (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Σ _ : (sigN lg.imp.imports.length).Op, Option Payload)))
      (z : DStG P σ lg.exp) (trc : List (Label (E3 P) σ)),
      Ii.Path P (.running f z₀.x.1 z₀.x.2) (callMoves cs) (.running f z.x.1 z.x.2) ∧
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii) cs dss ∧
      LinkedG.ExpRun P lg z₀.s dss.flatten z.s ∧
      DInvG prof impl d pl ii Ii s₀ u₀ F₀ g Oc₀ f th K segs rest M₀ Fc σ₀ z ∧
      Machine.Steps prof (fun _ _ => false) (DI P impl)
        (coreCfg { M₀ with conts := z₀.C, store := z₀.S } th K segs rest z₀.y) trc
        (coreCfg { M₀ with conts := z.C, store := z.S.toCStore, core := z.S.core } th K segs rest z.y) ∧
      (∀ ev, Label.host ev ∉ trc) ∧
      (Linked2.DivB P z.x.1 z.x.2 ∨ LinkedG.DivA P lg Ii f z.x.1 z.x.2 z.s ∨
        LinkedG.Chatter P lg Ii f z.x.1 z.x.2 z.s ∨
        ExitDivG prof impl d pl Ii s₀ u₀ F₀ g Oc₀ f th K segs rest M₀ Fc σ₀ z) := by
  classical
  let Pre : DStG P σ lg.exp → Prop := fun z => ∃ (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
    (dss : List (List (Σ _ : (sigN lg.imp.imports.length).Op, Option Payload)))
    (trc : List (Label (E3 P) σ)),
    Ii.Path P (.running f z₀.x.1 z₀.x.2) (callMoves cs) (.running f z.x.1 z.x.2) ∧
    List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii) cs dss ∧
    LinkedG.ExpRun P lg z₀.s dss.flatten z.s ∧
    Machine.Steps prof (fun _ _ => false) (DI P impl)
      (coreCfg { M₀ with conts := z₀.C, store := z₀.S } th K segs rest z₀.y) trc
      (coreCfg { M₀ with conts := z.C, store := z.S.toCStore, core := z.S.core } th K segs rest z.y) ∧
    (∀ ev, Label.host ev ∉ trc)
  by_cases hfin : ∃ z, Pre z ∧ DInvG prof impl d pl ii Ii s₀ u₀ F₀ g Oc₀ f th K segs rest M₀ Fc σ₀ z ∧
      (Linked2.DivB P z.x.1 z.x.2 ∨ LinkedG.DivA P lg Ii f z.x.1 z.x.2 z.s ∨
        ExitDivG prof impl d pl Ii s₀ u₀ F₀ g Oc₀ f th K segs rest M₀ Fc σ₀ z)
  · obtain ⟨z, ⟨cs, dss, trc, h₁, h₂, h₃, h₄, h₅⟩, hz, hd⟩ := hfin
    refine ⟨cs, dss, z, trc, h₁, h₂, h₃, hz, h₄, h₅, ?_⟩
    rcases hd with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr h))
  · let T : DStG P σ lg.exp → (Σ e : Ii.E.Op, Ii.E.Ar e) ×
        List (Σ _ : (sigN lg.imp.imports.length).Op, Option Payload) → DStG P σ lg.exp → Prop :=
      fun z gg z' => Ii.Path P (.running f z.x.1 z.x.2) (callMoves [gg.1])
          (.running f z'.x.1 z'.x.2) ∧
        Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii gg.1 gg.2 ∧
        LinkedG.ExpRun P lg z.s gg.2 z'.s
    have step : ∀ z, (Pre z ∧ DInvG prof impl d pl ii Ii s₀ u₀ F₀ g Oc₀ f th K segs rest M₀ Fc σ₀ z) →
        ∃ gg z', T z gg z' ∧
          (Pre z' ∧ DInvG prof impl d pl ii Ii s₀ u₀ F₀ g Oc₀ f th K segs rest M₀ Fc σ₀ z') := by
      rintro z ⟨⟨cs, dss, trc, h₁, h₂, h₃, h₄, h₅⟩, hz⟩
      rcases ldiv_roundG SI W hFr hDv hB hz with h | h | h | ⟨c, ds, z', trc', hp, hr, he, hz', hrun, hnh⟩
      · exact absurd ⟨z, ⟨cs, dss, trc, h₁, h₂, h₃, h₄, h₅⟩, hz, .inl h⟩ hfin
      · exact absurd ⟨z, ⟨cs, dss, trc, h₁, h₂, h₃, h₄, h₅⟩, hz, .inr (.inl h)⟩ hfin
      · exact absurd ⟨z, ⟨cs, dss, trc, h₁, h₂, h₃, h₄, h₅⟩, hz, .inr (.inr h)⟩ hfin
      refine ⟨(c, ds), z', ⟨hp, hr, he⟩, ⟨cs ++ [c], dss ++ [ds], trc ++ trc', ?_,
        List.rel_append h₂ (.cons hr .nil), ?_, Adequacy.steps_append h₄ hrun, ?_⟩, hz'⟩
      · rw [callMoves_append]
        exact path_append h₁ hp
      · rw [List.flatten_append, List.flatten_singleton]
        exact Silmaril.Proofs.Wasm.Component.Reference.LinkedG.expRunG_append h₃ he
      · intro ev hm
        rcases List.mem_append.mp hm with hm | hm
        · exact h₅ ev hm
        · exact hnh ev hm
    obtain ⟨sq, gs, h0, hs⟩ := seq_of_step _ T step
      (⟨⟨[], [], [], .nil _, .nil, .nil _, .refl _, (noHost_nil (P := P) (σ := σ))⟩, hz₀⟩ :
        Pre z₀ ∧ _)
    refine ⟨[], [], z₀, [], .nil _, .nil, .nil _, hz₀, .refl _, (noHost_nil (P := P) (σ := σ)),
      .inr (.inr (.inl ?_))⟩
    refine ⟨fun n => .running f (sq n).x.1 (sq n).x.2, fun n => (gs n).1, fun n => (gs n).2,
      fun n => (sq n).s, by simp only [h0], by simp only [h0], fun n => hs n⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv

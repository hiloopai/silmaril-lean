module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkSeg
public import Silmaril.Proofs.Wasm.Component.Reference.LinkSegs

/-!
# The ends of a linked call as plays of the importer

From `LInv` at the importer's export call (the part at the pending invocation of the export
question `f` from its store `u₀`, the exporter at its store `π₀`), the core ends of `lsegs_inv`
(`LEnd`) are IR plays of the importer's instance (`LPlay`): the export question, the rounds of
the nested calls related by `ImpRel` to component import calls answered by the exporter from
`π₀` (`Linked2.ExpRun`), and the answer.

* `lplay_values`: a returned activation, the answer of the part's values (`sanswer_of_run` on
  `LInv.run`, `values_back`);
* `lplay_trap`: a trapped activation, a trap answer (`trap_back`, `throwing_back`);
* `lplay_fail`: a callout whose arguments do not lift (an import call with no component call,
  `ImpRel` with `[]`), or whose nested call traps or returns results that do not lift (the
  component call answered `none`, `ExpRun.trap` with `Outcome.traps ∈ specAt` from `exp_run`):
  the trap round and a trap answer.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Rel4)

variable {P : Profile} {σ : Type}

/-- **The IR play of a linked call, importer side**: from the importer's store `u₀`, the export
question `f`, rounds related by `ImpRel` to component import calls answered by the exporter from
its store `π₀`, and the answer `w`. -/
def LPlay (P : Profile) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (u₀ π₀ : Store Nat) (f : Ii.F.Op) (w : Ii.F.Ar f) : Prop :=
  ∃ (rounds : List (Round Ii.E)) (q : Ii.HState)
    (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))),
    Ii.Path P (.idle u₀) (.inr (.ask f) :: callMoves rounds ++ [.inr (.ans f w)]) q ∧
    List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rounds dss ∧ Linked2.ExpRun P l Ie π₀ dss.flatten

section Ends

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ π₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ} {Op₀ Oc₀ : Own}
  {f : Ii.F.Op} {y₀ : CoreSt (E3 P)}

/-- **A segmented run to a result is a play**: when the part's thread at every point satisfying
`LInv` at the end `y` is at a result `r` with `Φ r`, the run is a play answering `r`. -/
theorem lplay_result (S : LStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y₀ (u₀, Ii.initThread f) π₀)
    {recs : List (LRec P)} {y : CoreSt (E3 P)} (hseg : LSeg B y₀ recs y)
    {Φ : Silmaril.Wasm.Execution.Core.Result → Prop}
    (hres : ∀ x π, LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π →
      ∃ r, Silmaril.Wasm.Game.ResultAt x.1 x.2 r ∧ Φ r) :
    ∃ (w : Ii.F.Ar f) (r : Silmaril.Wasm.Execution.Core.Result), LPlay P l Ie Ii u₀ π₀ f w ∧
      Φ r ∧ Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) r = some w := by
  obtain ⟨⟨zs, zt⟩, π', rounds, dss, hIz, hrel, hexp, hpath⟩ := lseg_path S hseg hI
  obtain ⟨r, hr, hΦ⟩ := hres _ _ hIz
  obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run S.impWf
    (valEnv_throwsBelow Ii _) hIz.run hr
  have hp := hpath [.inr (.ans f w)] (.idle zs) (fun _ _ hr' => .cons (.oret hr' hr hw) (.nil _))
  have hrun := hexp.run (.nil π')
  rw [List.append_nil] at hrun
  exact ⟨w, r, ⟨rounds, _, dss, .cons (.call u₀ f) hp, hrel, hrun⟩, hΦ, hw⟩

/-- **A returned activation is a play** answering the part's values, whose flat view is the
shared thread's. -/
theorem lplay_values (S : LStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y₀ (u₀, Ii.initThread f) π₀)
    {recs : List (LRec P)} {y : CoreSt (E3 P)} (hseg : LSeg B y₀ recs y) {zs : List Flat}
    (hst : (E3 P).status y.1 y.2 = .returned (.values zs)) :
    ∃ (w : Ii.F.Ar f) (cvs : List Silmaril.Wasm.Execution.Core.Val),
      LPlay P l Ie Ii u₀ π₀ f w ∧ cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs ∧
      Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) (.values cvs) = some w := by
  obtain ⟨cvs, hcode, hm⟩ := status_values hst
  have hres : ∀ x π, LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π → ∃ r,
      Silmaril.Wasm.Game.ResultAt x.1 x.2 r ∧ r = .values cvs := by
    intro x π hIx
    obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hIx.rel
    obtain ⟨ts, hs, ht⟩ := hIx.typed S
    have hc : (y.2.config (Store.mapH (gL P l) y.1)).code = Silmaril.Wasm.Execution.Core.vals cvs :=
      (config_code_mapH (gL P l) y.1 y.2).trans hcode
    obtain ⟨vs, hv, hvm⟩ := values_back P hL hs ht hc
    have hm' : (vs.map (linkMap s₀ ρc).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs := by
      rw [hvm]
      exact hm
    have hid := map_val_of_mapM _ hm'
    have hvs : vs = cvs := hid.symm.trans hvm
    exact ⟨.values cvs, hvs ▸ hv, rfl⟩
  obtain ⟨w, r, hP, rfl, hw⟩ := lplay_result S hI hseg hres
  exact ⟨w, cvs, hP, hm, hw⟩

/-- **A trapped activation is a play** answering a trap: its lifted answer is `none`. -/
theorem lplay_trap (S : LStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y₀ (u₀, Ii.initThread f) π₀)
    {recs : List (LRec P)} {y : CoreSt (E3 P)} (hseg : LSeg B y₀ recs y)
    (hst : (E3 P).status y.1 y.2 = .returned .trap) :
    ∃ w : Ii.F.Ar f, LPlay P l Ie Ii u₀ π₀ f w ∧ ∀ x : SimpleExport,
      (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift x.ty)) = none := by
  have hres : ∀ x π, LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π → ∃ r,
      Silmaril.Wasm.Game.ResultAt x.1 x.2 r ∧ r = .trap := by
    intro x π hIx
    obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hIx.rel
    obtain ⟨ts, hs, ht⟩ := hIx.typed S
    rcases status_trap hst with hc | ⟨a, hc⟩
    · exact ⟨.trap, trap_back P hL hs ht ((config_code_mapH (gL P l) y.1 y.2).trans hc), rfl⟩
    · exact (throwing_back P hL hs ht ((config_code_mapH (gL P l) y.1 y.2).trans hc)).elim
  obtain ⟨w, r, hP, rfl, hw⟩ := lplay_result S hI hseg hres
  exact ⟨w, hP, fun _ => lifted_trap (fun _ h => by cases h) hw⟩

/-- **A failing nested call is a component import call answered by a trap**: arguments that do
not lift make no component call (`ImpRel` with `[]`); otherwise the exporter's run from the
shared store traps or returns results that do not lift, a trap of its specification at its
current store (`ExpRun.trap`). -/
theorem expRun_fail (S : LStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)}
    {x : Store Nat × Silmaril.Wasm.SingleThreaded.Thread} {π : Store Nat}
    (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π) {e : Ii.E.Op} {k w : Nat} {nm : String}
    {xe : SimpleExport} (hk : l.imp.imports[k]? = some (nm, xe.ty)) (hek : e.1.val = k)
    (hw : l.wire[k]? = some w) (hxe : l.exp.exports[w]? = some xe) {ys : List Flat}
    (hys : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys)
    (hfail : liftArgs xe.ty.params ys = none ∨
      ∃ ws ev, liftArgs xe.ty.params ys = some ws ∧
        Relation.ReflTransGen (CoreStep (E3 P))
          (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
            (lowerArgs xe.ty.params ws)) ev ∧
        ((E3 P).status ev.1 ev.2 = .returned .trap ∨
          ∃ zs, (E3 P).status ev.1 ev.2 = .returned (.values zs) ∧
            liftArgs xe.ty.results zs = none)) :
    ∃ ds, Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii ⟨e, .trap⟩ ds ∧ Linked2.ExpRun P l Ie π ds := by
  have hk' : l.imp.imports[e.1.val]? = some (nm, xe.ty) := hek ▸ hk
  have hkl : e.1.val < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hk').1
  rcases hfail with hl | ⟨ws, ev, hws, hrun, hend⟩
  · refine ⟨[], ⟨nm, xe.ty, none, hk', rfl, ?_⟩, .nil π⟩
    show match liftArgs xe.ty.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
      | none => _ | some ws => _
    rw [hys, hl]
    exact ⟨rfl, rfl⟩
  have hmem : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
  have typed : ValTy.checkList xe.ty.params ws = true :=
    Silmaril.Wasm.Component.checkList_of_liftArgs hws
  obtain ⟨ρp, Op, ρc, Oc, -, hR⟩ := hI.rel
  obtain ⟨π₂, ρp₂, Op₂, -, -, -, hval, htr⟩ := exp_run (vs := ws) S.expInst
    (S.expGood.core xe hmem) typed hI.wf (gL P l) hR hI.fnE (S.owned xe hmem) hrun
  have hspec : Outcome.traps ∈ specAt P l.exp Ie xe ws π := by
    unfold specAt
    rw [checkLower_of_check typed]
    rcases hend with htrap | ⟨zs, hzs, hus⟩
    · exact Or.inl ⟨none, htr htrap, rfl⟩
    · exact Or.inl ⟨some zs, (hval zs hzs).2.1, by simp only [liftOutcome, hus]⟩
  have hwl : w < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
  have hxw : l.exp.exports[(⟨w, hwl⟩ : Fin l.exp.exports.length)] = xe :=
    (List.getElem?_eq_some_iff.mp hxe).2
  refine ⟨[⟨(⟨e.1.val, hkl⟩, .vals ws), none⟩], ⟨nm, xe.ty, none, hk', rfl, ?_⟩,
    .trap (k := ⟨e.1.val, hkl⟩) ⟨w, hwl⟩ (hek ▸ hw) (hxw ▸ hspec)⟩
  show match liftArgs xe.ty.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
    | none => _ | some ws => _
  rw [hys, hws]
  exact ⟨hkl, none, rfl, rfl⟩

/-- The part stopped at a callout, answered by a trap, answers the export question with a
trap. -/
theorem path_trap_round {e : Ii.E.Op} {zs : Store Nat} {zt : Silmaril.Wasm.SingleThreaded.Thread}
    {E : Silmaril.Wasm.SingleThreaded.Ctx} {a k : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hd : Silmaril.Wasm.SingleThreaded.decompose? zs (zt.config zs).code = some (E, a, k, args))
    (he : Ii.importOp? k args = some e) :
    ∀ s t, Silmaril.Wasm.Game.Reach P (s, t) (zs, zt) →
      Ii.Path P (.running f s t) [.inl (.ask e), .inl (.ans e .trap), .inr (.ans f .trap)]
        (.idle zs) := by
  intro s t hr
  have hres : Silmaril.Wasm.SingleThreaded.resumeResult zs zt
      (Silmaril.Wasm.Game.Answer.toResult (ft := Ii.imports.get e.1) .trap) =
      .active (zt.config zs).frame (E.fill [.trap]) := by
    simp only [Silmaril.Wasm.SingleThreaded.resumeResult, hd, Silmaril.Wasm.Game.Answer.toResult,
      Silmaril.Wasm.Execution.Core.Result.toAdmin]
  refine .cons (.ucall hr ⟨E, a, hd⟩ he) (.cons (.uret _) ?_)
  rw [hres]
  have hfin : Silmaril.Wasm.Game.ResultAt zs (.active (zt.config zs).frame [.trap]) .trap := rfl
  exact .cons (.oret (fill_trap_reach' (P := P) zs E (zt.config zs).frame) hfin rfl) (.nil _)

/-- **A failing callout at the end of a segmented run is a play** answering a trap: the rounds
of the nested calls, the trap round of the callout, and the trap. -/
theorem lplay_fail (S : LStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y₀ (u₀, Ii.initThread f) π₀)
    {recs : List (LRec P)} {y : CoreSt (E3 P)} (hseg : LSeg B y₀ recs y) {fid : FuncId}
    {a : (E3 P).FuncAddr} {p : FuncTy} {ys : List Flat}
    (hst : (E3 P).status y.1 y.2 = .callout (.lowered fid (witFt p) {} ⟨2⟩) ys)
    (hf : ArenaField.funcs.get? B.store fid = some (.lifted a (witFt p) {} ⟨1⟩))
    (hp : p.results.length ≤ 1)
    (hfail : liftArgs p.params ys = none ∨
      ∃ ws ev, liftArgs p.params ys = some ws ∧
        Relation.ReflTransGen (CoreStep (E3 P))
          (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs p.params ws)) ev ∧
        ((E3 P).status ev.1 ev.2 = .returned .trap ∨
          ∃ zs, (E3 P).status ev.1 ev.2 = .returned (.values zs) ∧
            liftArgs p.results zs = none)) :
    LPlay P l Ie Ii u₀ π₀ f .trap := by
  obtain ⟨⟨zs, zt⟩, π', rounds, dss, hIz, hrel, hexp, hpath⟩ := lseg_path S hseg hI
  obtain ⟨k, nm, p', w, xe, E, a', args, e, heq, hk, hw, hxe, hpx, hdx, hm, he', -⟩ :=
    hIz.callout S hst
  have hfk : fid = l.wireFid k ∧ witFt p = witFt p' := by
    have h' := heq
    simp only [CanonHost.lowered.injEq] at h'
    exact ⟨h'.1, h'.2.1⟩
  have hmi : (nm, p') ∈ l.imp.imports := List.mem_of_getElem? hk
  have hpp : p = xe.ty := (witFt_inj hfk.2 hp (S.arity.2 _ hmi).2.2).trans hpx.symm
  have hfl : ArenaField.funcs.get? B.store fid =
      some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
    hfk.1 ▸ S.lifted k w xe hw hxe
  have ha : a = Ie.addrs.getD xe.core 0 := by
    injection Option.some.inj (hf.symm.trans hfl)
  subst hpp ha
  have hek : e.1.val = k ∧ e.2.1 = args := ifaceOp?_some he'
  have hys : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
    hek.2 ▸ filterMap_of_mapM hm
  obtain ⟨ds, hds, hrun⟩ := expRun_fail S hIz (hpx ▸ hk) hek.1 hw hxe hys hfail
  have hP := hpath _ _ (path_trap_round hdx he')
  have hmoves : (.inr (.ask f) :: callMoves (rounds ++ [⟨e, .trap⟩]) ++ [.inr (.ans f .trap)] :
      List (Silmaril.Games.Move Ii.E Ii.F)) = .inr (.ask f) :: (callMoves rounds ++
        [.inl (.ask e), .inl (.ans e .trap), .inr (.ans f .trap)]) := by
    rw [callMoves_append, List.cons_append, List.append_assoc]
    rfl
  have hP' : Ii.Path P (.idle u₀) (.inr (.ask f) :: callMoves (rounds ++ [⟨e, .trap⟩]) ++
      [.inr (.ans f .trap)]) (.idle zs) := by
    rw [hmoves]
    exact .cons (.call u₀ f) hP
  refine ⟨rounds ++ [⟨e, .trap⟩], _, dss ++ [ds], hP',
    List.rel_append hrel (.cons hds .nil), ?_⟩
  rw [List.flatten_append, List.flatten_singleton]
  exact hexp.run hrun

end Ends

/-! ## The start -/

section Start

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {f : Ii.F.Op}


/-- Renaming host code commutes with relocation. -/
theorem mapH_reloc {H H' : Type} (g : H → H') (s₀ t : Store H) :
    Store.mapH g (reloc s₀ t) = reloc (Store.mapH g s₀) (Store.mapH g t) := by
  have hsh : Shift.ofStore (Store.mapH g s₀) = Shift.ofStore s₀ := by
    simp [Shift.ofStore, Store.mapH]
  simp only [reloc, hsh]
  simp [Store.mapH, Store.app, Shift.store, List.map_append, List.map_map, Function.comp_def,
    Shift.finst, FuncInst.mapH]


/-- Renaming host code twice is renaming by the composite. -/
theorem mapH_mapH {H H' H'' : Type} (g : H' → H'') (g' : H → H') (s : Store H) :
    Store.mapH g (Store.mapH g' s) = Store.mapH (g ∘ g') s := by
  have hf : ∀ fi : FuncInst H,
      FuncInst.mapH g (FuncInst.mapH g' fi) = FuncInst.mapH (g ∘ g') fi := by
    intro fi
    cases hc : fi.code <;> simp [FuncInst.mapH, FuncCode.mapH, hc]
  simp [Store.mapH, List.map_map, Function.comp_def, hf]

/-- Renamings agreeing on the host code of a store rename it alike. -/
theorem mapH_congr_hosts {H H' : Type} {Q : H → Prop} {s : Store H} (hs : HostsSat Q s)
    {g g' : H → H'} (hg : ∀ h, Q h → g h = g' h) : Store.mapH g s = Store.mapH g' s := by
  have hf : s.funcs.map (FuncInst.mapH g) = s.funcs.map (FuncInst.mapH g') := by
    refine List.map_congr_left fun fi hfi => ?_
    obtain ⟨a, ha⟩ := List.getElem?_of_mem hfi
    cases hc : fi.code with
    | wasm f => simp only [FuncInst.mapH, FuncCode.mapH, hc]
    | host h => simp only [FuncInst.mapH, FuncCode.mapH, hc, hg h (hs a fi h ha hc)]
  simp only [Store.mapH, hf]

/-- Preparing a module adds no host code. -/
theorem hostsSat_prepareE {H : Type} {Q : H → Prop} {s s' : Store H}
    {m : Silmaril.Wasm.Module} {xas : List Silmaril.Wasm.Execution.Core.ExternAddr}
    {mi : Silmaril.Wasm.Execution.Core.ModuleInst} {st : Option Nat} (hs : HostsSat Q s)
    (h : Silmaril.Wasm.Component.Engine.Core3.prepareE? s m xas = some (s', mi, st)) :
    HostsSat Q s' := by
  unfold Silmaril.Wasm.Component.Engine.Core3.prepareE? at h
  split at h
  · cases h
  · split_ifs at h
    split at h
    · cases h
    · next heq =>
      cases h
      exact hostsSat_instantiateOnce hs heq
    · next heq =>
      obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.mp h
      cases ha
      exact hostsSat_instantiateOnce hs heq


/-- The exporter's core store has no host functions. -/
theorem hostsSat_cse {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (E3 P).Store (CanonHost (E3 P))} {cie : (E3 P).Inst}
    (hFe : CoreFacts (Pf := P) c I cse cie) :
    HostsSat (fun _ => False) (cse : Store (CanonHost (E3 P))) :=
  hostsSat_prepareE (fun a fi _ ha _ => by
    change (({} : Store (CanonHost (E3 P))).funcs)[a]? = some fi at ha
    simp at ha) hFe.prepare

/-- **The shared core store after instantiation, renamed**: under `gL` it is the exporter
instance's store followed by the importer instance's, relocated (`instBehavioursL_inst`). -/
theorem linkStore_mapH {l : Linked2} (hn : l.WireNodup) (hw : l.WireTy)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P).Store (CanonHost (E3 P))}
    {cie : (E3 P).Inst} (hFe : CoreFacts (Pf := P) l.exp Ie cse cie)
    {r : Store (CanonHost (E3 P) × Nat)} (hrs : Store.mapH Prod.snd r = Ii.store)
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r) :
    Store.mapH (gL P l) (reloc cse (Store.mapH Prod.fst r)) = reloc Ie.store Ii.store := by
  have hcse := hostsSat_cse hFe
  have he : Store.mapH (gL P l) cse = Ie.store :=
    (mapH_congr_hosts hcse (g' := fun _ => 0) fun _ h => h.elim).trans hFe.store
  have hi : Store.mapH (gL P l) (Store.mapH Prod.fst r) = Ii.store := by
    rw [mapH_mapH, ← hrs]
    refine mapH_congr_hosts hh ?_
    rintro _ ⟨k, hk, rfl⟩
    show l.trampIdxL (E := E3 P) (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩) = k
    exact trampIdxL_wireFid hn (hw.length ▸ hk) _ _ _
  have e := mapH_reloc (gL P l) (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)
  rw [he, hi] at e
  exact e


/-- The exporter's export functions are functions of a store at which it is well formed. -/
theorem addr_lt_of_wf {m : Silmaril.Wasm.Component.Reference.NumModule}
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I) {s : Store Nat}
    (hw : I.WellFormed s) {k : Nat} (hk : k < m.exports.length) :
    I.addrs.getD k 0 < s.funcs.length := by
  have hlen : k < I.exports.length := by rw [hI.2.2, List.length_map]; exact hk
  obtain ⟨fi, hfi, -⟩ := hw.export_type ⟨k, hlen⟩
  exact (List.getElem?_eq_some_iff.mp hfi).1

/-- **The exporter's export functions are owned by its part** at its instance's store. -/
theorem owned_init {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} (hc : c.Good)
    (hI : c.mod.IsInst I) : ∀ xe ∈ c.exports, (ownOf I.store).fn (I.addrs.getD xe.core 0) := by
  intro xe hx
  obtain ⟨nm, hn⟩ := hc.core xe hx
  exact addr_lt_of_wf hI hI.1.choose_spec.ok (List.getElem?_eq_some_iff.mp hn).1

/-- A function of the relocated suffix is the shifted, renamed function of the part. -/
theorem reloc_suffix_get {H : Type} {cs : Store (CanonHost (E3 P))} {r : Store H}
    {g : H → CanonHost (E3 P)} {A : Nat} {fi : FuncInst (CanonHost (E3 P))}
    (hge : cs.funcs.length ≤ A) (hA : (reloc cs (Store.mapH g r)).funcs[A]? = some fi) :
    ∃ fr, r.funcs[A - cs.funcs.length]? = some fr ∧ (sh cs).finst (FuncInst.mapH g fr) = fi := by
  have h₁ : ((r.funcs[A - cs.funcs.length]?).map (FuncInst.mapH g)).map (sh cs).finst =
      some fi := by
    rw [← Store.mapH_funcs_getElem?, ← List.getElem?_map, ← List.getElem?_append_right hge]
    exact hA
  cases e : r.funcs[A - cs.funcs.length]? with
  | none => simp [e] at h₁
  | some fr => exact ⟨fr, rfl, by simpa [e] using h₁⟩

/-- Host code renamed by the first projection comes from a pair. -/
theorem mapH_fst_host {H K : Type} {fr : FuncInst (H × K)} {h : H}
    (hc : (FuncInst.mapH Prod.fst fr).code = .host h) :
    ∃ hk, fr.code = .host hk ∧ hk.1 = h := by
  cases hcode : fr.code with
  | wasm f => simp [FuncInst.mapH, FuncCode.mapH, hcode] at hc
  | host hk => exact ⟨hk, rfl, by simpa [FuncInst.mapH, FuncCode.mapH, hcode] using hc⟩

/-- **The host functions of the shared core store are the importer's trampolines.** -/
theorem tramp_linkStore {l : Linked2} {cs : Store (CanonHost (E3 P))}
    (hcse : HostsSat (fun _ => False) cs) {r : Store (CanonHost (E3 P) × Nat)}
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r) :
    ∀ (A : Nat) (fi : FuncInst (CanonHost (E3 P))) (h : CanonHost (E3 P)),
      (reloc cs (Store.mapH Prod.fst r)).funcs[A]? = some fi →
      fi.code = .host h →
      ∃ k nm p, h = .lowered (l.wireFid k) (witFt p) {} ⟨2⟩ ∧ l.imp.imports[k]? = some (nm, p) := by
  intro A fi h hA hc
  rcases Nat.lt_or_ge A cs.funcs.length with hlt | hge
  · have h₁ : cs.funcs[A]? = some fi :=
      (List.getElem?_append_left (l₂ := (Store.mapH Prod.fst r).funcs.map (sh cs).finst)
        hlt).symm.trans hA
    exact (hcse A fi h h₁ hc).elim
  obtain ⟨fr, hfr, hfe⟩ := reloc_suffix_get hge hA
  have hcf : (FuncInst.mapH Prod.fst fr).code = .host h := by
    rw [← hc, ← hfe]
    rfl
  obtain ⟨hk, hcode, hh'⟩ := mapH_fst_host hcf
  obtain ⟨k, hkl, hke⟩ := hh _ fr hk hfr hcode
  have hkh : h = .lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩ := by
    rw [← hh', hke]
  exact ⟨k, l.imp.imports[k].1, l.imp.imports[k].2, hkh, List.getElem?_eq_getElem hkl⟩


/-- The lifted function of the exporter's export `w`, at the front of the component functions. -/
theorem lifted_init {l : Linked2} {Ie : Silmaril.Wasm.Game.ScalarInstance}
    (rest : List (CFuncInst (E3 P))) {k w : Nat} {xe : SimpleExport}
    (hw : l.wire[k]? = some w) (hxe : l.exp.exports[w]? = some xe) :
    (liftedList (Pf := P) (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++ rest)[(l.wireFid k).idx]? =
      some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) := by
  have hwl : w < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
  have hidx : (l.wireFid k).idx = w := wire_getD hw
  rw [hidx, List.getElem?_append_left (by simpa [liftedList] using hwl)]
  simp [liftedList, hxe, liftedFt, witFt]

/-- **The static facts of a linked call after instantiation**: from the core facts of the
exporter (`CoreFacts`) and the importer's store `r` of `instBehavioursL_inst`, with the frame's
component functions those of `afterLink`. -/
theorem lstat_init {l : Linked2} (hEg : l.exp.Good) (hIg : l.imp.Good) (hW : l.WireTy)
    (hn : l.WireNodup) (har : l.imp.Arity) (hff : l.imp.FloatFree)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P).Store (CanonHost (E3 P))}
    {cie : (E3 P).Inst} (hFe : CoreFacts (Pf := P) l.exp Ie cse cie) (hI : l.imp.mod.IsInst Ii)
    {r : Store (CanonHost (E3 P) × Nat)}
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r)
    {B : Machine.Config (E3 P) σ} (rest : List (CFuncInst (E3 P)))
    (hB : B.store.funcs = liftedList (Pf := P) (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++ rest) :
    LStat P l Ie Ii Ii.store (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      B (ownOf Ie.store) where
  expGood := hEg
  expInst := hFe.isInst
  impGood := hIg
  impInst := hI
  impWf := hI.1.choose_spec.ok
  wireTy := hW
  nodup := hn
  arity := har
  floats := hff
  tramp := tramp_linkStore (hostsSat_cse hFe) hh
  lifted := fun k w xe hw hxe => by
    simp only [ArenaField.get?, ArenaField.funcs, hB, Arena.get?_eq_getElem?]
    exact lifted_init rest hw hxe
  owned := owned_init hEg hFe.isInst

/-- The exporter's store is a prefix of the relocated shared store. -/
theorem fnPre_prefix (s₀ u : Store Nat) : FnPre ({} : Store Nat) (reloc s₀ u) s₀ := by
  rw [fnPre_empty_iff]
  intro a fi h
  rw [reloc_funcs, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1, h]

/-- **The invariant at the importer's export call**: the shared core store renames under
`gL` to the exporter's store `s₀` followed by the importer's `u`, relocated, both good, with the
functions `F₀`; the shared thread invokes the relocated address of the export question `f` on
flat arguments. The part is the pending invocation of `f` from `u`, the exporter's store is
`s₀`, and the ownerships are those of `rel4_init`. -/
theorem linv_init {y : CoreSt (E3 P)} (hg₀ : StoreGood s₀) (hgu : StoreGood u)
    (hy : Store.mapH (gL P l) y.1 = reloc s₀ u) (hF : y.1.funcs = F₀) (hwf : Ie.WellFormed s₀)
    (ha : Ii.addr f.1 < u.funcs.length) {xs : List Flat}
    (hxs : f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat)
    (hth : y.2 = Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (s₀.funcs.length + Ii.addr f.1) xs) :
    LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u)) f y (u, Ii.initThread f) s₀ := by
  have hR := rel4_init hg₀ hgu
  have hvs : ∀ v ∈ f.2.1, ∀ r, v ≠ .ref r := hxs ▸ ofFlat_scalar xs
  have hO : (shOwn (sh s₀) (ownOf u)).fn (s₀.funcs.length + Ii.addr f.1) :=
    ⟨Nat.le_add_right _ _, by simpa [ownOf] using ha⟩
  have hL := linkSt_invoke hR.rc (fnPre_refl s₀ u) ha hO hvs (splitGood_invoke hgu ha hvs)
  have hshared : (Store.mapH (gL P l) y.1, y.2) = (reloc s₀ u,
      Silmaril.Wasm.SingleThreaded.Thread.pending (s₀.funcs.length + Ii.addr f.1) f.2.1) := by
    rw [hy, hth, hxs]
    rfl
  have hR' : Rel4 (ownOf s₀) (shOwn (sh s₀) (ownOf u)) Ren.id (ownOf s₀) Ren.id
      (shOwn (sh s₀) (ownOf u)) (Store.mapH (gL P l) y.1) s₀ (reloc s₀ u) := by
    rw [hy]
    exact hR
  refine ⟨⟨_, _, _, _, hshared ▸ hL, hR'⟩, hy ▸ fnPre_prefix s₀ u, hwf, hF, ?_⟩
  exact .refl

/-- **The invariant at the importer's export call after instantiation**: the shared core store
of `instBehavioursL_inst`, the shared thread invoking the relocated address of the export
question `f` of `Ii` on flat arguments; the part at the pending invocation from `Ii.store`, the
exporter at `Ie.store`. -/
theorem linv_afterLink {l : Linked2} (hS : l.SplitOk) (hn : l.WireNodup) (hW : l.WireTy)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P).Store (CanonHost (E3 P))}
    {cie : (E3 P).Inst} (hFe : CoreFacts (Pf := P) l.exp Ie cse cie) (hI : l.imp.mod.IsInst Ii)
    {r : Store (CanonHost (E3 P) × Nat)} (hrs : Store.mapH Prod.snd r = Ii.store)
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r)
    {f : Ii.F.Op} {xs : List Flat} (hxs : f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat) :
    LInv P l Ie Ii Ie.store Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs (ownOf Ie.store)
      (shOwn (sh Ie.store) (ownOf Ii.store)) f
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r),
        Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.store.funcs.length + Ii.addr f.1) xs)
      (Ii.store, Ii.initThread f) Ie.store := by
  have hwi : Ii.WellFormed Ii.store := hI.1.choose_spec.ok
  have hwe : Ie.WellFormed Ie.store := hFe.isInst.1.choose_spec.ok
  have hg₀ : StoreGood Ie.store := storeGood_inst hS.exp hFe.isInst.1.choose_spec
  have hgu : StoreGood Ii.store := storeGood_inst hS.imp hI.1.choose_spec
  obtain ⟨fi, hfi, -⟩ := hwi.export_type f.1
  exact linv_init hg₀ hgu (linkStore_mapH hn hW hFe hrs hh) rfl hwe
    (List.getElem?_eq_some_iff.mp hfi).1 hxs rfl


end Start

end Silmaril.Proofs.Wasm.Component.Reference

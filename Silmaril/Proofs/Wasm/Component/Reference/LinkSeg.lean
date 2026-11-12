module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkImp
public import Silmaril.Proofs.Wasm.Component.Reference.CalloutPath

/-!
# The importer's half of a linked call along segmented runs

The importer of a `Linked2` runs as the relocated part of the shared core store, renamed to
`Nat` host codes by `g = trampIdxL l` (its trampoline of import `k` has code `k`). Along a
segmented run (`LSeg`) we keep `LInv`: the importer's part thread `x` (its own store) is
related to the shared thread (`LinkSt`, prefix `s₀`), the exporter's store `π` and the importer's
relocated store embed disjointly (`Rel4`), the exporter's functions are the shared store's
(`FnPre {}`), `Ie` is well formed at `π`, the shared functions are the initial ones `F₀`, and the
part's run is a product run of the export call `f` of `Ii` against the environment answering
every import question with typed values (`valEnv`), which types its callouts.

The static facts of the shared store and the frame (`LStat`): every host function of `F₀` is the
trampoline of an import `k` (`.lowered (wireFid l k) (witFt p) {} ⟨2⟩`, `p` the import's type),
the frame's component function `wireFid l k` is the exporter's lifted export `wire[k]`, and the
exporter's export functions are owned by its part.

* `LInv.reach`: host-free shared runs keep `LInv` (`reach_link_back`, `Rel4.after_c`);
* `LInv.callout`: a callout of the shared thread is the trampoline of an import `k`, the part is
  stopped at the typed import question of `k` on the same arguments;
* `LInv.site`: it is a `LinkSite` (`linkSite_exp`);
* `LInv.resume`: after the exporter's nested run returns values that lift, the resumed threads
  satisfy `LInv` again, with the exporter's new store, the nested call a returned call (`RetAt`);
* `LInv.linkOk`: `LinkOk` holds from every point satisfying `LInv`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch Rel4)

/-! ## Typing the importer's part -/

/-- The environment answering every import question with typed values (one state). -/
def valEnv (I : Silmaril.Wasm.Game.ScalarInstance) : Silmaril.Wasm.Game.SEnv I.E :=
  ⟨Unit, fun _ _ w _ => ∃ v, w = .values v, fun _ _ => False⟩

theorem valEnv_throwsBelow (I : Silmaril.Wasm.Game.ScalarInstance) (n : Nat) :
    (valEnv I).ThrowsBelow n := by
  rintro q e w q' ⟨v, rfl⟩
  trivial

/-- Arguments of the flat scalar types `ts` that are flat have the types `ts`. -/
theorem flat_types_of_hasVal :
    ∀ {ts : List Silmaril.Wasm.NumType} {args : List Silmaril.Wasm.Execution.Core.Val}
      {ys : List Flat},
      List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (ts.map .num) args →
      args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys → ys.map (·.type) = ts
  | [], [], ys, .nil, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | t :: ts, v :: args, ys, .cons ⟨bits, hv⟩ hr, h => by
    subst hv
    cases hm : args.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
    | none => simp [List.mapM_cons, hm] at h
    | some ys' =>
      simp only [List.mapM_cons, hm, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.some.injEq, Silmaril.Wasm.SingleThreaded.toFlat?] at h
      subst h
      simp only [List.map_cons, flat_types_of_hasVal hr hm]

/-- Flat values are scalar. -/
theorem ofFlat_scalar (zs : List Flat) :
    ∀ v ∈ zs.map Silmaril.Wasm.SingleThreaded.ofFlat, ∀ r, v ≠ .ref r := by
  intro v hv r
  obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv
  exact nofun

/-- Values that are flat are their own image under a code map. -/
theorem map_val_of_mapM (M : CMap) {args : List Silmaril.Wasm.Execution.Core.Val}
    {ys : List Flat} (h : (args.map M.val).mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys) :
    args.map M.val = args :=
  map_val_flat M h

/-- Shared host-free runs keep the functions. -/
theorem reach_funcs' {P : Profile} {H : Type} {x y : Store H × Silmaril.Wasm.SingleThreaded.Thread}
    (h : Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) x y) : y.1.funcs = x.1.funcs := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    exact (Silmaril.Proofs.Wasm.Game.InternalP.funcs_prefix (P := P) (s := _) (t := (_ : Store H ×
      Silmaril.Wasm.SingleThreaded.Thread).2) hst).trans ih

theorem mapH_funcs_eq {H H' : Type} (g : H → H') {s s' : Store H} (h : s'.funcs = s.funcs) :
    (Store.mapH g s').funcs = (Store.mapH g s).funcs := by
  simp only [Store.mapH, h]

/-! ## The static facts and the invariant -/

variable {P : Profile} {σ : Type}

/-- **The static facts of a linked call**: the two components and instances, the wiring, the
arities and float-freedom of the imports, the trampolines of the shared functions `F₀`, the
lifted exports in the frame `B`, the exporter's export functions owned by its part. -/
structure LStat (P : Profile) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P)))) (B : Machine.Config (E3 P) σ)
    (Op₀ : Own) : Prop where
  expGood : l.exp.Good
  expInst : l.exp.mod.IsInst Ie
  impGood : l.imp.Good
  impInst : l.imp.mod.IsInst Ii
  impWf : Ii.WellFormed u₀
  wireTy : l.WireTy
  nodup : l.WireNodup
  arity : l.imp.Arity
  floats : l.imp.FloatFree
  tramp : ∀ (A : Nat) (fi : FuncInst (CanonHost (E3 P))) (h : CanonHost (E3 P)),
    F₀[A]? = some fi → fi.code = .host h →
    ∃ k nm p, h = .lowered (l.wireFid k) (witFt p) {} ⟨2⟩ ∧ l.imp.imports[k]? = some (nm, p)
  lifted : ∀ k w (xe : SimpleExport), l.wire[k]? = some w → l.exp.exports[w]? = some xe →
    ArenaField.funcs.get? B.store (l.wireFid k) =
      some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩)
  owned : ∀ xe ∈ l.exp.exports, Op₀.fn (Ie.addrs.getD xe.core 0)

/-- The renaming of the shared store's host codes: trampolines to their import index. -/
abbrev gL (P : Profile) (l : Linked2) : CanonHost (E3 P) → Nat := l.trampIdxL (E := E3 P)

/-- **The invariant along a segmented run** at the shared thread `y`, the importer's part thread
`x` and the exporter's store `π`. -/
structure LInv (P : Profile) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (s₀ u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P)))) (Op₀ Oc₀ : Own) (f : Ii.F.Op)
    (y : CoreSt (E3 P)) (x : Store Nat × Silmaril.Wasm.SingleThreaded.Thread) (π : Store Nat) :
    Prop where
  rel : ∃ ρp Op ρc Oc, LinkSt s₀ ρc Oc x (Store.mapH (gL P l) y.1, y.2) ∧
    Rel4 Op₀ Oc₀ ρp Op ρc Oc (Store.mapH (gL P l) y.1) π (reloc s₀ x.1)
  fnE : FnPre ({} : Store Nat) (Store.mapH (gL P l) y.1) π
  wf : Ie.WellFormed π
  funcs : y.1.funcs = F₀
  run : Silmaril.Wasm.Game.SSteps P (valEnv Ii) (Silmaril.Wasm.Execution.Core.invoke u₀ (Ii.addr f.1) f.2.1, ())
    (x.2.config x.1, ())

section Inv

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ} {Op₀ Oc₀ : Own}
  {f : Ii.F.Op} {y : CoreSt (E3 P)} {x : Store Nat × Silmaril.Wasm.SingleThreaded.Thread}
  {π : Store Nat}

/-- The part thread is typed. -/
theorem LInv.typed (S : LStat P l Ie Ii u₀ F₀ B Op₀) (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π) :
    ∃ ts, Silmaril.Wasm.Execution.Core.StoreOk x.1 ∧
      Silmaril.Wasm.SingleThreaded.ThreadOk x.1 x.2 ts := by
  obtain ⟨ts, hg₀⟩ := SEnvTyping.good_invoke S.impWf f
  have hg := SEnvTyping.good_ssteps (P := P) S.impWf (valEnv_throwsBelow Ii _)
    (x := (_, ())) (y := (x.2.config x.1, ())) hg₀ hI.run
  have hs : Silmaril.Wasm.Execution.Core.StoreOk (x.2.config x.1).store := Silmaril.Wasm.SingleThreaded.ConfigOk.storeOk hg.ok
  rw [Silmaril.Wasm.SingleThreaded.Thread.config_store] at hs
  exact ⟨ts, hs, hg.ok⟩

/-- **Host-free shared runs keep the invariant**, the part running host-free alongside. -/
theorem LInv.reach (S : LStat P l Ie Ii u₀ F₀ B Op₀) (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π)
    {y' : CoreSt (E3 P)} (hy : Relation.ReflTransGen (CoreStep (E3 P)) y y') :
    ∃ x', LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y' x' π ∧ Silmaril.Wasm.Game.Reach P x x' := by
  obtain ⟨ρp, Op, ρc, Oc, hL, hR⟩ := hI.rel
  obtain ⟨ts, hs, ht⟩ := hI.typed S
  have hrun := reach_mapH (gL P l) (coreSteps_internalP hy)
  obtain ⟨x', ρc', Oc', prun, hL', hgr, htc, -, -⟩ := reach_link_back hrun hL hs ht
  have hrc : PartRel ρc' Oc' (reloc s₀ x'.1) (Store.mapH (gL P l) y'.1) := by
    have h := hL'.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at h
  have hfy : y'.1.funcs = y.1.funcs := reach_funcs' (coreSteps_internalP hy)
  refine ⟨x', ⟨⟨ρp, Op, ρc', Oc', hL', Rel4.after_c hR hrc hgr htc⟩,
    hI.fnE.congr (mapH_funcs_eq _ hfy) rfl, hI.wf, hfy.trans hI.funcs, ?_⟩, prun⟩
  exact hI.run.trans (reach_ssteps prun)

/-- **A callout of the shared thread is a trampoline call of the importer**: the trampoline of
an import `k` (type `p`, wired to the exporter's export `xe` of type `p`), the part stopped at
the redex of host code `k` on the same arguments, a typed import question of `Ii`, whose flat
arguments have the flat parameter types. -/
theorem LInv.callout (S : LStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π) {h : CanonHost (E3 P)} {ys : List Flat}
    (hst : (E3 P).status y.1 y.2 = .callout h ys) :
    ∃ (k : Nat) (nm : String) (p : FuncTy) (w : Nat) (xe : SimpleExport)
      (E : Silmaril.Wasm.SingleThreaded.Ctx) (a : Nat) (args : List Silmaril.Wasm.Execution.Core.Val)
      (e : Ii.E.Op),
      h = .lowered (l.wireFid k) (witFt p) {} ⟨2⟩ ∧ l.imp.imports[k]? = some (nm, p) ∧
      l.wire[k]? = some w ∧ l.exp.exports[w]? = some xe ∧ xe.ty = p ∧
      Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args) ∧
      args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys ∧ Ii.importOp? k args = some e ∧
      ys.map (·.type) = ValTy.flatList p.params := by
  obtain ⟨E', A, args', hd, hm⟩ := status_callout_redex hst
  obtain ⟨fi, -, -, -, hf, hcode, -⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  rw [hI.funcs] at hf
  obtain ⟨k, nm, p, rfl, hk⟩ := S.tramp A fi h hf hcode
  obtain ⟨hk', hpk⟩ := List.getElem?_eq_some_iff.mp hk
  have hkl : k < l.wire.length := S.wireTy.length ▸ hk'
  have hg : gL P l (.lowered (l.wireFid k) (witFt p) {} ⟨2⟩) = k :=
    trampIdxL_wireFid S.nodup hkl _ _ _
  have hdm : Silmaril.Wasm.SingleThreaded.decompose? (Store.mapH (gL P l) y.1)
      (y.2.config (Store.mapH (gL P l) y.1)).code = some (E', A, k, args') := by
    refine (decompose?_config_mapH (gL P l) y.1 y.2).trans ?_
    rw [hd]
    simp only [Option.map_some, mapR, hg]
  obtain ⟨ρp, Op, ρc, Oc, hL, -⟩ := hI.rel
  obtain ⟨ts, hs, ht⟩ := hI.typed S
  obtain ⟨E, a, args, hdx, -, -, hargs⟩ := callout_back P hL hs ht hdm
  have hm' : args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys := by
    have hmm : (args.map (linkMap s₀ ρc).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? =
        some ys := hargs ▸ hm
    rwa [map_val_flat _ hmm] at hmm
  have hdx' : Silmaril.Wasm.SingleThreaded.decompose? (x.2.config x.1).store
      (x.2.config x.1).code = some (E, a, k, args) := by
    rw [Silmaril.Wasm.SingleThreaded.Thread.config_store]
    exact hdx
  obtain ⟨e, he⟩ := SEnvTyping.sstep_callout_typed S.impWf (valEnv_throwsBelow Ii _) hI.run hdx'
  obtain ⟨w, hw⟩ : ∃ w, l.wire[k]? = some w := ⟨_, List.getElem?_eq_getElem hkl⟩
  obtain ⟨xe, hxe, hty⟩ := S.wireTy.ty k w hw
  have hpx : xe.ty = p := by
    rw [hk] at hty
    simp only [Option.map_some, Option.some.injEq] at hty
    exact hty.symm
  have hek := ifaceOp?_some he
  have h2 : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (Ii.imports.get e.1).params args :=
    hek.2 ▸ e.2.2
  rw [imports_get S.impGood S.impInst e k hk' hek.1, hpk] at h2
  exact ⟨k, nm, p, w, xe, E, a, args, e, rfl, hk, hw, hxe, hpx, hdx, hm', he,
    flat_types_of_hasVal h2 hm'⟩

/-- **A callout of the shared thread is a link site.** -/
theorem LInv.site (S : LStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π) {h : CanonHost (E3 P)} {ys : List Flat}
    (hst : (E3 P).status y.1 y.2 = .callout h ys) : LinkSite B y h ys := by
  obtain ⟨k, nm, p, w, xe, E, a, args, e, rfl, hk, hw, hxe, rfl, -, -, -, hys⟩ := hI.callout S hst
  obtain ⟨ρp, Op, ρc, Oc, -, hR⟩ := hI.rel
  have hmem : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
  have hmi : (nm, xe.ty) ∈ l.imp.imports := List.mem_of_getElem? hk
  obtain ⟨hmaxp, hmaxr, hres⟩ := S.arity.2 _ hmi
  obtain ⟨hpf, hrf⟩ := S.floats.2 _ hmi
  exact linkSite_exp (S.lifted k w xe hw hxe) hpf hys hmaxp hres hrf hmaxr S.expInst
    (S.expGood.core xe hmem) hI.wf (gL P l) hR hI.fnE (S.owned xe hmem)

/-- The typed values answer of the import question `e` of `Ii` from the lowering of results
`us` of the import's type. -/
theorem resAnswer (S : LStat P l Ie Ii u₀ F₀ B Op₀) {e : Ii.E.Op} {k : Nat} {nm : String}
    {p : FuncTy} (hk : l.imp.imports[k]? = some (nm, p)) (he : e.1.val = k)
    {us : List Silmaril.Wasm.Component.Val} (hus : ValTy.checkList p.results us = true) :
    List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (Ii.imports.get e.1).results
      ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat) := by
  obtain ⟨hk', hpk⟩ := List.getElem?_eq_some_iff.mp hk
  have hty : (lowerArgs p.results us).map (·.type) = ValTy.flatList p.results :=
    lowerList_types _ _ hus
  have heq : (Silmaril.Wasm.Component.Reference.fnOf l.imp.imports[k].2.flat).results =
      (lowerArgs p.results us).map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) := by
    rw [hpk]
    show (ValTy.flatList p.results).map _ = _
    rw [← hty, List.map_map]
    rfl
  rw [imports_get S.impGood S.impInst e k hk' he, heq]
  exact forall₂_hasVal_ofFlat _

/-- **After a nested call the invariant holds again**: the exporter's run from the shared store
at the callout, on the lowering of the lifted arguments, returns values that lift to `us`; the
shared thread resumed with their lowering and the part resumed with the same values satisfy
`LInv` with the exporter's store `π'` after a returned call `RetAt`. -/
theorem LInv.resume (S : LStat P l Ie Ii u₀ F₀ B Op₀)
    (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π) {k : Nat} {nm : String} {w : Nat}
    {xe : SimpleExport} {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} {e : Ii.E.Op}
    (hk : l.imp.imports[k]? = some (nm, xe.ty)) (hxe : l.exp.exports[w]? = some xe)
    (hdx : Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args))
    (he : Ii.importOp? k args = some e) {ys : List Flat} {ws : List Silmaril.Wasm.Component.Val}
    (hws : liftArgs xe.ty.params ys = some ws) {ev : CoreSt (E3 P)}
    (hrun : Relation.ReflTransGen (CoreStep (E3 P))
      (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
        (lowerArgs xe.ty.params ws)) ev)
    {zs : List Flat} (hzs : (E3 P).status ev.1 ev.2 = .returned (.values zs))
    {us : List Silmaril.Wasm.Component.Val} (hus : liftArgs xe.ty.results zs = some us) :
    ∃ π', LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f
        (ev.1, (E3 P).resume ev.1 y.2 (.values (lowerArgs xe.ty.results us)))
        (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
          (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) π' ∧
      RetAt P l.exp Ie xe ws π us π' := by
  obtain ⟨ρp, Op, ρc, Oc, hL, hR⟩ := hI.rel
  have hmem : xe ∈ l.exp.exports := List.mem_of_getElem? hxe
  have typed : ValTy.checkList xe.ty.params ws = true :=
    Silmaril.Wasm.Component.checkList_of_liftArgs hws
  obtain ⟨π', ρp', Op', hR', hF', -, hval, -⟩ := exp_run (vs := ws) S.expInst
    (S.expGood.core xe hmem) typed hI.wf (gL P l) hR hI.fnE (S.owned xe hmem) hrun
  obtain ⟨hRet, hwf'⟩ := (hval zs hzs).2.2 us hus
  have hfe : ev.1.funcs = y.1.funcs :=
    reach_funcs' (x := (y.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (Ie.addrs.getD xe.core 0) (lowerArgs xe.ty.params ws))) (coreSteps_internalP hrun)
  have hfm : (Store.mapH (gL P l) ev.1).funcs = (Store.mapH (gL P l) y.1).funcs :=
    mapH_funcs_eq (gL P l) hfe
  have hL1 : LinkSt s₀ ρc Oc x (Store.mapH (gL P l) ev.1, y.2) := linkSt_transport hL hfm hR'.rc
  have hL2 : LinkSt s₀ ρc Oc
      (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)))
      (Store.mapH (gL P l) ev.1, Silmaril.Wasm.SingleThreaded.resumeResult
        (Store.mapH (gL P l) ev.1) y.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) :=
    link_resume hL1 hdx (ofFlat_scalar _)
  have hres : (E3 P).resume ev.1 y.2 (.values (lowerArgs xe.ty.results us)) =
      Silmaril.Wasm.SingleThreaded.resumeResult (Store.mapH (gL P l) ev.1) y.2
        (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)) :=
    (resume_values ev.1 y.2 _).trans (resumeResult_mapH (gL P l) ev.1 y.2 _).symm
  have hcheck : ValTy.checkList xe.ty.results us = true :=
    Silmaril.Wasm.Component.checkList_of_liftArgs hus
  have hek : e.1.val = k ∧ e.2.1 = args := ifaceOp?_some he
  have hdx' : Silmaril.Wasm.SingleThreaded.decompose? (x.2.config x.1).store
      (x.2.config x.1).code = some (E, a, k, args) :=
    (Silmaril.Wasm.SingleThreaded.Thread.config_store x.1 x.2).symm ▸ hdx
  have hstep : Silmaril.Wasm.Game.SStep P (valEnv Ii) (x.2.config x.1, ())
      (⟨(x.2.config x.1).store, (x.2.config x.1).frame,
        E.fill (Silmaril.Wasm.Execution.Core.Result.values
          ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)).toAdmin⟩, ()) :=
    Silmaril.Wasm.Game.SStep.answer (P := P) (L := valEnv Ii) (q := ()) (q' := ())
      (w := .values ⟨_, resAnswer S hk hek.1 hcheck⟩) hdx' he ⟨_, rfl⟩
  have hcfg := resumeResult_config hdx'
    (.values ((lowerArgs xe.ty.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))
  refine ⟨π', ⟨⟨ρp', Op', ρc, Oc, hres ▸ hL2, hR'⟩, hF', hwf', hfe.trans hI.funcs, ?_⟩, hRet⟩
  show Silmaril.Wasm.Game.SSteps P (valEnv Ii) _ (Silmaril.Wasm.SingleThreaded.Thread.config x.1
    (Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2 _), ())
  rw [hcfg]
  exact hI.run.tail hstep

end Inv

/-! ## The exporter's returned calls -/

/-- **Returned calls of the wired exports** from the exporter's store `s` to `s'`, answering the
importer's component import calls `ds` in order (the returned prefix of `Linked2.ExpRun`). -/
inductive ExpSeg (P : Profile) (l : Linked2) (I : Silmaril.Wasm.Game.ScalarInstance) :
    Store Nat → List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload) → Store Nat → Prop
  | nil (s : Store Nat) : ExpSeg P l I s [] s
  | ret {s s' s'' : Store Nat} {k : Fin l.imp.imports.length}
      {ws us : List Silmaril.Wasm.Component.Val}
      {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
      (w : Fin l.exp.exports.length) :
      l.wire[k.val]? = some w.val → RetAt P l.exp I l.exp.exports[w] ws s us s' →
      ExpSeg P l I s' ds s'' → ExpSeg P l I s (⟨(k, .vals ws), some (.vals us)⟩ :: ds) s''

theorem ExpSeg.append {l : Linked2} {I : Silmaril.Wasm.Game.ScalarInstance} {s s₁ s₂ : Store Nat}
    {ds ds' : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (h : ExpSeg P l I s ds s₁) (h' : ExpSeg P l I s₁ ds' s₂) : ExpSeg P l I s (ds ++ ds') s₂ := by
  induction h with
  | nil => exact h'
  | ret w hw hr _ ih => exact .ret w hw hr (ih h')

/-- **A returned prefix followed by a run of the exporter is a run.** -/
theorem ExpSeg.run {l : Linked2} {I : Silmaril.Wasm.Game.ScalarInstance} {s s' : Store Nat}
    {ds ds' : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (h : ExpSeg P l I s ds s') (h' : Linked2.ExpRun P l I s' ds') :
    Linked2.ExpRun P l I s (ds ++ ds') := by
  induction h with
  | nil => exact h'
  | ret w hw hr _ ih => exact .ret w hw hr (ih h')

/-! ## Segmented runs as plays of the importer -/

section Path

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ} {Op₀ Oc₀ : Own}
  {f : Ii.F.Op}

/-- **A nested call is a component import call related to its round**: the import question `e`
of `k` on the flat arguments `ys` lifting to `ws`, answered with the lowering of `us`, is the
component import call of `k` on `ws` answered `us`. -/
theorem impRel_link {e : Ii.E.Op} {k : Nat} {nm : String} {p : FuncTy}
    (hk : l.imp.imports[k]? = some (nm, p)) (hek : e.1.val = k)
    {args : List Silmaril.Wasm.Execution.Core.Val} (hea : e.2.1 = args) {ys : List Flat}
    (hm : args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys)
    {ws us : List Silmaril.Wasm.Component.Val} (hws : liftArgs p.params ys = some ws)
    (hus : ValTy.checkList p.results us = true)
    (wv : Ii.E.Ar e)
    (hwv : Silmaril.Wasm.Game.Answer.toResult wv =
      .values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)) :
    Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii ⟨e, wv⟩
      [⟨(⟨e.1.val, hek ▸ (List.getElem?_eq_some_iff.mp hk).1⟩, .vals ws), some (.vals us)⟩] := by
  have hk' : l.imp.imports[e.1.val]? = some (nm, p) := hek ▸ hk
  have hup : (some (Payload.vals us)).bind (Silmaril.Wasm.Component.Adapter.lower p).up =
      some (.flat (lowerArgs p.results us)) := by
    simp only [Option.bind_some, Silmaril.Wasm.Component.Adapter.up, Silmaril.Wasm.Component.checkLower,
      hus, ite_true, Option.map_some]
  refine ⟨nm, p, _, hk', payloadAnswer_flat hwv, ?_⟩
  show match liftArgs p.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
    | none => _ | some ws => _
  rw [hea, filterMap_of_mapM hm, hws]
  exact ⟨_, some (.vals us), rfl, hup.symm⟩

/-- **A segmented run of the importer with nested calls is a play of the importer's instance**:
from shared and part threads satisfying `LInv`, every `LSeg` ends where `LInv` holds again; its
nested calls are rounds of `Ii` (import questions answered with the lowered results), related by
`ImpRel` to component import calls answered by returned calls of the exporter (`ExpSeg`) from
`π`; and the rounds are a path of `Ii` before any continuation from the part's end. -/
theorem lseg_path (S : LStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)} {recs : List (LRec P)}
    {z : CoreSt (E3 P)} (hseg : LSeg B y recs z) :
    ∀ {x : Store Nat × Silmaril.Wasm.SingleThreaded.Thread} {π : Store Nat},
      LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π →
      ∃ (z' : Store Nat × Silmaril.Wasm.SingleThreaded.Thread) (π' : Store Nat)
        (rounds : List (Round Ii.E))
        (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))),
        LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f z z' π' ∧ List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) rounds dss ∧
        ExpSeg P l Ie π dss.flatten π' ∧
        ∀ (rest : List (Silmaril.Games.Move Ii.E Ii.F)) (q : Ii.HState),
          (∀ s t, Silmaril.Wasm.Game.Reach P (s, t) z' → Ii.Path P (.running f s t) rest q) →
          Ii.Path P (.running f x.1 x.2) (callMoves rounds ++ rest) q := by
  induction hseg with
  | done hy =>
    intro x π hI
    obtain ⟨x', hI', hr⟩ := hI.reach S hy
    exact ⟨x', π, [], [], hI', .nil, .nil π, fun rest q hk => hk x.1 x.2 hr⟩
  | @call x₀ y₁ ev z₁ fid a p ys zs ws us rest₁ hy hs hf hr hws he hst hus _ ih =>
    show ∀ {x : Store Nat × Silmaril.Wasm.SingleThreaded.Thread} {π : Store Nat},
      LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f x₀ x π → _
    intro x π hI
    obtain ⟨x₁, hI₁, hr₁⟩ := hI.reach S hy
    obtain ⟨k, nm, p', w, xe, E, a', args, e, heq, hk, hw, hxe, hpx, hdx, hm, he', -⟩ :=
      hI₁.callout S hs
    have hfk : fid = l.wireFid k ∧ witFt p = witFt p' := by
      have h' := heq
      simp only [CanonHost.lowered.injEq] at h'
      exact ⟨h'.1, h'.2.1⟩
    have hmi : (nm, p') ∈ l.imp.imports := List.mem_of_getElem? hk
    have hpp : p = xe.ty := (witFt_inj hfk.2 hr (S.arity.2 _ hmi).2.2).trans hpx.symm
    have hfl : ArenaField.funcs.get? B.store fid =
        some (.lifted (Ie.addrs.getD xe.core 0) (witFt xe.ty) {} ⟨1⟩) :=
      hfk.1 ▸ S.lifted k w xe hw hxe
    have ha : a = Ie.addrs.getD xe.core 0 := by
      injection Option.some.inj (hf.symm.trans hfl)
    have hk₂ : l.imp.imports[k]? = some (nm, xe.ty) := hpx ▸ hk
    have he₂ : Relation.ReflTransGen (CoreStep (E3 P))
        (y₁.1, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD xe.core 0)
          (lowerArgs xe.ty.params ws)) ev := ha ▸ hpp ▸ he
    obtain ⟨π₁, hI₂, hRet⟩ :=
      hI₁.resume S hk₂ hxe hdx he' (hpp ▸ hws) he₂ hst (hpp ▸ hus)
    obtain ⟨z', π', rounds, dss, hIz, hrel, hexp, hpath⟩ := ih (hpp ▸ hI₂)
    have hek : e.1.val = k ∧ e.2.1 = args := ifaceOp?_some he'
    have hcheck : ValTy.checkList xe.ty.results us = true :=
      Silmaril.Wasm.Component.checkList_of_liftArgs (hpp ▸ hus)
    have hwl : w < l.exp.exports.length := (List.getElem?_eq_some_iff.mp hxe).1
    have hxw : l.exp.exports[(⟨w, hwl⟩ : Fin l.exp.exports.length)] = xe :=
      (List.getElem?_eq_some_iff.mp hxe).2
    have hrel₁ := impRel_link hk₂ hek.1 hek.2 hm (hpp ▸ hws) hcheck
      (.values ⟨_, resAnswer S hk₂ hek.1 hcheck⟩) rfl
    have hw' : l.wire[e.1.val]? = some w := hek.1 ▸ hw
    refine ⟨z', π', _ :: rounds, _ :: dss, hIz, .cons hrel₁ hrel,
      .ret ⟨w, hwl⟩ hw' (hxw ▸ hRet) hexp, ?_⟩
    intro rest q hk'
    have hco : Silmaril.Wasm.Game.CalloutAt x₁.1 x₁.2 k args := ⟨E, a', hdx⟩
    exact .cons (.ucall hr₁ hco he') (.cons (.uret _) (hpp ▸ hpath rest q hk'))

/-- **`LinkOk` from the invariant.** -/
theorem LInv.linkOk (S : LStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)}
    {x : Store Nat × Silmaril.Wasm.SingleThreaded.Thread} {π : Store Nat}
    (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π) : LinkOk B y := by
  intro recs z h ys hz hst
  obtain ⟨z', π', -, -, hIz, -⟩ := lseg_path S hz hI
  exact hIz.site S hst

end Path

end Silmaril.Proofs.Wasm.Component.Reference

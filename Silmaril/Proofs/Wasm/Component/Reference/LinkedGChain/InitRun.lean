module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.Run

/-!
# The nested instantiation of `LinkedG.toRef` as a live run, in any context

`instG_lrun` of `LinkedGInst` runs the instantiation of `lg.toRef` only from `initConfig`,
after the host's instantiation event, at the root instance `⟨0⟩` with no outer frames. R4 of a
linked component as an exporter (`RefData.InitUX`) runs it **nested**: the late-bound call
`Call.instantiate ⟨lg.toRef, outer⟩ []` from any configuration with an empty core store, in any
thread, under any outer frames, its instance the next one of the store.

* `clEGo`, `clIGo`, `scAo`, `scWo`, `scIo`: the closures and scopes of `LinkedGInit` under outer
  frames `outer` (`clEG P lg = clEGo P lg []`, …);
* `stageAo` … `toRefG_reacho`: the stages of `LinkedGInst.Run` at any instance `inst`, outer
  frames and thread;
* `ReachL.callL`: a late-bound call whose dispatched program reaches its result by a live run
  reaches it by a live run (`ReachL.call` for `ReachL` in place of `SRuns`);
* `instCallG_reach`: **the nested instantiation of `lg.toRef` is a live run**, to the
  importer's nested instantiation after R4's configuration (`FoldEndX`), observing nothing.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (FuncTy)

/-! ## A late-bound call by a live run -/

section Call

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {D : Call E → Canon.P E σ (Ret E)} {th : Option ThreadId}

/-- **A late-bound call reaches what its dispatched program reaches**, by a live run. -/
theorem ReachL.callL {c : Call E} {m : Machine.Config E σ}
    {Q : List HostObs → Ret E → Machine.Config E σ → Prop}
    (h : ReachL prof hr D th (D c) m Q) :
    ReachL prof hr D th (callRet c : Canon.P E σ (Ret E)) m Q := by
  intro hl f segs rest
  obtain ⟨tr, a, m', d₁, hh, ht, hl', hq⟩ :=
    h hl Prog.pure (.prog (fun r => Prog.pure r >>= f) :: segs) rest
  rw [Prog.bind_eq, Prog.bind_pure] at d₁
  have s₁ : UniqueStep prof hr D
      { m with ctl := ⟨th, .prog (.op (S := Eff E σ) (.call c) fun r => Prog.pure r >>= f),
        segs⟩ :: rest }
      .tau { m with ctl := ⟨th, .prog (D c), .prog (fun r => Prog.pure r >>= f) :: segs⟩ ::
        rest } :=
    .of_prog rfl (fun _ _ e => by cases e) (.call (k := fun r => Prog.pure r >>= f) rfl)
  have s₂ : UniqueStep prof hr D
      { m' with ctl := ⟨th, .prog (Prog.pure a), .prog (fun r => Prog.pure r >>= f) :: segs⟩ ::
        rest }
      .tau { m' with ctl := ⟨th, .prog (Prog.pure a >>= f), segs⟩ :: rest } :=
    .of_prog rfl (fun _ _ e => by cases e) (.popProg (k := fun r => Prog.pure r >>= f) (r := a) rfl)
  have hrun : LRun prof hr D
      { m with ctl := ⟨th, .prog ((callRet c : Canon.P E σ (Ret E)) >>= f), segs⟩ :: rest }
      (.tau :: (tr ++ [.tau])) { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } :=
    .cons (RunsQ.live_op hl) s₁ (d₁.trans (.cons (RunsQ.live_op hl') s₂ (.refl _)))
  have e : traceObs (.tau :: (tr ++ [.tau]) : List (Label E σ)) = traceObs tr := by
    show (Label.tau :: (tr ++ [Label.tau])).filterMap Label.obs? = tr.filterMap Label.obs?
    rw [List.filterMap_cons_none rfl, List.filterMap_append, List.filterMap_cons_none rfl,
      List.filterMap_nil, List.append_nil]
  refine ⟨.tau :: (tr ++ [.tau]), a, m', hrun, ?_, ?_, hl', e ▸ hq⟩
  · intro ev hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hh ev hm
    · simp at hm
  · intro r hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ht r hm
    · simp at hm

end Call

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (core3P P) σ}

/-! ## Closures and scopes under outer frames -/

variable (P) in
/-- The exporter's closure in the parent, under the parent's outer frames `outer`. -/
def clEGo (lg : LinkedG) (outer : List (Frame (core3P P))) : Closure (core3P P) :=
  ⟨lg.exp.ref, Frame.empty :: outer⟩

variable (P) in
/-- The importer's closure in the parent, under the parent's outer frames `outer`. -/
def clIGo (lg : LinkedG) (outer : List (Frame (core3P P))) : Closure (core3P P) :=
  ⟨lg.imp.toRef, { (Frame.empty : Frame (core3P P)) with components := [clEGo P lg outer] } ::
    outer⟩

variable (P) in
/-- `scA` under outer frames. -/
def scAo (lg : LinkedG) (outer : List (Frame (core3P P)))
    (es : List (String × ItemVal (core3P P))) : Scope (core3P P) :=
  { frame := { Frame.empty with
      components := [clEGo P lg outer, clIGo P lg outer]
      instances := [es] } }

/-- `scW` under outer frames. -/
def scWo {lg : LinkedG} (d : lg.exp.RefData P) (pl : d.Pl) (outer : List (Frame (core3P P)))
    (es : List (String × ItemVal (core3P P))) : Scope (core3P P) :=
  { scAo P lg outer es with frame := { (scAo P lg outer es).frame with
      funcs := (scAo P lg outer es).frame.funcs ++ lg.wire.map fun w => (⟨d.fid pl w⟩ : FuncId) } }

/-- `scI` under outer frames. -/
def scIo {lg : LinkedG} (d : lg.exp.RefData P) (pl : d.Pl) (outer : List (Frame (core3P P)))
    (es esI : List (String × ItemVal (core3P P))) : Scope (core3P P) :=
  { scWo d pl outer es with frame := { (scWo d pl outer es).frame with
      instances := (scWo d pl outer es).frame.instances ++ [esI] } }

variable {lg : LinkedG} {d : lg.exp.RefData P}

/-- **`FoldEndU` with the parent's exports exactly**: export `i` of the importer at function
`m₁.store.funcs.length + i`. -/
def FoldEndX (d : lg.exp.RefData P) (Ii : Silmaril.Wasm.Game.ScalarInstance)
    (cfg : Machine.Config (core3P P) σ) (xs : Exports (core3P P)) (m : Machine.Config (core3P P) σ) :
    Prop :=
  ∃ (m₁ : Machine.Config (core3P P) σ) (pl : d.Pl) (F : CoreFoot)
    (es : List (String × ItemVal (core3P P))) (r : Store (CanonHost (core3P P) × Nat)),
    InitW d pl F es cfg m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
    TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
    xs = lg.imp.exports.mapIdx (fun i x => (x.name, ItemVal.func ⟨m₁.store.funcs.length + i⟩)) ∧
    m = impCfg lg Ii m₁ r

/-! ## The stages at any instance, outer frames and thread -/

section Stages

variable (inst : InstId) (outer : List (Frame (core3P P))) (th : Option ThreadId)

/-- The closures and the exporter's nested instantiation (R4). -/
theorem stageAo (hInit : d.InitUX) (cfg : Machine.Config (core3P P) σ)
    (hcore : cfg.core = (core3P P).empty _) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch th
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) inst outer []) {}
        ([.component lg.exp.ref, .component lg.imp.toRef, .instance_ (.instantiate 0 [])] :
          Core3Component))
      cfg (fun os sc m => os = [] ∧ ∃ pl F es, InitW d pl F es cfg m ∧ sc = scAo P lg outer es) := by
  let sc₁ : Scope (core3P P) := { frame := { Frame.empty with components := [clEGo P lg outer] } }
  let sc₂ : Scope (core3P P) :=
    { frame := { Frame.empty with components := [clEGo P lg outer, clIGo P lg outer] } }
  have r₁ : instantiateDef (callRecurse : Recurse (core3P P) σ) inst outer [] {}
      (.component lg.exp.ref) = Pure.pure sc₁ := instDef_component _ _
  have r₂ : instantiateDef (callRecurse : Recurse (core3P P) σ) inst outer [] sc₁
      (.component lg.imp.toRef) = Pure.pure sc₂ := instDef_component _ _
  have r₃ := instDef_instantiate (σ := σ) sc₂ (inst := inst) (outer := outer) (args := [])
    (c := 0) (iargs := []) (cl := clEGo P lg outer) (vs := []) rfl rfl
  refine ReachL.foldlM_cons (ReachL.of_eq r₁ (ReachL.pure sc₁ cfg)) fun os s m' h => ?_
  obtain ⟨rfl, rfl, e⟩ := h
  subst m'
  refine ReachL.foldlM_cons (ReachL.of_eq r₂ (ReachL.pure sc₂ _)) fun os s m' h => ?_
  obtain ⟨rfl, rfl, e⟩ := h
  subst m'
  refine ReachL.foldlM_cons (Q := fun os sc m => os = [] ∧ ∃ pl F es, InitW d pl F es cfg m ∧
    sc = scAo P lg outer es) ?_ fun os s m' h => ReachL.foldlM_nil ?_
  · refine ReachL.of_eq r₃ ?_
    refine ReachL.bind (ReachL.callItems (R := fun os es m => os = [] ∧ ∃ pl F,
        InitW d pl F es cfg m) (reach_initU hInit th (Frame.empty :: outer) cfg hcore)
        fun os r m ⟨ho, pl, F, es, hr, hA⟩ => ⟨es, hr, ho, pl, F, hA⟩)
      fun os es m ⟨ho, pl, F, hA⟩ => ReachL.pure_of ?_
    subst ho
    exact ⟨rfl, pl, F, es, hA, rfl⟩
  · obtain ⟨ho, h⟩ := h
    subst ho
    exact ⟨rfl, h⟩

/-- The aliases of the wired exports. -/
theorem stageWo (hW : lg.WireTy) {cfg m : Machine.Config (core3P P) σ} {pl : d.Pl} {F : CoreFoot}
    {es : List (String × ItemVal (core3P P))} (hA : InitW d pl F es cfg m) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch th
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) inst outer [])
        (scAo P lg outer es)
        (lg.wire.map fun w => (.alias (.export_ 0 (lg.expName w) .func) :
          Syntax.Definition Silmaril.Wasm.Module)))
      m (fun os sc m' => os = [] ∧ sc = scWo d pl outer es ∧ m' = m) := by
  have hFA : List.Forall₂ (fun n f => lookupExport? es n = some (.func f))
      (lg.wire.map lg.expName) (lg.wire.map fun w => (⟨d.fid pl w⟩ : FuncId)) := by
    refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun w hw => ?_))
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hw
    obtain ⟨x, hx, -⟩ := hW.ty k w hk
    have hn : lg.expName w = x.name := by simp [LinkedG.expName, hx]
    rw [hn]
    exact (hA.exports w x hx).1
  have h := aliases_run (σ := σ) (R := (callRecurse : Recurse (core3P P) σ)) (inst := inst)
    (outer := outer) (args := []) (i := 0) hFA (scAo P lg outer es) m rfl
  rw [List.map_map] at h
  exact (ReachL.ofTRuns h).mono fun _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩

/-- **The importer's nested instantiation** over the shared store after R4's configuration `m`,
import `k` bound to the exporter's function `fidG d pl k`. -/
theorem stageIo (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    {cfg m : Machine.Config (core3P P) σ} {pl : d.Pl} {F : CoreFoot}
    {es : List (String × ItemVal (core3P P))} (hA : InitW d pl F es cfg m) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch th
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) inst outer [])
        (scWo d pl outer es)
        ([.instance_ (.instantiate 1 (lg.imp.imports.mapIdx fun k p => (p.1, ⟨.func, k⟩)))] :
          Core3Component))
      m (fun os sc m' => os = [] ∧ ∃ (esI : List (String × ItemVal (core3P P)))
        (r : Store (CanonHost (core3P P) × Nat)), Store.mapH Prod.snd r = Ii.store ∧
        TrampsOf lg (fidG d pl) (nextInst m.store) r ∧
        funcExports esI = lg.imp.exports.mapIdx (fun i x => (x.name, ⟨m.store.funcs.length + i⟩)) ∧
        TagOrFunc esI ∧ sc = scIo d pl outer es esI ∧
        m' = impCfg lg Ii m r) := by
  have hlen : lg.wire.length = lg.imp.imports.length := hW.length
  obtain ⟨r, ci, hrs, hh, hF⟩ := coreFactsL_of_inst (Pf := P) hIg hIi hseg hI m.core
    (nextInst m.store) (fidG d pl)
  have hv : ((lg.imp.imports.mapIdx fun k p =>
      (p.1, (⟨.func, k⟩ : Syntax.SortIdx Syntax.Sort_)))).mapM
      (fun x => (x.1, ·) <$> itemAt? (scWo d pl outer es).frame x.2) =
        some (linkArgsG P lg (fidG d pl)) := by
    refine mapM_eq_some_of_getElem (by simp [linkArgsG]) fun i hi => ?_
    have hi' : i < lg.imp.imports.length := by simpa using hi
    have hiw : i < lg.wire.length := hlen ▸ hi'
    simp only [scWo, scAo, Frame.empty, List.nil_append, List.getElem_mapIdx, linkArgsG, itemAt?,
      Frame.get?, Frame.func?, List.getElem?_map, List.getElem?_eq_getElem hiw, Option.map_some,
      Option.bind_some, Function.comp_apply, Entry.toItem?, fidG, getD_lt hiw]
    rfl
  have hb : ImportsBound lg.imp (linkArgsG P lg (fidG d pl)) (fidG d pl) m.store := by
    intro j hj
    have hjw : j < lg.wire.length := hlen ▸ hj
    obtain ⟨x, hx, hty⟩ := hW.ty j lg.wire[j] (List.getElem?_eq_getElem hjw)
    have hty' : lg.imp.imports[j].2 = x.ty := by
      simpa [List.getElem?_eq_getElem hj] using hty
    have hfid : fidG d pl j = ⟨d.fid pl lg.wire[j]⟩ := by
      show (⟨d.fid pl (lg.wire.getD j 0)⟩ : FuncId) = _
      rw [getD_lt hjw]
    obtain ⟨hl, -⟩ := hFr.lifted pl lg.exp.init m.ref F lg.wire[j] x hA.hold hx
    refine ⟨?_, _, by rw [hfid]; exact hl, ?_⟩
    · have h := lookup_mapIdx_val (·.1)
        (fun k => (ItemVal.func (fidG d pl k) : ItemVal (core3P P))) 0 lg.imp.imports j hj
        hIi.importNames
      simp only [Nat.zero_add] at h
      exact h
    · show witFt x.ty = witFt lg.imp.imports[j].2
      rw [hty']
  obtain ⟨esI, hxI, htI, hrI⟩ := instantiateCall_simpleI' (Pf := P) (σ := σ) hIg hIa
    ({ (Frame.empty : Frame (core3P P)) with components := [clEGo P lg outer] } :: outer)
    (linkArgsG P lg (fidG d pl)) m hF rfl rfl hb
  have r₅ := instDef_instantiate (σ := σ) (scWo d pl outer es) (inst := inst) (outer := outer)
    (args := []) (c := 1) (cl := clIGo P lg outer) rfl hv
  refine ReachL.foldlM_cons (Q := fun os sc m' => os = [] ∧ sc = scIo d pl outer es esI ∧
    m' = impCfg lg Ii m r) ?_ fun os s m' h => ReachL.foldlM_nil ?_
  · refine ReachL.of_eq r₅ ?_
    refine ReachL.bind (ReachL.callItems (R := fun os es' m' => os = [] ∧ es' = esI ∧
        m' = impCfg lg Ii m r) (ReachL.call hrI)
        fun os r' m' ⟨h₁, h₂, h₃⟩ => ⟨esI, h₂, h₁, rfl, h₃⟩)
      fun os es' m' ⟨h₁, h₂, h₃⟩ => ReachL.pure_of ?_
    subst h₁ h₂ h₃
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨h₁, h₂, h₃⟩ := h
    subst h₁ h₂ h₃
    exact ⟨rfl, esI, r, hrs, hh, hxI, htI, rfl, rfl⟩

/-- The aliases of the importer's exports. -/
theorem stageIAo (hIg : lg.imp.Good) (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {m : Machine.Config (core3P P) σ} {fb : Nat} {esI : List (String × ItemVal (core3P P))}
    (hxI : funcExports esI = lg.imp.exports.mapIdx (fun i x => (x.name, ⟨fb + i⟩)))
    (htI : TagOrFunc esI) (sc : Scope (core3P P)) (hsc : sc.frame.instance? 1 = some esI) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch th
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) inst outer []) sc
        (lg.imp.exports.map fun x => (.alias (.export_ 1 x.name .func) :
          Syntax.Definition Silmaril.Wasm.Module)))
      m (fun os sc' m' => os = [] ∧
        sc' = { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ LinkedGInst.fsI lg fb } } ∧
        m' = m) := by
  have hFB : List.Forall₂ (fun n f => lookupExport? esI n = some (.func f))
      (lg.imp.exports.map (·.name)) (LinkedGInst.fsI lg fb) := by
    refine List.forall₂_iff_get.2 ⟨by simp [LinkedGInst.fsI], fun i h₁ h₂ => ?_⟩
    have hi : i < lg.imp.exports.length := by simpa using h₁
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, LinkedGInst.fsI]
    exact lookup_funcExportL htI hxI hIg.names i hi (hNI _ (List.getElem_mem hi))
  have h := aliases_run (σ := σ) (R := (callRecurse : Recurse (core3P P) σ)) (inst := inst)
    (outer := outer) (args := []) (i := 1) hFB sc m hsc
  rw [List.map_map] at h
  exact (ReachL.ofTRuns h).mono fun _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩

/-- The exports of the parent. -/
theorem stageXo {m : Machine.Config (core3P P) σ} {fb : Nat} (sc : Scope (core3P P))
    (hsc : ∀ j < lg.imp.exports.length, sc.frame.funcs[lg.wire.length + j]? = some ⟨fb + j⟩) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch th
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) inst outer []) sc
        (lg.imp.exports.mapIdx fun i x => (.export_ { name := x.name } ⟨.func, lg.wire.length + i⟩
          none : Syntax.Definition Silmaril.Wasm.Module)))
      m (fun os sc' m' => os = [] ∧
        sc'.exports = sc.exports ++ lg.imp.exports.mapIdx (fun i x => (x.name, .func ⟨fb + i⟩)) ∧
        m' = m) := by
  obtain ⟨sc', h, hx⟩ := exportsP_run (σ := σ) (R := (callRecurse : Recurse (core3P P) σ))
    (inst := inst) (outer := outer) (args := []) lg.imp.exports lg.wire.length fb sc m hsc
  exact (ReachL.ofTRuns h).mono fun _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂ ▸ hx, h₃⟩

/-- **The definitions of `lg.toRef` run** at any instance, outer frames and thread, from a
configuration with an empty core store, to the importer's nested instantiation after R4's
configuration. -/
theorem toRefG_reacho (hInit : d.InitUX) (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    (cfg : Machine.Config (core3P P) σ) (hcore : cfg.core = (core3P P).empty _) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch th
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) inst outer []) {}
        lg.toRef)
      cfg (fun os sc m => os = [] ∧ FoldEndX d Ii cfg sc.exports m) := by
  refine ReachL.foldlM_append (Q := fun os sc m => os = [] ∧ ∃ (m₁ : Machine.Config (core3P P) σ)
      (pl : d.Pl) (F : CoreFoot) (es : List (String × ItemVal (core3P P)))
      (r : Store (CanonHost (core3P P) × Nat)),
      InitW d pl F es cfg m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
      TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
      (∀ j < lg.imp.exports.length,
        sc.frame.funcs[lg.wire.length + j]? = some ⟨m₁.store.funcs.length + j⟩) ∧
      sc.exports = [] ∧ m = impCfg lg Ii m₁ r) ?_ ?_
  · refine ReachL.foldlM_append (Q := fun os sc m => os = [] ∧ ∃ (m₁ : Machine.Config (core3P P) σ)
        (pl : d.Pl) (F : CoreFoot) (es esI : List (String × ItemVal (core3P P)))
        (r : Store (CanonHost (core3P P) × Nat)),
        InitW d pl F es cfg m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
        TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
        funcExports esI =
          lg.imp.exports.mapIdx (fun i x => (x.name, ⟨m₁.store.funcs.length + i⟩)) ∧
        TagOrFunc esI ∧ sc = scIo d pl outer es esI ∧
        m = impCfg lg Ii m₁ r) ?_ ?_
    · refine ReachL.foldlM_append (Q := fun os sc m => os = [] ∧ ∃ (pl : d.Pl) (F : CoreFoot)
          (es : List (String × ItemVal (core3P P))), InitW d pl F es cfg m ∧
          sc = scWo d pl outer es) ?_ ?_
      · refine ReachL.foldlM_append (stageAo inst outer th hInit cfg hcore) fun os sc m h => ?_
        obtain ⟨rfl, pl, F, es, hA, rfl⟩ := h
        exact (stageWo inst outer th hW hA).mono fun os' sc' m' ⟨h₁, h₂, h₃⟩ => by
          subst h₁ h₂ h₃
          exact ⟨rfl, pl, F, es, hA, rfl⟩
      · intro os sc m h
        obtain ⟨rfl, pl, F, es, hA, rfl⟩ := h
        exact (stageIo inst outer th hFr hW hIg hIi hIa hseg hI hA).mono
          fun os' sc' m' ⟨h₁, esI, r, hrs, hh, hxI, htI, h₂, h₃⟩ => by
            subst h₁ h₂ h₃
            exact ⟨rfl, m, pl, F, es, esI, r, hA, hrs, hh, hxI, htI, rfl, rfl⟩
    · intro os sc m h
      obtain ⟨rfl, m₁, pl, F, es, esI, r, hA, hrs, hh, hxI, htI, rfl, rfl⟩ := h
      exact (stageIAo inst outer th hIg hNI hxI htI (scIo d pl outer es esI) rfl).mono
        fun os' sc' m' ⟨h₁, h₂, h₃⟩ => by
          subst h₁ h₂ h₃
          refine ⟨rfl, m₁, pl, F, es, r, hA, hrs, hh, fun j hj => ?_, rfl, rfl⟩
          have hl : (scIo d pl outer es esI).frame.funcs.length = lg.wire.length := by
            simp [scIo, scWo, scAo, Frame.empty]
          show ((scIo d pl outer es esI).frame.funcs ++ LinkedGInst.fsI lg m₁.store.funcs.length)[
            lg.wire.length + j]? = _
          rw [List.getElem?_append_right (by omega), hl, Nat.add_sub_cancel_left]
          simp [LinkedGInst.fsI, hj]
  · intro os sc m h
    obtain ⟨rfl, m₁, pl, F, es, r, hA, hrs, hh, hf, hx, rfl⟩ := h
    exact (stageXo inst outer th sc hf).mono fun os' sc' m' ⟨h₁, h₂, h₃⟩ => by
      subst h₁ h₃
      refine ⟨rfl, m₁, pl, F, es, r, hA, hrs, hh, ?_, rfl⟩
      rw [h₂, hx, List.nil_append]

end Stages

/-- **The nested instantiation of `lg.toRef` is a live run**, from any configuration with an
empty core store, in any thread and under any outer frames: its instance is allocated, then its
definitions run (`toRefG_reacho`) to the importer's nested instantiation after R4's
configuration, observing nothing; it answers the parent's exports. -/
theorem instCallG_reach (hInit : d.InitUX) (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    (th : Option ThreadId) (outer : List (Frame (core3P P)))
    (M : Machine.Config (core3P P) σ) (hcore : M.core = (core3P P).empty _) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch th
      (callRet (.instantiate ⟨lg.toRef, outer⟩ []) : Canon.P (core3P P) σ (Ret (core3P P))) M
      (fun os r m => os = [] ∧ ∃ xs, r = .items xs ∧
        FoldEndX d Ii { M with store := ArenaOps.allocSt ArenaField.insts {} M.store } xs m) := by
  refine ReachL.callL ?_
  show ReachL prof (linkHost impl).hr (linkHost impl).dispatch th
    (instantiateCallProg ⟨lg.toRef, outer⟩ [] : Canon.P (core3P P) σ (Ret (core3P P))) M _
  unfold instantiateCallProg instantiateClosure instantiateComponent
  refine ReachL.bind (Q := fun os xs m => os = [] ∧
      FoldEndX d Ii { M with store := ArenaOps.allocSt ArenaField.insts {} M.store } xs m)
    ?_ fun os xs m h => ReachL.pure_of ?_
  · refine ReachL.bind_eq (ReachL.ofTRuns (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} M))
      ?_
    refine ReachL.bind (toRefG_reacho _ outer th hInit hFr hW hIg hIi hIa hseg hNI hI _ hcore)
      fun os sc m h => ReachL.pure_of ?_
    obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, h⟩
  · obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, xs, rfl, h⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain

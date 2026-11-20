module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.ReachL
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Run

/-!
# The instantiation of `LinkedG.toRef` as a live run

`instG_run` of `LinkedGInit` with R4 read back (`RefData.InitU`): every stage of the parent's
instantiation (the closures, R4, the aliases of the wired exports, the importer's nested
instantiation, the aliases of its exports and the exports) is a `ReachL`, a live run of unique
steps, so the instantiation of `lg.toRef` after its host event is one live run to `afterG`:

* `stageAU` … `instProgG_reachU`: the stages of `LinkedGInit.Run` as `ReachL`s, R4's end
  keeping the waiting threads (`InitW`);
* `instG_lrun`: the instantiation of `lg.toRef` after its host event is an `LRun` to `afterG`,
  observing the root instance `0` and the export map `exportMapG`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (FuncTy)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (core3P P) σ}

/-- **What the parent's definitions reach** (`FoldEnd` of `LinkedGInit`), R4's end keeping the
waiting threads. -/
def FoldEndU {lg : LinkedG} (d : lg.exp.RefData P) (Ii : Silmaril.Wasm.Game.ScalarInstance)
    (cfg : Machine.Config (core3P P) σ) (xs : Exports (core3P P)) (m : Machine.Config (core3P P) σ) :
    Prop :=
  ∃ (m₁ : Machine.Config (core3P P) σ) (pl : d.Pl) (F : CoreFoot)
    (es : List (String × ItemVal (core3P P))) (r : Store (CanonHost (core3P P) × Nat)),
    InitW d pl F es cfg m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
    TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
    funcExports xs = exportMapG lg m₁.store.funcs.length ∧
    m = impCfg lg Ii m₁ r

variable {lg : LinkedG} {d : lg.exp.RefData P}

/-- The closures and the exporter's nested instantiation (R4). -/
theorem stageAU (hInit : d.InitUX) (cfg : Machine.Config (core3P P) σ)
    (hcore : cfg.core = (core3P P).empty _) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch none
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] []) {}
        ([.component lg.exp.ref, .component lg.imp.toRef, .instance_ (.instantiate 0 [])] :
          Core3Component))
      cfg (fun os sc m => os = [] ∧ ∃ pl F es, InitW d pl F es cfg m ∧ sc = scA P lg es) := by
  let sc₁ : Scope (core3P P) := { frame := { Frame.empty with components := [clEG P lg] } }
  let sc₂ : Scope (core3P P) :=
    { frame := { Frame.empty with components := [clEG P lg, clIG P lg] } }
  have r₁ : instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] [] {}
      (.component lg.exp.ref) = Pure.pure sc₁ := instDef_component _ _
  have r₂ : instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] [] sc₁
      (.component lg.imp.toRef) = Pure.pure sc₂ := instDef_component _ _
  have r₃ := instDef_instantiate (σ := σ) sc₂ (inst := ⟨0⟩) (outer := []) (args := [])
    (c := 0) (iargs := []) (cl := clEG P lg) (vs := []) rfl rfl
  refine ReachL.foldlM_cons (ReachL.of_eq r₁ (ReachL.pure sc₁ cfg)) fun os s m' h => ?_
  obtain ⟨rfl, rfl, e⟩ := h
  subst m'
  refine ReachL.foldlM_cons (ReachL.of_eq r₂ (ReachL.pure sc₂ _)) fun os s m' h => ?_
  obtain ⟨rfl, rfl, e⟩ := h
  subst m'
  refine ReachL.foldlM_cons (Q := fun os sc m => os = [] ∧ ∃ pl F es, InitW d pl F es cfg m ∧
    sc = scA P lg es) ?_ fun os s m' h => ReachL.foldlM_nil ?_
  · refine ReachL.of_eq r₃ ?_
    refine ReachL.bind (ReachL.callItems (R := fun os es m => os = [] ∧ ∃ pl F,
        InitW d pl F es cfg m) (reach_initU hInit none [Frame.empty] cfg hcore)
        fun os r m ⟨ho, pl, F, es, hr, hA⟩ => ⟨es, hr, ho, pl, F, hA⟩)
      fun os es m ⟨ho, pl, F, hA⟩ => ReachL.pure_of ?_
    subst ho
    exact ⟨rfl, pl, F, es, hA, rfl⟩
  · obtain ⟨ho, h⟩ := h
    subst ho
    exact ⟨rfl, h⟩

/-- The aliases of the wired exports. -/
theorem stageWU (hW : lg.WireTy) {cfg m : Machine.Config (core3P P) σ} {pl : d.Pl} {F : CoreFoot}
    {es : List (String × ItemVal (core3P P))} (hA : InitW d pl F es cfg m) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch none
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] []) (scA P lg es)
        (lg.wire.map fun w => (.alias (.export_ 0 (lg.expName w) .func) :
          Syntax.Definition Silmaril.Wasm.Module)))
      m (fun os sc m' => os = [] ∧ sc = scW d pl es ∧ m' = m) := by
  have hFA : List.Forall₂ (fun n f => lookupExport? es n = some (.func f))
      (lg.wire.map lg.expName) (lg.wire.map fun w => (⟨d.fid pl w⟩ : FuncId)) := by
    refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun w hw => ?_))
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hw
    obtain ⟨x, hx, -⟩ := hW.ty k w hk
    have hn : lg.expName w = x.name := by simp [LinkedG.expName, hx]
    rw [hn]
    exact (hA.exports w x hx).1
  have h := aliases_run (σ := σ) (R := (callRecurse : Recurse (core3P P) σ)) (inst := ⟨0⟩)
    (outer := []) (args := []) (i := 0) hFA (scA P lg es) m rfl
  rw [List.map_map] at h
  exact (ReachL.ofTRuns h).mono fun _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩

/-- **The importer's nested instantiation** over the shared store after R4's configuration `m`,
import `k` bound to the exporter's function `fidG d pl k`. -/
theorem stageIU (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    {cfg m : Machine.Config (core3P P) σ} {pl : d.Pl} {F : CoreFoot}
    {es : List (String × ItemVal (core3P P))} (hA : InitW d pl F es cfg m) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch none
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] []) (scW d pl es)
        ([.instance_ (.instantiate 1 (lg.imp.imports.mapIdx fun k p => (p.1, ⟨.func, k⟩)))] :
          Core3Component))
      m (fun os sc m' => os = [] ∧ ∃ (esI : List (String × ItemVal (core3P P)))
        (r : Store (CanonHost (core3P P) × Nat)), Store.mapH Prod.snd r = Ii.store ∧
        TrampsOf lg (fidG d pl) (nextInst m.store) r ∧
        funcExports esI = lg.imp.exports.mapIdx (fun i x => (x.name, ⟨m.store.funcs.length + i⟩)) ∧
        TagOrFunc esI ∧ sc = scI d pl es esI ∧ m' = impCfg lg Ii m r) := by
  have hlen : lg.wire.length = lg.imp.imports.length := hW.length
  obtain ⟨r, ci, hrs, hh, hF⟩ := coreFactsL_of_inst (Pf := P) hIg hIi hseg hI m.core
    (nextInst m.store) (fidG d pl)
  have hv : ((lg.imp.imports.mapIdx fun k p =>
      (p.1, (⟨.func, k⟩ : Syntax.SortIdx Syntax.Sort_)))).mapM
      (fun x => (x.1, ·) <$> itemAt? (scW d pl es).frame x.2) =
        some (linkArgsG P lg (fidG d pl)) := by
    refine mapM_eq_some_of_getElem (by simp [linkArgsG]) fun i hi => ?_
    have hi' : i < lg.imp.imports.length := by simpa using hi
    have hiw : i < lg.wire.length := hlen ▸ hi'
    simp only [scW, scA, Frame.empty, List.nil_append, List.getElem_mapIdx, linkArgsG, itemAt?,
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
    [{ (Frame.empty : Frame (core3P P)) with components := [clEG P lg] }]
    (linkArgsG P lg (fidG d pl)) m hF rfl rfl hb
  have r₅ := instDef_instantiate (σ := σ) (scW d pl es) (inst := ⟨0⟩) (outer := []) (args := [])
    (c := 1) (cl := clIG P lg) rfl hv
  refine ReachL.foldlM_cons (Q := fun os sc m' => os = [] ∧ sc = scI d pl es esI ∧
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

/-- The importer's lifted functions, from export `0` at function `fb`. -/
def fsI (lg : LinkedG) (fb : Nat) : List FuncId :=
  (List.range lg.imp.exports.length).map fun i => ⟨fb + i⟩

/-- The aliases of the importer's exports. -/
theorem stageIAU (hIg : lg.imp.Good) (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {m : Machine.Config (core3P P) σ} {fb : Nat} {esI : List (String × ItemVal (core3P P))}
    (hxI : funcExports esI = lg.imp.exports.mapIdx (fun i x => (x.name, ⟨fb + i⟩)))
    (htI : TagOrFunc esI) (sc : Scope (core3P P)) (hsc : sc.frame.instance? 1 = some esI) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch none
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] []) sc
        (lg.imp.exports.map fun x => (.alias (.export_ 1 x.name .func) :
          Syntax.Definition Silmaril.Wasm.Module)))
      m (fun os sc' m' => os = [] ∧
        sc' = { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ fsI lg fb } } ∧
        m' = m) := by
  have hFB : List.Forall₂ (fun n f => lookupExport? esI n = some (.func f))
      (lg.imp.exports.map (·.name)) (fsI lg fb) := by
    refine List.forall₂_iff_get.2 ⟨by simp [fsI], fun i h₁ h₂ => ?_⟩
    have hi : i < lg.imp.exports.length := by simpa using h₁
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, fsI]
    exact lookup_funcExportL htI hxI hIg.names i hi (hNI _ (List.getElem_mem hi))
  have h := aliases_run (σ := σ) (R := (callRecurse : Recurse (core3P P) σ)) (inst := ⟨0⟩)
    (outer := []) (args := []) (i := 1) hFB sc m hsc
  rw [List.map_map] at h
  exact (ReachL.ofTRuns h).mono fun _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩

/-- The exports of the parent. -/
theorem stageXU {m : Machine.Config (core3P P) σ} {fb : Nat} (sc : Scope (core3P P))
    (hsc : ∀ j < lg.imp.exports.length, sc.frame.funcs[lg.wire.length + j]? = some ⟨fb + j⟩) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch none
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] []) sc
        (lg.imp.exports.mapIdx fun i x => (.export_ { name := x.name } ⟨.func, lg.wire.length + i⟩
          none : Syntax.Definition Silmaril.Wasm.Module)))
      m (fun os sc' m' => os = [] ∧
        sc'.exports = sc.exports ++ lg.imp.exports.mapIdx (fun i x => (x.name, .func ⟨fb + i⟩)) ∧
        m' = m) := by
  obtain ⟨sc', h, hx⟩ := exportsP_run (σ := σ) (R := (callRecurse : Recurse (core3P P) σ))
    (inst := ⟨0⟩) (outer := []) (args := []) lg.imp.exports lg.wire.length fb sc m hsc
  exact (ReachL.ofTRuns h).mono fun _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂ ▸ hx, h₃⟩

/-- **The definitions of `lg.toRef` run** from a configuration with an empty core store, to the
importer's nested instantiation after R4's configuration. -/
theorem toRefG_reachU (hInit : d.InitUX) (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    (cfg : Machine.Config (core3P P) σ) (hcore : cfg.core = (core3P P).empty _) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch none
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] []) {} lg.toRef)
      cfg (fun os sc m => os = [] ∧ FoldEndU d Ii cfg sc.exports m) := by
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
        TagOrFunc esI ∧ sc = scI d pl es esI ∧
        m = impCfg lg Ii m₁ r) ?_ ?_
    · refine ReachL.foldlM_append (Q := fun os sc m => os = [] ∧ ∃ (pl : d.Pl) (F : CoreFoot)
          (es : List (String × ItemVal (core3P P))), InitW d pl F es cfg m ∧ sc = scW d pl es)
        ?_ ?_
      · refine ReachL.foldlM_append (stageAU hInit cfg hcore) fun os sc m h => ?_
        obtain ⟨rfl, pl, F, es, hA, rfl⟩ := h
        exact (stageWU hW hA).mono fun os' sc' m' ⟨h₁, h₂, h₃⟩ => by
          subst h₁ h₂ h₃
          exact ⟨rfl, pl, F, es, hA, rfl⟩
      · intro os sc m h
        obtain ⟨rfl, pl, F, es, hA, rfl⟩ := h
        exact (stageIU hFr hW hIg hIi hIa hseg hI hA).mono
          fun os' sc' m' ⟨h₁, esI, r, hrs, hh, hxI, htI, h₂, h₃⟩ => by
            subst h₁ h₂ h₃
            exact ⟨rfl, m, pl, F, es, esI, r, hA, hrs, hh, hxI, htI, rfl, rfl⟩
    · intro os sc m h
      obtain ⟨rfl, m₁, pl, F, es, esI, r, hA, hrs, hh, hxI, htI, rfl, rfl⟩ := h
      exact (stageIAU hIg hNI hxI htI (scI d pl es esI) rfl).mono
        fun os' sc' m' ⟨h₁, h₂, h₃⟩ => by
          subst h₁ h₂ h₃
          refine ⟨rfl, m₁, pl, F, es, r, hA, hrs, hh, fun j hj => ?_, rfl, rfl⟩
          have hl : (scI d pl es esI).frame.funcs.length = lg.wire.length := by
            simp [scI, scW, scA, Frame.empty]
          show ((scI d pl es esI).frame.funcs ++ fsI lg m₁.store.funcs.length)[
            lg.wire.length + j]? = _
          rw [List.getElem?_append_right (by omega), hl, Nat.add_sub_cancel_left]
          simp [fsI, hj]
  · intro os sc m h
    obtain ⟨rfl, m₁, pl, F, es, r, hA, hrs, hh, hf, hx, rfl⟩ := h
    exact (stageXU sc hf).mono fun os' sc' m' ⟨h₁, h₂, h₃⟩ => by
      subst h₁ h₃
      refine ⟨rfl, m₁, pl, F, es, r, hA, hrs, hh, ?_, rfl⟩
      rw [h₂, hx, List.nil_append]
      exact funcExports_mapIdx_func _ _


/-- **Root instantiation of `lg.toRef`** from a configuration with the empty core store and no
component instance: the root instance `0`, then the definitions (`toRefG_reachU`). -/
theorem rootG_reachU (hInit : d.InitUX) (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    (cfg : Machine.Config (core3P P) σ) (hcore : cfg.core = (core3P P).empty _)
    (hinsts : cfg.store.insts = []) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch none
      (instantiateRootCall lg.toRef [] : Canon.P (core3P P) σ (InstId × Exports (core3P P))) cfg
      (fun os p m => os = [] ∧ p.1 = ⟨0⟩ ∧
        FoldEndU d Ii { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } p.2 m) := by
  have hn := noImport_toRefG lg
  have hac : argsComplete lg.toRef ([] : Exports (core3P P)) = true := by
    rw [argsComplete, importNames_nil hn]
    rfl
  have hpre : ∀ s : CStore (core3P P), precheckImports s [] Frame.empty lg.toRef = .ok () :=
    fun s => precheckImports_ok s [] _ _ hn
  have hid : (ArenaField.insts (E := core3P P)).mkId (ArenaField.insts.size cfg.store) =
      (⟨0⟩ : InstId) := by
    simp only [ArenaField.size, ArenaField.insts, hinsts, List.length_nil]
  unfold instantiateRootCall instantiateRoot
  refine ReachL.bind_eq (ReachL.ofTRuns (trapIf_run ((congrArg (!·) hac).trans rfl) _ cfg)) ?_
  refine ReachL.bind_eq (ReachL.ofTRuns (TRuns.getStore cfg)) ?_
  refine ReachL.bind_eq (ReachL.ofTRuns (checkImport_run (hpre _) cfg)) ?_
  refine ReachL.bind_eq (ReachL.ofTRuns (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg)) ?_
  rw [hid]
  unfold instantiateComponent
  refine ReachL.bind (Q := fun os xs m => os = [] ∧
      FoldEndU d Ii { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } xs m)
    (ReachL.bind (toRefG_reachU hInit hFr hW hIg hIi hIa hseg hNI hI _ hcore)
      fun os sc m h => ReachL.pure_of ?_)
    fun os xs m h => ReachL.pure_of ?_
  · obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, h⟩
  · obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, rfl, h⟩


/-- **The instantiation program of `lg.toRef` reaches** the importer's nested instantiation after
R4's configuration, the nesting depth decremented, observing the root instance and the export
map. -/
theorem instProgG_reachU (hInit : d.InitUX) (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii) (h₀ : σ) :
    ReachL prof (linkHost impl).hr (linkHost impl).dispatch none
      (instantiateProg lg.toRef [] : Canon.P (core3P P) σ (Ret (core3P P)))
      (initConfig h₀)
      (fun os _ m => ∃ (m₁ : Machine.Config (core3P P) σ) (pl : d.Pl) (F : CoreFoot)
        (es : List (String × ItemVal (core3P P))) (r : Store (CanonHost (core3P P) × Nat)),
        InitW d pl F es (startG h₀) m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
        TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
        os = [instantiatedObs ⟨0⟩ (exportMapG lg m₁.store.funcs.length)] ∧
        m = { m₁ with
          store := DispatchSt.decNestingSt (impStore lg Ii m₁.store m₁.core r)
          core := impCore m₁.core r }) := by
  unfold instantiateProg
  refine ReachL.bind_eq (ReachL.ofTRuns
    (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) _)) ?_
  refine ReachL.bind (rootG_reachU hInit hFr hW hIg hIi hIa hseg hNI hI _ rfl rfl)
    fun os p m h => ?_
  obtain ⟨rfl, hp, m₁, pl, F, es, r, hA, hrs, hh, hx, rfl⟩ := h
  obtain ⟨inst, xs⟩ := p
  simp only at hp hx
  subst hp
  refine ReachL.bind_eq (ReachL.ofTRuns
    (TRuns.modifyStore (f := DispatchSt.decNestingSt) (fun _ => rfl) _)) ?_
  refine ReachL.bind (ReachL.ofSRuns
    (p := (emit (instantiatedObs ⟨0⟩ (funcExports xs)) : Canon.P (core3P P) σ Unit))
    (SRuns.emit (SRuns.pure () _))) fun os' u m' ⟨h₁, _, h₂⟩ => ReachL.pure_of ?_
  subst h₁ h₂
  refine ⟨m₁, pl, F, es, r, hA, hrs, hh, ?_, rfl⟩
  rw [hx]
  rfl


/-- The configuration after the instantiation host event of `lg.toRef`. -/
def instStartG (lg : LinkedG) (h₀ : σ) : Machine.Config (core3P P) σ :=
  { (initConfig h₀ : Machine.Config (core3P P) σ) with
    ctl := [.ofProg none (StepDefs.runProg (instantiateProg lg.toRef []))] }

/-- **The instantiation of `lg.toRef` after its host event is one live run** to `afterG`,
observing the root instance `0` and the export map. -/
theorem instG_lrun (hInit : d.InitUX) (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii) (h₀ : σ) :
    ∃ (tr : List (Label (core3P P) σ)) (m₁ : Machine.Config (core3P P) σ) (pl : d.Pl)
      (F : CoreFoot) (es : List (String × ItemVal (core3P P)))
      (r : Store (CanonHost (core3P P) × Nat)),
      InitW d pl F es (startG h₀) m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
      TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
      LRun prof (linkHost impl).hr (linkHost impl).dispatch (instStartG lg h₀) tr
        (afterG lg Ii m₁ r) ∧
      traceObs tr = [instantiatedObs ⟨0⟩ (exportMapG lg m₁.store.funcs.length)] := by
  obtain ⟨tr, a, m', hs, -, -, hl, m₁, pl, F, es, r, hA, hrs, htr, ho, rfl⟩ :=
    instProgG_reachU (prof := prof) (impl := impl) hInit hFr hW hIg hIi hIa hseg hNI hI h₀ rfl
      (fun _ => Pure.pure .unit) [] []
  have s₁ : UniqueStep prof (linkHost impl).hr (linkHost impl).dispatch
      { afterG lg Ii m₁ r with ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      (afterG lg Ii m₁ r) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  have hs' : LRun prof (linkHost impl).hr (linkHost impl).dispatch (instStartG lg h₀) tr
      { afterG lg Ii m₁ r with ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } := hs
  exact ⟨tr ++ [.tau], m₁, pl, F, es, r, hA, hrs, htr,
    hs'.trans (.cons ⟨List.cons_ne_nil _ _, hl⟩ s₁ (.refl _)),
    by rw [traceObs_append, ← ho]; exact List.append_nil _⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst

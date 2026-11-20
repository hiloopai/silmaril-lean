module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Reach
public import Silmaril.Proofs.Wasm.Component.Reference.InstLink
public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkCore
public import Silmaril.Wasm.Component.Reference.LinkedGInit.Defs

/-!
# The instantiation of `LinkedG.toRef` through an abstract exporter

`instL_lrun` of `Linked2` with the exporter abstracted to its R4 (`RefData.InitS`):

* `reach_initS`: R4 is a `Reach` of the late-bound call `Call.instantiate ⟨e.ref, outer⟩ []`;
* `toRefG_reach`: the definitions of `lg.toRef` (the closures, the exporter's nested
  instantiation by R4, the aliases of the wired exports, the importer's nested instantiation
  over the shared store after the exporter's, `instantiateCall_simpleI'` at the instance and
  function offsets R4 leaves, the aliases of the importer's exports and the exports) reach the
  store `impStore` of the importer's instantiation after R4's configuration;
* `instG_run`: the instantiation of `lg.toRef` as a host event from the initial configuration is
  a run without host events to `afterG`, observing the root instance `0` and the export map
  `exportMapG lg fb` (`fb` the component functions after the exporter's instantiation).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (FuncTy)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (core3P P) σ}

/-! ## R4 as a reach -/

/-- `InitAt` without its host-code fact. -/
theorem InitAt.toX {e : ExpSpec} {d : e.RefData P} {pl : d.Pl} {F : CoreFoot}
    {es : List (String × ItemVal (core3P P))} {M m : Machine.Config (core3P P) σ}
    (h : d.InitAt pl F es M m) : d.InitAtX pl F es M m :=
  ⟨h.lock, h.ext, h.hold, h.block, h.exports, h.pending, h.results, h.nest, h.globals, h.fidInj⟩

/-- **`InitS` implies `InitSX`.** -/
theorem initS_initSX {e : ExpSpec} {d : e.RefData P} (h : d.InitS) : d.InitSX := by
  intro σ prof impl M th outer k segs rest hcore hlock
  obtain ⟨tr, m, pl, F, es, hs, hh, ht, ho, hc, hA⟩ :=
    h prof impl M th outer k segs rest hcore hlock
  exact ⟨tr, m, pl, F, es, hs, hh, ht, ho, hc, InitAt.toX hA⟩

/-- **R4 reaches the exporter's exports**, in any context. -/
theorem reach_initS {e : ExpSpec} {d : e.RefData P} (hI : d.InitSX) (th : Option ThreadId)
    (outer : List (Frame (core3P P))) (M : Machine.Config (core3P P) σ)
    (hcore : M.core = (core3P P).empty _) :
    Reach prof (linkHost impl).hr (linkHost impl).dispatch th
      (callRet (.instantiate ⟨e.ref, outer⟩ []) : Canon.P (core3P P) σ (Ret (core3P P))) M
      (fun os r m => os = [] ∧ ∃ pl F es, r = .items es ∧ d.InitAtX pl F es M m) := by
  intro hl f segs rest
  obtain ⟨tr, m, pl, F, es, hs, hh, ht, ho, hc, hA⟩ := hI prof impl M th outer f segs rest hcore hl
  have hm : { m with ctl := ⟨th, .prog (f (.items es)), segs⟩ :: rest } = m := by rw [← hc]
  refine ⟨tr, .items es, m, ?_, hh, ht, hA.lock, ho, pl, F, es, rfl, hA⟩
  rw [hm]
  exact hs

theorem Reach.pure_of {E : CoreEngine} {hr : HostReady σ} {D : Call E → Canon.P E σ (Ret E)}
    {th : Option ThreadId} {α : Type} {a : α} {m : Machine.Config E σ}
    {R : List HostObs → α → Machine.Config E σ → Prop} (h : R [] a m) :
    Reach prof hr D th (Pure.pure a : Canon.P E σ α) m R :=
  (Reach.pure a m).mono fun _ _ _ ⟨e₁, e₂, e₃⟩ => by subst e₁ e₂ e₃; exact h

/-! ## The parent's definitions -/

section Fold

variable (P) in
/-- The exporter's closure in the parent. -/
def clEG (lg : LinkedG) : Closure (core3P P) := ⟨lg.exp.ref, [Frame.empty]⟩

variable (P) in
/-- The importer's closure in the parent. -/
def clIG (lg : LinkedG) : Closure (core3P P) :=
  ⟨lg.imp.toRef, [{ (Frame.empty : Frame (core3P P)) with components := [clEG P lg] }]⟩

/-- The function id of the export wired to import `k`. -/
def fidG {lg : LinkedG} (d : lg.exp.RefData P) (pl : d.Pl) (k : Nat) : FuncId :=
  ⟨d.fid pl (lg.wire.getD k 0)⟩

variable (P) in
/-- The instantiation arguments of the importer: import `k` bound to `fid k`. -/
def linkArgsG (lg : LinkedG) (fid : Nat → FuncId) : Exports (core3P P) :=
  lg.imp.imports.mapIdx fun k p => (p.1, .func (fid k))

/-- The function exports of the parent: export `i` of the importer is function `fb + i`. -/
def exportMapG (lg : LinkedG) (fb : Nat) : List (String × FuncId) :=
  lg.imp.exports.mapIdx fun i x => (x.name, ⟨fb + i⟩)

/-- The store after the importer's nested instantiation from the store `s` and the core store
`c` after the exporter's, the importer's core store `r` relocated after `c`. -/
def impStore (lg : LinkedG) (Ii : Silmaril.Wasm.Game.ScalarInstance) (s : CStore (core3P P))
    (c : Store (CanonHost (core3P P))) (r : Store (CanonHost (core3P P) × Nat)) :
    CStore (core3P P) :=
  nestStoreI (reloc c (Store.mapH Prod.fst r)) s (addrL c.funcs.length Ii) (nextInst s) lg.imp

/-- The core store after the importer's nested instantiation from the core store `c`: the
importer's core store `r` relocated after `c`. -/
def impCore (c : Store (CanonHost (core3P P))) (r : Store (CanonHost (core3P P) × Nat)) :
    Store (CanonHost (core3P P)) :=
  reloc c (Store.mapH Prod.fst r)

/-- The configuration after the importer's nested instantiation from `m` (`impStore`,
`impCore`). -/
def impCfg (lg : LinkedG) (Ii : Silmaril.Wasm.Game.ScalarInstance)
    (m : Machine.Config (core3P P) σ) (r : Store (CanonHost (core3P P) × Nat)) :
    Machine.Config (core3P P) σ :=
  { m with store := impStore lg Ii m.store m.core r, core := impCore m.core r }

/-- The host code of the importer's store `r`: trampoline `k` paired with `k`. -/
def TrampsOf (lg : LinkedG) (fid : Nat → FuncId) (inst : InstId)
    (r : Store (CanonHost (core3P P) × Nat)) : Prop :=
  HostsSat (fun h => ∃ (k : Nat) (hk : k < lg.imp.imports.length),
    h = (.lowered (fid k) (witFt lg.imp.imports[k].2) {} inst, k)) r

/-- **What the parent's definitions reach** from `cfg`: R4's configuration `m₁`, the importer's
store `r`, the export map, and the importer's nested instantiation after `m₁`. -/
def FoldEnd {lg : LinkedG} (d : lg.exp.RefData P) (Ii : Silmaril.Wasm.Game.ScalarInstance)
    (cfg : Machine.Config (core3P P) σ) (xs : Exports (core3P P)) (m : Machine.Config (core3P P) σ) :
    Prop :=
  ∃ (m₁ : Machine.Config (core3P P) σ) (pl : d.Pl) (F : CoreFoot)
    (es : List (String × ItemVal (core3P P))) (r : Store (CanonHost (core3P P) × Nat)),
    d.InitAtX pl F es cfg m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
    TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
    funcExports xs = exportMapG lg m₁.store.funcs.length ∧
    m = impCfg lg Ii m₁ r

/-! ### Folding definitions -/

section FoldLemmas

variable {E : CoreEngine} {hr : HostReady σ} {D : Call E → Canon.P E σ (Ret E)}
  {th : Option ThreadId} {α β : Type}

theorem Reach.of_eq {γ : Type} {p q : Canon.P E σ γ} {m : Machine.Config E σ}
    {Q : List HostObs → γ → Machine.Config E σ → Prop} (e : p = q)
    (h : Reach prof hr D th q m Q) : Reach prof hr D th p m Q := e ▸ h

theorem Reach.foldlM_append {g : β → α → Canon.P E σ β} {b : β} {l l' : List α}
    {m : Machine.Config E σ} {Q R : List HostObs → β → Machine.Config E σ → Prop}
    (h₁ : Reach prof hr D th (l.foldlM g b) m Q)
    (h₂ : ∀ os s m', Q os s m' →
      Reach prof hr D th (l'.foldlM g s) m' (fun os' b' m'' => R (os ++ os') b' m'')) :
    Reach prof hr D th ((l ++ l').foldlM g b) m R := by
  rw [List.foldlM_append]
  exact Reach.bind h₁ h₂

theorem Reach.foldlM_cons {g : β → α → Canon.P E σ β} {b : β} {x : α} {l : List α}
    {m : Machine.Config E σ} {Q R : List HostObs → β → Machine.Config E σ → Prop}
    (h₁ : Reach prof hr D th (g b x) m Q)
    (h₂ : ∀ os s m', Q os s m' →
      Reach prof hr D th (l.foldlM g s) m' (fun os' b' m'' => R (os ++ os') b' m'')) :
    Reach prof hr D th ((x :: l).foldlM g b) m R := by
  rw [List.foldlM_cons]
  exact Reach.bind h₁ h₂

theorem Reach.foldlM_nil {g : β → α → Canon.P E σ β} {b : β} {m : Machine.Config E σ}
    {R : List HostObs → β → Machine.Config E σ → Prop} (h : R [] b m) :
    Reach prof hr D th (([] : List α).foldlM g b) m R :=
  Reach.pure_of h

/-- **A silent run of definitions** reaches its scope. -/
theorem Reach.ofTRuns {γ : Type} {p : Canon.P E σ γ} {m m' : Machine.Config E σ} {a : γ}
    (h : TRuns p m a m') :
    Reach prof hr D th p m (fun os b m'' => os = [] ∧ b = a ∧ m'' = m') :=
  Reach.ofSRuns h

end FoldLemmas

variable (P) in
/-- The parent's scope after the exporter's nested instantiation (export map `es`). -/
def scA (lg : LinkedG) (es : List (String × ItemVal (core3P P))) : Scope (core3P P) :=
  { frame := { Frame.empty with components := [clEG P lg, clIG P lg], instances := [es] } }

/-- The parent's scope after the aliases of the wired exports. -/
def scW {lg : LinkedG} (d : lg.exp.RefData P) (pl : d.Pl)
    (es : List (String × ItemVal (core3P P))) : Scope (core3P P) :=
  { scA P lg es with frame := { (scA P lg es).frame with
      funcs := (scA P lg es).frame.funcs ++ lg.wire.map fun w => (⟨d.fid pl w⟩ : FuncId) } }

/-- The parent's scope after the importer's nested instantiation (export map `esI`). -/
def scI {lg : LinkedG} (d : lg.exp.RefData P) (pl : d.Pl)
    (es esI : List (String × ItemVal (core3P P))) : Scope (core3P P) :=
  { scW d pl es with frame := { (scW d pl es).frame with
      instances := (scW d pl es).frame.instances ++ [esI] } }

variable {lg : LinkedG} {d : lg.exp.RefData P}

/-- The closures and the exporter's nested instantiation (R4). -/
theorem stageA (hInit : d.InitSX) (cfg : Machine.Config (core3P P) σ)
    (hcore : cfg.core = (core3P P).empty _) :
    Reach prof (linkHost impl).hr (linkHost impl).dispatch none
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] []) {}
        ([.component lg.exp.ref, .component lg.imp.toRef, .instance_ (.instantiate 0 [])] :
          Core3Component))
      cfg (fun os sc m => os = [] ∧ ∃ pl F es, d.InitAtX pl F es cfg m ∧ sc = scA P lg es) := by
  let sc₁ : Scope (core3P P) := { frame := { Frame.empty with components := [clEG P lg] } }
  let sc₂ : Scope (core3P P) :=
    { frame := { Frame.empty with components := [clEG P lg, clIG P lg] } }
  have r₁ : instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] [] {}
      (.component lg.exp.ref) = Pure.pure sc₁ := instDef_component _ _
  have r₂ : instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] [] sc₁
      (.component lg.imp.toRef) = Pure.pure sc₂ := instDef_component _ _
  have r₃ := instDef_instantiate (σ := σ) sc₂ (inst := ⟨0⟩) (outer := []) (args := [])
    (c := 0) (iargs := []) (cl := clEG P lg) (vs := []) rfl rfl
  refine Reach.foldlM_cons (Reach.of_eq r₁ (Reach.pure sc₁ cfg)) fun os s m' h => ?_
  obtain ⟨rfl, rfl, e⟩ := h
  subst m'
  refine Reach.foldlM_cons (Reach.of_eq r₂ (Reach.pure sc₂ _)) fun os s m' h => ?_
  obtain ⟨rfl, rfl, e⟩ := h
  subst m'
  refine Reach.foldlM_cons (Q := fun os sc m => os = [] ∧ ∃ pl F es, d.InitAtX pl F es cfg m ∧
    sc = scA P lg es) ?_ fun os s m' h => Reach.foldlM_nil ?_
  · refine Reach.of_eq r₃ ?_
    refine Reach.bind (Reach.callItems (R := fun os es m => os = [] ∧ ∃ pl F,
        d.InitAtX pl F es cfg m) (reach_initS hInit none [Frame.empty] cfg hcore)
        fun os r m ⟨ho, pl, F, es, hr, hA⟩ => ⟨es, hr, ho, pl, F, hA⟩)
      fun os es m ⟨ho, pl, F, hA⟩ => Reach.pure_of ?_
    subst ho
    exact ⟨rfl, pl, F, es, hA, rfl⟩
  · obtain ⟨ho, h⟩ := h
    subst ho
    exact ⟨rfl, h⟩

/-- The aliases of the wired exports. -/
theorem stageW (hW : lg.WireTy) {cfg m : Machine.Config (core3P P) σ} {pl : d.Pl} {F : CoreFoot}
    {es : List (String × ItemVal (core3P P))} (hA : d.InitAtX pl F es cfg m) :
    Reach prof (linkHost impl).hr (linkHost impl).dispatch none
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
  exact (Reach.ofTRuns h).mono fun _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩

/-- **The importer's nested instantiation** over the shared store after R4's configuration `m`,
import `k` bound to the exporter's function `fidG d pl k`. -/
theorem stageI (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    {cfg m : Machine.Config (core3P P) σ} {pl : d.Pl} {F : CoreFoot}
    {es : List (String × ItemVal (core3P P))} (hA : d.InitAtX pl F es cfg m) :
    Reach prof (linkHost impl).hr (linkHost impl).dispatch none
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
  refine Reach.foldlM_cons (Q := fun os sc m' => os = [] ∧ sc = scI d pl es esI ∧
    m' = impCfg lg Ii m r) ?_ fun os s m' h => Reach.foldlM_nil ?_
  · refine Reach.of_eq r₅ ?_
    refine Reach.bind (Reach.callItems (R := fun os es' m' => os = [] ∧ es' = esI ∧
        m' = impCfg lg Ii m r) (Reach.call hrI)
        fun os r' m' ⟨h₁, h₂, h₃⟩ => ⟨esI, h₂, h₁, rfl, h₃⟩)
      fun os es' m' ⟨h₁, h₂, h₃⟩ => Reach.pure_of ?_
    subst h₁ h₂ h₃
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨h₁, h₂, h₃⟩ := h
    subst h₁ h₂ h₃
    exact ⟨rfl, esI, r, hrs, hh, hxI, htI, rfl, rfl⟩

/-- The importer's lifted functions, from export `0` at function `fb`. -/
def fsI (lg : LinkedG) (fb : Nat) : List FuncId :=
  (List.range lg.imp.exports.length).map fun i => ⟨fb + i⟩

/-- The aliases of the importer's exports. -/
theorem stageIA (hIg : lg.imp.Good) (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {m : Machine.Config (core3P P) σ} {fb : Nat} {esI : List (String × ItemVal (core3P P))}
    (hxI : funcExports esI = lg.imp.exports.mapIdx (fun i x => (x.name, ⟨fb + i⟩)))
    (htI : TagOrFunc esI) (sc : Scope (core3P P)) (hsc : sc.frame.instance? 1 = some esI) :
    Reach prof (linkHost impl).hr (linkHost impl).dispatch none
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
  exact (Reach.ofTRuns h).mono fun _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩

/-- The exports of the parent. -/
theorem stageX {m : Machine.Config (core3P P) σ} {fb : Nat} (sc : Scope (core3P P))
    (hsc : ∀ j < lg.imp.exports.length, sc.frame.funcs[lg.wire.length + j]? = some ⟨fb + j⟩) :
    Reach prof (linkHost impl).hr (linkHost impl).dispatch none
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] []) sc
        (lg.imp.exports.mapIdx fun i x => (.export_ { name := x.name } ⟨.func, lg.wire.length + i⟩
          none : Syntax.Definition Silmaril.Wasm.Module)))
      m (fun os sc' m' => os = [] ∧
        sc'.exports = sc.exports ++ lg.imp.exports.mapIdx (fun i x => (x.name, .func ⟨fb + i⟩)) ∧
        m' = m) := by
  obtain ⟨sc', h, hx⟩ := exportsP_run (σ := σ) (R := (callRecurse : Recurse (core3P P) σ))
    (inst := ⟨0⟩) (outer := []) (args := []) lg.imp.exports lg.wire.length fb sc m hsc
  exact (Reach.ofTRuns h).mono fun _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂ ▸ hx, h₃⟩

/-- **The definitions of `lg.toRef` run** from a configuration with an empty core store, to the
importer's nested instantiation after R4's configuration. -/
theorem toRefG_reach (hInit : d.InitSX) (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    (cfg : Machine.Config (core3P P) σ) (hcore : cfg.core = (core3P P).empty _) :
    Reach prof (linkHost impl).hr (linkHost impl).dispatch none
      (List.foldlM (instantiateDef (callRecurse : Recurse (core3P P) σ) ⟨0⟩ [] []) {} lg.toRef)
      cfg (fun os sc m => os = [] ∧ FoldEnd d Ii cfg sc.exports m) := by
  refine Reach.foldlM_append (Q := fun os sc m => os = [] ∧ ∃ (m₁ : Machine.Config (core3P P) σ)
      (pl : d.Pl) (F : CoreFoot) (es : List (String × ItemVal (core3P P)))
      (r : Store (CanonHost (core3P P) × Nat)),
      d.InitAtX pl F es cfg m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
      TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
      (∀ j < lg.imp.exports.length,
        sc.frame.funcs[lg.wire.length + j]? = some ⟨m₁.store.funcs.length + j⟩) ∧
      sc.exports = [] ∧ m = impCfg lg Ii m₁ r) ?_ ?_
  · refine Reach.foldlM_append (Q := fun os sc m => os = [] ∧ ∃ (m₁ : Machine.Config (core3P P) σ)
        (pl : d.Pl) (F : CoreFoot) (es esI : List (String × ItemVal (core3P P)))
        (r : Store (CanonHost (core3P P) × Nat)),
        d.InitAtX pl F es cfg m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
        TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
        funcExports esI =
          lg.imp.exports.mapIdx (fun i x => (x.name, ⟨m₁.store.funcs.length + i⟩)) ∧
        TagOrFunc esI ∧ sc = scI d pl es esI ∧
        m = impCfg lg Ii m₁ r) ?_ ?_
    · refine Reach.foldlM_append (Q := fun os sc m => os = [] ∧ ∃ (pl : d.Pl) (F : CoreFoot)
          (es : List (String × ItemVal (core3P P))), d.InitAtX pl F es cfg m ∧ sc = scW d pl es)
        ?_ ?_
      · refine Reach.foldlM_append (stageA hInit cfg hcore) fun os sc m h => ?_
        obtain ⟨rfl, pl, F, es, hA, rfl⟩ := h
        exact (stageW hW hA).mono fun os' sc' m' ⟨h₁, h₂, h₃⟩ => by
          subst h₁ h₂ h₃
          exact ⟨rfl, pl, F, es, hA, rfl⟩
      · intro os sc m h
        obtain ⟨rfl, pl, F, es, hA, rfl⟩ := h
        exact (stageI hFr hW hIg hIi hIa hseg hI hA).mono
          fun os' sc' m' ⟨h₁, esI, r, hrs, hh, hxI, htI, h₂, h₃⟩ => by
            subst h₁ h₂ h₃
            exact ⟨rfl, m, pl, F, es, esI, r, hA, hrs, hh, hxI, htI, rfl, rfl⟩
    · intro os sc m h
      obtain ⟨rfl, m₁, pl, F, es, esI, r, hA, hrs, hh, hxI, htI, rfl, rfl⟩ := h
      exact (stageIA hIg hNI hxI htI (scI d pl es esI) rfl).mono
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
    exact (stageX sc hf).mono fun os' sc' m' ⟨h₁, h₂, h₃⟩ => by
      subst h₁ h₃
      refine ⟨rfl, m₁, pl, F, es, r, hA, hrs, hh, ?_, rfl⟩
      rw [h₂, hx, List.nil_append]
      exact funcExports_mapIdx_func _ _

/-- The definitions of `lg.toRef` are no imports. -/
theorem noImport_toRefG (lg : LinkedG) : NoImport lg.toRef := by
  intro d hd n x e
  simp only [LinkedG.toRef, List.mem_append, List.mem_cons, List.mem_map, List.mem_mapIdx,
    List.not_mem_nil, or_false] at hd
  rcases hd with ((((rfl | rfl | rfl) | ⟨_, -, rfl⟩) | rfl) | ⟨_, -, rfl⟩) | ⟨_, _, rfl⟩ <;>
    cases e

/-- **Root instantiation of `lg.toRef`** from a configuration with the empty core store and no
component instance: the root instance `0`, then the definitions (`toRefG_reach`). -/
theorem rootG_reach (hInit : d.InitSX) (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    (cfg : Machine.Config (core3P P) σ) (hcore : cfg.core = (core3P P).empty _)
    (hinsts : cfg.store.insts = []) :
    Reach prof (linkHost impl).hr (linkHost impl).dispatch none
      (instantiateRootCall lg.toRef [] : Canon.P (core3P P) σ (InstId × Exports (core3P P))) cfg
      (fun os p m => os = [] ∧ p.1 = ⟨0⟩ ∧
        FoldEnd d Ii { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } p.2 m) := by
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
  refine Reach.bind_eq (Reach.ofTRuns (trapIf_run ((congrArg (!·) hac).trans rfl) _ cfg)) ?_
  refine Reach.bind_eq (Reach.ofTRuns (TRuns.getStore cfg)) ?_
  refine Reach.bind_eq (Reach.ofTRuns (checkImport_run (hpre _) cfg)) ?_
  refine Reach.bind_eq (Reach.ofTRuns (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg)) ?_
  rw [hid]
  unfold instantiateComponent
  refine Reach.bind (Q := fun os xs m => os = [] ∧
      FoldEnd d Ii { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } xs m)
    (Reach.bind (toRefG_reach hInit hFr hW hIg hIi hIa hseg hNI hI _ hcore)
      fun os sc m h => Reach.pure_of ?_)
    fun os xs m h => Reach.pure_of ?_
  · obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, h⟩
  · obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, rfl, h⟩

/-- The configuration at which the exporter's nested instantiation starts in the parent. -/
def startG (h₀ : σ) : Machine.Config (core3P P) σ :=
  { (initConfig h₀ : Machine.Config (core3P P) σ) with
    store := ArenaOps.allocSt ArenaField.insts {}
      (DispatchSt.incNestingSt (initConfig h₀ : Machine.Config (core3P P) σ).store) }

/-- **The instantiation program of `lg.toRef` reaches** the importer's nested instantiation after
R4's configuration, the nesting depth decremented, observing the root instance and the export
map. -/
theorem instProgG_reach (hInit : d.InitSX) (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii) (h₀ : σ) :
    Reach prof (linkHost impl).hr (linkHost impl).dispatch none
      (instantiateProg lg.toRef [] : Canon.P (core3P P) σ (Ret (core3P P)))
      (initConfig h₀)
      (fun os _ m => ∃ (m₁ : Machine.Config (core3P P) σ) (pl : d.Pl) (F : CoreFoot)
        (es : List (String × ItemVal (core3P P))) (r : Store (CanonHost (core3P P) × Nat)),
        d.InitAtX pl F es (startG h₀) m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
        TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
        os = [instantiatedObs ⟨0⟩ (exportMapG lg m₁.store.funcs.length)] ∧
        m = { m₁ with
          store := DispatchSt.decNestingSt (impStore lg Ii m₁.store m₁.core r)
          core := impCore m₁.core r }) := by
  unfold instantiateProg
  refine Reach.bind_eq (Reach.ofTRuns
    (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) _)) ?_
  refine Reach.bind (rootG_reach hInit hFr hW hIg hIi hIa hseg hNI hI _ rfl rfl)
    fun os p m h => ?_
  obtain ⟨rfl, hp, m₁, pl, F, es, r, hA, hrs, hh, hx, rfl⟩ := h
  obtain ⟨inst, xs⟩ := p
  simp only at hp hx
  subst hp
  refine Reach.bind_eq (Reach.ofTRuns
    (TRuns.modifyStore (f := DispatchSt.decNestingSt) (fun _ => rfl) _)) ?_
  refine Reach.bind (Reach.ofSRuns
    (p := (emit (instantiatedObs ⟨0⟩ (funcExports xs)) : Canon.P (core3P P) σ Unit))
    (SRuns.emit (SRuns.pure () _))) fun os' u m' ⟨h₁, _, h₂⟩ => Reach.pure_of ?_
  subst h₁ h₂
  refine ⟨m₁, pl, F, es, r, hA, hrs, hh, ?_, rfl⟩
  rw [hx]
  rfl

/-- **The configuration after instantiating `lg.toRef`**: R4's configuration `m₁` with the
importer's nested instantiation after it, the nesting depth decremented, the host in control. -/
def afterG (lg : LinkedG) (Ii : Silmaril.Wasm.Game.ScalarInstance) (m₁ : Machine.Config (core3P P) σ)
    (r : Store (CanonHost (core3P P) × Nat)) : Machine.Config (core3P P) σ :=
  { m₁ with
    store := DispatchSt.decNestingSt (impStore lg Ii m₁.store m₁.core r)
    core := impCore m₁.core r
    ctl := [] }

/-- **The instantiation of `lg.toRef` as a host event** from the initial configuration: a run
without host events to `afterG`, observing the root instance `0` and the export map. -/
theorem instG_run (hInit : d.InitSX) (hFr : d.Frame) (hW : lg.WireTy) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity)
    (hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [])
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii) (h₀ : σ) :
    ∃ (tr : List (Label (core3P P) σ)) (m₁ : Machine.Config (core3P P) σ) (pl : d.Pl)
      (F : CoreFoot) (es : List (String × ItemVal (core3P P)))
      (r : Store (CanonHost (core3P P) × Nat)),
      d.InitAtX pl F es (startG h₀) m₁ ∧ Store.mapH Prod.snd r = Ii.store ∧
      TrampsOf lg (fidG d pl) (nextInst m₁.store) r ∧
      Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch (initConfig h₀)
        (.host (instantiateTop lg.toRef []) :: tr) (afterG lg Ii m₁ r) ∧
      (∀ ev, Label.host ev ∉ tr) ∧
      traceObs tr = [instantiatedObs ⟨0⟩ (exportMapG lg m₁.store.funcs.length)] := by
  obtain ⟨tr, a, m', hs, hh, -, -, m₁, pl, F, es, r, hA, hrs, htr, ho, rfl⟩ :=
    instProgG_reach (prof := prof) (impl := impl) hInit hFr hW hIg hIi hIa hseg hNI hI h₀ rfl
      (fun _ => Pure.pure .unit) [] []
  have s₀ : Machine.Step prof (linkHost impl).hr (linkHost impl).dispatch (initConfig h₀)
      (.host (instantiateTop lg.toRef []))
      { (initConfig h₀ : Machine.Config (core3P P) σ) with
        ctl := [.ofProg none (StepDefs.runProg (instantiateProg lg.toRef []))] } :=
    Step.hostRun ⟨rfl, rfl, rfl⟩
  have s₁ : UniqueStep prof (linkHost impl).hr (linkHost impl).dispatch
      { afterG lg Ii m₁ r with ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      (afterG lg Ii m₁ r) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  have hs' : Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
      { (initConfig h₀ : Machine.Config (core3P P) σ) with
        ctl := [.ofProg none (StepDefs.runProg (instantiateProg lg.toRef []))] } tr
      { afterG lg Ii m₁ r with ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } := hs
  refine ⟨tr ++ [.tau], m₁, pl, F, es, r, hA, hrs, htr,
    .cons s₀ (Adequacy.steps_append hs' (.cons s₁.1 (.refl _))), fun ev hm => ?_, ?_⟩
  · rcases List.mem_append.1 hm with hm | hm
    · exact hh ev hm
    · simp at hm
  · rw [traceObs_append, ← ho]
    exact List.append_nil _

end Fold

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit

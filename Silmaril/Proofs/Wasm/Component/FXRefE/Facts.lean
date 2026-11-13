module

public import Silmaril.Proofs.Wasm.Component.FXRefE.Run
public import Silmaril.Proofs.Wasm.Component.Reference.InstCore
public import Silmaril.Proofs.Wasm.Component.FXRef.Spec
public import Silmaril.Wasm.Component.EngineRef.Thms
public import Silmaril.Wasm.Component.FXRef.Defs
public import Silmaril.Wasm.Component.FXEngine.Thms

/-!
# The engine facts of `fxE P`, and the machine half over the WasmFX engine

* `imports_nil`, `prepare_core3`, `prepare_fx`: a `Simple.Inst` module has no imports, and
  the FX engine prepares it (as an FX module with no FX functions) in the empty store at any
  host type, to the Core 3.0 store of `instantiateOnce?` and the FX instance with no FX
  exports;
* `instOf_core3P_some`: its `core3P P` engine instance exists, with the store of its `IsInst`
  instance `I` and export `k` at `I.addrs.getD k 0`;
* `facts_fx`: **the instantiation facts** (`EngineRef.InstFacts`) of `fxE P` and **the run
  facts** (`EngineRef.RunFacts`, from `FXRefE.Run.runFacts_fx`) of every typed export call,
  whose outcomes (`specOut_sub`) are in `exportSpecE (fxE P) ofNum`;
* `refToSpecE_fx`: **`FXRef.RefToSpecEFXAll`**, through `EngineRef.refToSpecEOn_of_facts`.

Unlike Lime1 (`Lime1RefE`), no engine fact is left open: the FX engine prepares a Core module
as Core 3.0 does, and on a store with neither host nor FX functions its Core threads are Core
3.0 threads, so Core 3.0 instantiation (`inst_once`), type soundness (`run_results_typed`) and
the absence of callouts (`run_no_callout`) apply.

New proofs; `prepare_core3` is `FXRef.prepare_core3P_nat` at any host type.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXRefE

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.EngineRef Silmaril.Wasm.Component.FXRef
open Silmaril.Proofs.Wasm.Component.Reference (inst_once lookup_funcExport exports_core3P
  instantiateOnce?_mapH empty_mapH Store.mapH)
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component.Runtime (CanonHost)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-! ## Lists -/

theorem mapM_getElem? {α β : Type} {f : α → Option β} :
    ∀ {L : List α} {R : List β}, L.mapM f = some R → ∀ {k : Nat} {x : α}, L[k]? = some x →
      ∃ y, f x = some y ∧ R[k]? = some y
  | [], _, _, _, _, hx => by simp at hx
  | a :: L, R, h, k, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨b, hb, R', hR', e⟩ := h
    cases e
    cases k with
    | zero =>
      cases (Option.some.inj hx)
      exact ⟨b, hb, rfl⟩
    | succ k => exact mapM_getElem? hR' hx

theorem mapM_some {α β : Type} {f : α → Option β} :
    ∀ {L : List α}, (∀ x ∈ L, ∃ y, f x = some y) → ∃ R, L.mapM f = some R
  | [], _ => ⟨[], rfl⟩
  | a :: L, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨R, hR⟩ := mapM_some (L := L) fun x hx => h x (List.mem_cons_of_mem a hx)
    exact ⟨b :: R, by simp [List.mapM_cons, hb, hR]⟩

/-! ## Instantiation -/

/-- A validated module whose type has no imports has no imports. -/
theorem imports_nil {m : Module} {mt : Validation.CModuleType} (hv : Validation.validate? m = some mt)
    (hmt : mt.imports = []) : m.imports = [] := by
  cases Silmaril.Wasm.Validation.validate?_sound hv with
  | mk _ himports =>
    subst hmt
    exact List.forall₂_nil_right_iff.1 himports

/-- `prepareE?` on an import-free, start-free module, at any host type. -/
theorem prepare_core3 {H : Type} {m : Module} {mt : Validation.CModuleType} {cs : Store H}
    {f' : Frame} (hv : Validation.validate? m = some mt) (hmt : mt.imports = [])
    (ho : instantiateOnce? ({} : Store H) m [] = some (cs, f', none)) :
    Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store H) m [] =
      some (cs, f'.module, none) := by
  simp only [Silmaril.Wasm.Component.Engine.Core3.prepareE?, hv, hmt, ho, externAddrsOk?,
    ite_true]

/-- **The FX engine prepares a Core module** as Core 3.0 does, with no FX exports. -/
theorem prepare_fx {H : Type} {m : Module} {mt : Validation.CModuleType} {cs : Store (FXCode H)}
    {f' : Frame} (hv : Validation.validate? m = some mt) (hmt : mt.imports = [])
    (ho : instantiateOnce? ({} : Store (FXCode H)) m [] = some (cs, f', none)) :
    (fxE P).prepare? ((fxE P).empty H) (ofCoreFX m) [] = some (cs, ⟨f'.module, []⟩, none) := by
  show prepareFX? ({} : Store (FXCode H)) ⟨m, []⟩ [] = _
  unfold prepareFX?
  rw [show (⟨m, []⟩ : ModuleFX).core = m from rfl, prepare_core3 hv hmt ho]
  rfl

/-- The import types of a Core module without imports. -/
theorem importTypes_fx {m : Module} {mt : Validation.CModuleType}
    (hv : Validation.validate? m = some mt) (hmt : mt.imports = []) :
    (fxE P).importTypes (ofCoreFX m) = [] := by
  show Silmaril.Wasm.Component.Engine.Core3.importTypesE m = []
  unfold Silmaril.Wasm.Component.Engine.Core3.importTypesE
  split
  · simp [imports_nil hv hmt]
  · rfl

/-- Export `k` of a `Simple.Inst` module is found by name in its Core instance, at
`I.addrs.getD k 0`. -/
theorem lookup_core3P {c : Simple} (hi : c.Inst) {I : Silmaril.Wasm.Game.ScalarInstance}
    {mt : Validation.CModuleType} {f' : Frame} (hv : Validation.validate? c.mod.mod = some mt)
    (hoN : instantiateOnce? ({} : Store Nat) c.mod.mod [] = some (I.store, f', none))
    (ha : Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs) {k : Nat} {nm : String}
    {ft : CoreFuncTy} (hk : c.mod.exports[k]? = some (nm, ft)) :
    (((core3P P).exports f'.module).lookup nm).bind (core3P P).asFunc? =
      some (I.addrs.getD k 0) := by
  have hl := lookup_funcExport hi hv hoN ha hk
  rw [← exports_core3P P] at hl
  exact (congrArg (fun o => Option.bind o (core3P P).asFunc?) hl).trans rfl

/-- The `core3P P` engine instance of an import-free, start-free module with export
addresses `L`. -/
theorem instOf_core3P_eq {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {mt : Validation.CModuleType} {f' : Frame} (hv : Validation.validate? c.mod.mod = some mt)
    (hmt : mt.imports = [])
    (hoN : instantiateOnce? ({} : Store Nat) c.mod.mod [] = some (I.store, f', none))
    {L : List Nat} (hL : exportAddrs (core3P P) f'.module c.mod.exports = some L) :
    instOf (core3P P) c.mod.mod (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some ⟨I.store, L⟩ := by
  show instOf (core3P P) c.mod.mod [] c.mod.exports = _
  unfold instOf
  simp only [allocHosts, List.map_nil]
  rw [Silmaril.Proofs.Wasm.Component.FXRef.prepare_core3P_nat hv hmt hoN]
  simp only [hL]
  rfl

/-- **The `core3P P` engine instance of a `Simple.Inst` module** exists, with the store of the
`IsInst` instance and export `k` at `I.addrs.getD k 0`. -/
theorem instOf_core3P_some {c : Simple} (hi : c.Inst) {I : Silmaril.Wasm.Game.ScalarInstance}
    {mt : Validation.CModuleType} {f' : Frame} (hv : Validation.validate? c.mod.mod = some mt)
    (hmt : mt.imports = [])
    (hoN : instantiateOnce? ({} : Store Nat) c.mod.mod [] = some (I.store, f', none))
    (ha : Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs) :
    ∃ J : EInstance (core3P P),
      instOf (core3P P) c.mod.mod (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
        some J ∧ J.store = I.store ∧
      ∀ (k : Nat) (nm : String) (ft : CoreFuncTy), c.mod.exports[k]? = some (nm, ft) →
        J.addrs[k]? = some (I.addrs.getD k 0) := by
  obtain ⟨L, hL⟩ : ∃ L, exportAddrs (core3P P) f'.module c.mod.exports = some L :=
    mapM_some fun p hp => by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hp
      exact ⟨_, lookup_core3P hi hv hoN ha (nm := p.1) (ft := p.2) hk⟩
  refine ⟨⟨I.store, L⟩, instOf_core3P_eq hv hmt hoN hL, rfl, fun k nm ft hk => ?_⟩
  obtain ⟨y, hy, hLk⟩ := mapM_getElem? hL hk
  have hy' : some (I.addrs.getD k 0) = some y := (lookup_core3P hi hv hoN ha hk).symm.trans hy
  show L[k]? = _
  rw [hLk, hy']

/-! ## The machine half -/

/-- The run outcomes of a typed call are in the FX engine's specification. -/
theorem specOut_sub {c : Simple} {J : EInstance (core3P P)}
    (hJ : instOf (core3P P) c.mod.mod (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some J) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList x.ty.params vs = true) :
    specOut x (engineOut (core3P P) J x.core (lowerArgs x.ty.params vs))
        (engineDiverges (core3P P) J x.core (lowerArgs x.ty.params vs)) ⊆
      exportSpecE (fxE P) ofNum c x vs := by
  rw [exportSpecE_ofNum]
  have hl : checkLower x.ty.params vs = some (lowerArgs x.ty.params vs) := by
    unfold checkLower
    rw [ite_eq_left_iff.mpr (fun h => absurd hvs h)]
  intro b hb
  unfold exportSpecE
  rw [hl]
  rcases hb with ⟨r, hr, rfl⟩ | ⟨rfl, hd⟩
  · exact Or.inl ⟨J, hJ, r, hr, rfl⟩
  · exact Or.inr ⟨rfl, J, hJ, hd⟩

/-- The Nat-store instantiation of the module, from the one at the machine's host type. -/
theorem instantiate_nat {H : Type} {m : Module} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : Store (FXCode H)} {f' : Frame}
    (ho : instantiateOnce? ({} : Store (FXCode H)) m [] = some (cs, f', none))
    (hs : Store.mapH (fun _ => (0 : Nat)) cs = I.store) :
    instantiateOnce? ({} : Store Nat) m [] = some (I.store, f', none) := by
  have e := instantiateOnce?_mapH (fun _ : FXCode H => (0 : Nat)) ({} : Store (FXCode H)) m []
  rw [empty_mapH, ho] at e
  rw [e, ← hs]
  rfl

/-- The lookup of a lifted export in the FX instance of the module. -/
theorem lookup_fx {H : Type} {c : Simple} (hc : c.Good) (hi : c.Inst)
    {I : Silmaril.Wasm.Game.ScalarInstance} {mt : Validation.CModuleType} {cs : Store (FXCode H)}
    {f' : Frame} (hv : Validation.validate? c.mod.mod = some mt)
    (ho : instantiateOnce? ({} : Store (FXCode H)) c.mod.mod [] = some (cs, f', none))
    (ha : Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs) (x : SimpleExport)
    (hx : x ∈ c.exports) :
    ∃ v, ((fxE P).exports ⟨f'.module, []⟩).lookup (coreNameE c.mod x) = some v ∧
      (fxE P).asFunc? v = some (I.addrs.getD x.core 0) := by
  obtain ⟨nm, hn⟩ := hc.core x hx
  refine ⟨.func (I.addrs.getD x.core 0), ?_, rfl⟩
  show (Silmaril.Wasm.Component.Engine.Core3.instExports f'.module ++ []).lookup
    (coreNameE c.mod x) = _
  rw [List.append_nil, coreNameE, hn]
  exact lookup_funcExport hi hv ho ha hn

/-- **The engine facts of `fxE P`** for a `Simple.Inst` component: instantiation facts, and run
facts of every typed export call with outcomes in `exportSpecE (fxE P) ofNum`. -/
theorem facts_fx {c : Simple} (hc : c.Good) (hi : c.Inst) :
    ∃ (cs : (fxE P).Store (CanonHost (fxE P))) (ci : (fxE P).Inst)
      (addr : Nat → (fxE P).FuncAddr),
      InstFacts (fxE P) ofCoreFX c cs ci addr ∧
      ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
        ∃ (Out : Set (Option (List Flat))) (Div : Prop),
          RunFacts (fxE P) cs (addr x.core) (lowerArgs x.ty.params vs)
            (ValTy.flatList x.ty.results) Out Div ∧
          specOut x Out Div ⊆ exportSpecE (fxE P) ofNum c x vs := by
  obtain ⟨I, mt, cs, f', hI, hv, hmt, ho, hs, ha⟩ :=
    inst_once (H := FXCode (CanonHost (fxE P))) (fun _ => (0 : Nat)) hi
  obtain ⟨J, hJ, hJs, hJa⟩ := instOf_core3P_some (P := P) hi hv hmt (instantiate_nat ho hs) ha
  have hrun : ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      RunFacts (fxE P) cs (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs)
        (ValTy.flatList x.ty.results) (engineOut (core3P P) J x.core (lowerArgs x.ty.params vs))
        (engineDiverges (core3P P) J x.core (lowerArgs x.ty.params vs)) := fun x hx vs hvs =>
    runFacts_fx ⟨hI, hs, hc.core x hx, Silmaril.Proofs.Wasm.Component.Reference.lowerList_types _ _ hvs⟩
      hJs (hJa _ _ _ (hc.core x hx).choose_spec)
  exact ⟨cs, ⟨f'.module, []⟩, fun k => I.addrs.getD k 0,
    ⟨importTypes_fx hv hmt, prepare_fx hv hmt ho, lookup_fx hc hi hv ho ha⟩,
    fun x hx vs hvs => ⟨_, _, hrun x hx vs hvs, specOut_sub hJ x vs hvs⟩⟩

/-- **The machine half over the WasmFX engine** (`FXRef.RefToSpecEFXAll`). -/
theorem refToSpecE_fx : RefToSpecEFXAll := by
  intro P prof c hc hf hi ha
  exact refToSpecEOn_of_facts (E := fxE P) (ofCore := ofCoreFX) (emb := ofNum)
    (D := fun _ => True) (fun c _ hc _ hi _ => facts_fx hc hi) prof c trivial hc hf hi ha

end Silmaril.Proofs.Wasm.Component.FXRefE

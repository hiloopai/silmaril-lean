module

public import Silmaril.Proofs.Wasm.Component.Lime1Eng.CoreAlloc
public import Silmaril.Wasm.Component.Lime1RefE.Defs

/-!
# The Lime1 engine instantiates every module of the Lime1 domain that has a Core 3.0 instance

`Lime1RefE.Lime1InstOk`: for a simple component in the Lime1 domain whose module has a
Core 3.0 instance (`Simple.Inst`), `instOf lime1` succeeds. This is the converse direction of the
instantiation bridge `Lime1Inst.instBridgeE`, proved from the Core 3.0 run:

* the global initializers: Core's `$evalglobals` evaluates their images, so Lime1 evaluates them
  (`globals_of_core`, by `evalConst_back`; Lime1 initializers read no global, since the module
  has no imports);
* allocation: Lime1 allocation of a valid module cannot fail otherwise (`allocate?_some`);
* the segments: the Core allocation of the residue is related to the Lime1 allocation
  (`rel_of_prepare`), and Core's segment initialisation succeeds, so every Lime1 segment
  resolves (`elemList_back`, `dataList_back`);
* no start function (the Core instance has none), and the engine's lookup of the exports by name
  succeeds (distinct export names, `Simple.Inst.names`).

* **`lime1Inst_proof`**: `Lime1RefE.Lime1InstOk`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Eng

open Silmaril.Wasm Silmaril.Wasm.Lime1 Silmaril.Wasm.Lime1.Validation
open Silmaril.Wasm.Execution.Runtime (Value ModuleInst GlobalInst ExternVal)
open Silmaril.Wasm.Execution.Core (evalConst?)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Lime1Ref
open Silmaril.Proofs.Wasm.Component.Lime1Inst (residueL residueStore residueImports withElems
  funcrefElem globalInsts)
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)

/-! ## Global initializers -/

/-- **Core's `$evalglobals` on the images of initializers that read no global, backwards.** -/
theorem evalGlobals_back {C : Context} (hC : C.globals = [])
    {S : Silmaril.Wasm.Execution.Core.Store Nat} {F : Silmaril.Wasm.Execution.Core.Frame} :
    ∀ {gs : List Lime1.Global} {gts : List Silmaril.Wasm.Validation.CGlobalType}
      {r : Silmaril.Wasm.Execution.Core.Store Nat × Silmaril.Wasm.Execution.Core.Frame ×
        List Silmaril.Wasm.Execution.Core.Val},
      (∀ g ∈ gs, ConstantExpr C g.init) →
      Silmaril.Wasm.Execution.Core.evalGlobals? evalConst? S F gts
        (gs.map fun g => Lime1.Expr.toCore g.init) = some r →
      ∃ vals, gs.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr?
        ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init) = some vals
  | [], _, _, _, _ => ⟨[], rfl⟩
  | _ :: _, [], _, _, h => by simp [Silmaril.Wasm.Execution.Core.evalGlobals?] at h
  | g :: gs, gt :: gts, _, hc, h => by
    have h' : ∃ S' v, evalConst? S F (Lime1.Expr.toCore g.init) = some (S', v) ∧
        ∃ S'' : Silmaril.Wasm.Execution.Core.Store Nat, ∃ F'' : Silmaril.Wasm.Execution.Core.Frame,
          ∃ r', Silmaril.Wasm.Execution.Core.evalGlobals? evalConst? S'' F'' gts
          (gs.map fun g => Lime1.Expr.toCore g.init) = some r' := by
      simp only [List.map_cons, Silmaril.Wasm.Execution.Core.evalGlobals?] at h
      split at h
      · cases h
      · rename_i S' v hv
        split at h
        · cases h
        · rename_i S'' F'' vs hr
          exact ⟨S', v, hv, _, _, _, hr⟩
    obtain ⟨S', v, hv, S'', F'', r', hr⟩ := h'
    have hnoG : ∀ x, Lime1.Instr.globalGet x ∈ g.init →
        GAgreeAt S F ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} x := fun x hx => by
      have hci := hc g (by simp) _ hx
      cases hci with
      | globalGet _ hget => simp [hC] at hget
    obtain ⟨-, v', hv', -⟩ := evalConst_back (hc g (by simp)) hnoG hv
    obtain ⟨vals, hvals⟩ := evalGlobals_back (S := S'') (F := F'') hC
      (fun g' hg' => hc g' (by simp [hg'])) hr
    exact ⟨v' :: vals, by simp only [List.mapM_cons, hv', hvals]; rfl⟩

/-- **The global initializers of the decoding of a module with a Core 3.0 instance evaluate.** -/
theorem globals_of_core {M : Silmaril.Wasm.Module} {l : Lime1.Module}
    (hret : l.toCore = Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElems M)
    (hv : ModuleValid l) (hlimp : l.imports = [])
    {r : Silmaril.Wasm.Execution.Core.Store Nat × Silmaril.Wasm.Execution.Core.Frame ×
      Option FuncIdx}
    (h : Silmaril.Wasm.Execution.Core.instantiateOnce? (Silmaril.Wasm.Game.importStore []) M [] =
      some r) :
    ∃ vals, l.globals.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init) = some vals := by
  obtain ⟨-, hgi⟩ := Silmaril.Proofs.Wasm.Component.Lime1Inst.globals_image hret
  have hC : (initializerContext l).globals = [] := by
    simp [initializerContext, importedGlobals, hlimp]
  unfold Silmaril.Wasm.Execution.Core.instantiateOnce? at h
  rw [hgi] at h
  split at h
  · cases h
  · rename_i r' hr
    exact evalGlobals_back hC (fun g hg => (hv.globals g hg).constant) hr

/-! ## The residue -/

theorem forall₂_of_map_eq {α β γ : Type _} {f : α → γ} {g : β → γ} :
    ∀ {as : List α} {bs : List β}, as.map f = bs.map g → List.Forall₂ (fun a b => g b = f a) as bs
  | [], [], _ => .nil
  | a :: as, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1.symm (forall₂_of_map_eq h.2)

theorem residue_imported (n : Nat) :
    Silmaril.Wasm.V1.Execution.importedInstance (residueImports n) =
      { globals := Silmaril.Wasm.V1.Execution.addresses .global 0 n } := by
  simp [Silmaril.Wasm.V1.Execution.importedInstance, residueImports, List.filterMap_map,
    Silmaril.Wasm.V1.Execution.addresses]

/-- The global reads of the residue's allocation have the residue context's types. -/
theorem gTyped_residue {l : Lime1.Module} (hlimp : l.imports = [])
    {vals : List Value} (hT2 : List.Forall₂ (fun g v => v.type = g.type.value) l.globals vals)
    {A : Silmaril.Wasm.Lime1.Execution.Store Nat} {mod : ModuleInst}
    (hal : Silmaril.Wasm.Lime1.Execution.allocate? (residueStore l.globals vals) (residueL l)
      (residueImports l.globals.length) = some (A, mod)) :
    GTyped A mod (moduleContext (residueL l)) := by
  obtain ⟨exports, funcs, -, -, rfl, rfl⟩ := Silmaril.Wasm.Lime1.Execution.allocate?_inv rfl hal
  intro x v hx gt hgt
  rw [Silmaril.Proofs.Wasm.Component.Lime1Inst.moduleContext_residue, ctx_globals hlimp,
    List.getElem?_map] at hgt
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hgt
  have hxn : x.toNat < l.globals.length := lt_of_getElem? hg
  obtain ⟨w, hw, hwt⟩ := Silmaril.Wasm.Lime1.Execution.forall₂_getElem? hT2 hg
  have hgx : (globalInsts l.globals vals)[x.toNat]? = some ⟨w, g.type.mutability⟩ := by
    simp [globalInsts, List.getElem?_zipWith, hg, hw]
  have hx' : v = w := by
    simpa [lread, Silmaril.Wasm.Lime1.Execution.baseInst,
      residue_imported, getElem?_addresses hxn, residueStore, hgx] using hx.symm
  rw [hx']
  exact hwt

/-- Every function index of the residue's context has an address in its allocation. -/
theorem funcs_residue {l : Lime1.Module} (hlimp : l.imports = []) {vals : List Value}
    {A : Silmaril.Wasm.Lime1.Execution.Store Nat} {mod : ModuleInst}
    (hal : Silmaril.Wasm.Lime1.Execution.allocate? (residueStore l.globals vals) (residueL l)
      (residueImports l.globals.length) = some (A, mod)) (i : FuncIdx)
    (hi : ∃ ft, (moduleContext (residueL l)).funcs[i.toNat]? = some ft) :
    ∃ a, mod.funcs[i.toNat]? = some a := by
  obtain ⟨exports, funcs, -, -, rfl, -⟩ := Silmaril.Wasm.Lime1.Execution.allocate?_inv rfl hal
  obtain ⟨ft, hft⟩ := hi
  rw [Silmaril.Proofs.Wasm.Component.Lime1Inst.moduleContext_residue] at hft
  have hlt : i.toNat < l.funcs.length := (lt_of_getElem? hft).trans_le (ctx_funcs_le hlimp)
  exact ⟨⟨i.toNat⟩, by simp [Silmaril.Wasm.Lime1.Execution.baseInst,
    residue_imported, residueL, residueStore, getElem?_addresses hlt]⟩

/-- Lime1 preparation from its parts. -/
theorem prepare?_of {s : Silmaril.Wasm.Lime1.Execution.Store Nat} {m : Lime1.Module}
    {imports : List ExternVal} {A : Silmaril.Wasm.Lime1.Execution.Store Nat} {mod : ModuleInst}
    {es : List Silmaril.Wasm.Lime1.Execution.ElemWrite}
    {ds : List Silmaril.Wasm.Lime1.Execution.DataWrite}
    (ha : Silmaril.Wasm.Lime1.Execution.allocate? s m imports = some (A, mod))
    (he : m.elems.mapM (Silmaril.Wasm.Lime1.Execution.resolveElem? A mod) = some es)
    (hd : m.data.mapM (Silmaril.Wasm.Lime1.Execution.resolveData? A mod) = some ds)
    (hst : m.start = none) :
    Silmaril.Wasm.Lime1.Execution.prepare? s m imports =
      some ⟨ds.foldl Silmaril.Wasm.Lime1.Execution.applyData
        (es.foldl Silmaril.Wasm.Lime1.Execution.applyElem A), mod, []⟩ := by
  simp [Silmaril.Wasm.Lime1.Execution.prepare?, ha, he, hd, hst]

/-- The segment runs of a successful `initSegments?`. -/
theorem initSegments_inv {H : Type}
    {ev : Silmaril.Wasm.Execution.Core.Store H → Silmaril.Wasm.Execution.Core.Frame →
      Silmaril.Wasm.Expr →
        Option (Silmaril.Wasm.Execution.Core.Store H × Silmaril.Wasm.Execution.Core.Val)}
    {S S' : Silmaril.Wasm.Execution.Core.Store H} {F F' : Silmaril.Wasm.Execution.Core.Frame}
    {m : Silmaril.Wasm.Module}
    (h : Silmaril.Wasm.Execution.Core.initSegments? ev S F m = some (S', F')) :
    ∃ S₁, Silmaril.Wasm.Execution.Core.initElemList? ev S F
        ((List.range' 0 m.elems.length).zip m.elems) = some S₁ ∧
      Silmaril.Wasm.Execution.Core.initDataList? ev S₁ F
        ((List.range' 0 m.data.length).zip m.data) = some S' := by
  rw [← List.range_eq_range', ← List.range_eq_range']
  unfold Silmaril.Wasm.Execution.Core.initSegments? at h
  split at h
  · cases h
  · rename_i S₁ F₁ h₁
    unfold Silmaril.Wasm.Execution.Core.initElem? at h₁
    obtain ⟨S₁', h₁', he₁⟩ := Option.map_eq_some_iff.mp h₁
    have hS₁ : S₁' = S₁ := congrArg Prod.fst he₁
    have hF₁ : F = F₁ := congrArg Prod.snd he₁
    unfold Silmaril.Wasm.Execution.Core.initData? at h
    obtain ⟨S₂, h₂, he₂⟩ := Option.map_eq_some_iff.mp h
    have hS₂ : S₂ = S' := congrArg Prod.fst he₂
    refine ⟨S₁, hS₁ ▸ h₁', ?_⟩
    rw [hF₁, ← hS₂]
    exact h₂

/-! ## Assembly -/

/-- **The Lime1 residue prepares**, when the Core 3.0 module has an instance. -/
theorem residue_prepare {M : Silmaril.Wasm.Module} {l : Lime1.Module}
    (hret : l.toCore = Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElems M)
    (hv : ModuleValid l) (hlimp : l.imports = []) {vals : List Value}
    (hvals : l.globals.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init) = some vals)
    (hty : ∀ g ∈ l.globals, ∀ v, Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init = some v → v.type = g.type.value)
    {S : Silmaril.Wasm.Execution.Core.Store Nat} {f : Silmaril.Wasm.Execution.Core.Frame}
    (hinst : Silmaril.Wasm.Execution.Core.instantiateOnce? (Silmaril.Wasm.Game.importStore []) M [] =
      some (S, f, none)) :
    ∃ p : Silmaril.Wasm.Lime1.Execution.Prepared Nat,
      Silmaril.Wasm.Lime1.Execution.prepare? (residueStore l.globals vals) (residueL l)
        (residueImports l.globals.length) = some p ∧ p.start = [] := by
  have hdirR := Silmaril.Proofs.Wasm.Component.Lime1Inst.instantiateOnce_residue hret hvals hty hinst
  have hstR : M.globalResidue.start = none :=
    (Silmaril.Wasm.Execution.Core.instantiateDirect?_start hdirR).symm
  have hstL : (residueL l).start = none := by
    have h := congrArg Silmaril.Wasm.Module.start hret
    simpa [Lime1.Module.toCore, residueL, Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElems,
      Silmaril.Wasm.Module.globalResidue] using h.trans hstR
  obtain ⟨c₀, hp₀, -⟩ := Silmaril.Wasm.Execution.Core.prepareDirect?_frame hdirR
  have hseg := Silmaril.Proofs.Wasm.Component.Lime1Inst.initSegments_of_direct hdirR hp₀
  have hguard := Silmaril.Proofs.Wasm.Component.Lime1Inst.prepare?_guard hp₀
  obtain ⟨⟨A, mod⟩, hal0⟩ := allocate?_some (H := Nat) hv hlimp hvals
  have hal : Silmaril.Wasm.Lime1.Execution.allocate? (residueStore l.globals vals) (residueL l)
      (residueImports l.globals.length) = some (A, mod) :=
    (Silmaril.Proofs.Wasm.Component.Lime1Inst.allocate?_residue hvals).trans hal0
  have hes : M.elems.map funcrefElem = (residueL l).toCore.elems :=
    (Silmaril.Proofs.Wasm.Component.Lime1Inst.retract_elems hret).symm
  have hW : withElems (residueL l) M.elems = M.globalResidue :=
    Silmaril.Proofs.Wasm.Component.Lime1Inst.withElems_residue hret
  have hp₀' : Silmaril.Wasm.Execution.Core.prepare? evalConst?
      (residueStore (H := Nat) l.globals vals).toCore (withElems (residueL l) M.elems)
      ((residueImports l.globals.length).map ExternVal.toCore) = some (c₀, none) := by
    rw [hW]; exact hp₀
  have R : Rel c₀.store c₀.frame A mod := rel_of_prepare rfl hes hal hp₀'
  have hT2 : List.Forall₂ (fun g v => v.type = g.type.value) l.globals vals :=
    Silmaril.Proofs.Wasm.Component.Lime1Inst.forall₂_imp_mem (fun g hg v hgv => hty g hg v hgv)
      (Silmaril.Wasm.Lime1.Execution.mapM_forall₂ hvals)
  have hT := gTyped_residue hlimp hT2 hal
  have hvR := Silmaril.Proofs.Wasm.Component.Lime1Inst.residue_valid hv
  obtain ⟨S₁, hE, hD⟩ := initSegments_inv hseg
  have hEL : List.Forall₂ (fun (eL : Lime1.Elem) (eC : Silmaril.Wasm.Elem) =>
      funcrefElem eC = Lime1.Elem.toCore eL) l.elems M.elems :=
    forall₂_of_map_eq (Silmaril.Proofs.Wasm.Component.Lime1Inst.retract_elems hret)
  obtain ⟨hS₁, hEr⟩ := elemList_back R hT (funcs_residue hlimp hal) l.elems M.elems 0 c₀.store S₁
    hEL (fun e he => hvR.elements e he) (fun e he => hguard.2.2.2 e he) (Same.refl _) hE
  have hDM : M.globalResidue.data = l.data.map Lime1.Data.toCore :=
    (Silmaril.Proofs.Wasm.Component.Lime1Inst.retract_data hret).symm
  rw [hDM, List.length_map] at hD
  obtain ⟨-, hDr⟩ := dataList_back R hT l.data 0 S₁ S (fun d hd => hvR.data d hd)
    (fun d hd => hguard.2.2.1 _ (by rw [hDM]; exact List.mem_map_of_mem hd)) hS₁ hD
  obtain ⟨ws, hws⟩ := mapM_some (xs := (residueL l).elems) hEr
  obtain ⟨ds, hds⟩ := mapM_some (xs := (residueL l).data) hDr
  exact ⟨_, prepare?_of hal hws hds hstL, rfl⟩

/-- The engine's lookup of the exports by name succeeds. -/
theorem exportAddrs_some {M : Silmaril.Wasm.Module} {l : Lime1.Module}
    (hret : l.toCore = Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElems M)
    (hv : ModuleValid l) (hg : l.globals = [])
    {before : Silmaril.Wasm.Lime1.Execution.Store Nat}
    {p : Silmaril.Wasm.Lime1.Execution.Prepared Nat} {imports : List ExternVal}
    (hp : Silmaril.Wasm.Lime1.Execution.prepare? before l imports = some p) {exps : CoreIface}
    (hnames : funcExportNames M = exps.map (·.1)) :
    ∃ addrs, exportAddrs lime1 p.module exps = some addrs := by
  obtain ⟨allocated, -, -, hal, -, -, -⟩ := Silmaril.Wasm.Lime1.Execution.prepare?_inv hp
  obtain ⟨exports, -, hex, -, hmod, -⟩ := Silmaril.Wasm.Lime1.Execution.allocate?_inv hg hal
  have ⟨hn, hf⟩ := Silmaril.Proofs.Wasm.Component.Lime1Inst.allocExports_funcNames
    (Silmaril.Wasm.Lime1.Execution.mapM_forall₂ hex)
  have hpe : p.module.exports = exports := by rw [hmod]
  have hnd : (exports.map (·.name)).Nodup := by
    rw [hn]; exact hv.uniqueExports
  have hfn : Silmaril.Proofs.Wasm.Component.Lime1Inst.funcNames exports = exps.map (·.1) := by
    rw [hf, ← hnames]
    simp only [funcExportNames, Silmaril.Proofs.Wasm.Component.Lime1Inst.retract_exports hret]
  have hlk := Silmaril.Proofs.Wasm.Component.Lime1Inst.lookup_funcNames hnd
  rw [hfn, ← Silmaril.Proofs.Wasm.Component.Lime1Inst.mapM_fst] at hlk
  refine ⟨Silmaril.Proofs.Wasm.Component.Lime1Inst.funcAddrs exports, ?_⟩
  rw [← hlk, exportAddrs]
  simp only [Silmaril.Wasm.Component.Engine.Lime1.lime1, hpe]
  rfl

/-- The engine instance of an import-free module from a preparation without start function. -/
theorem instOf_of {m : Lime1.Module} {exps : CoreIface}
    {p : Silmaril.Wasm.Lime1.Execution.Prepared Nat}
    (hp : Silmaril.Wasm.Lime1.Execution.prepare? {} m [] = some p) (hst : p.start = [])
    {addrs : List lime1.FuncAddr} (ha : exportAddrs lime1 p.module exps = some addrs) :
    instOf lime1 m [] exps = some ⟨p.store, addrs⟩ := by
  simp only [instOf, allocHosts, Silmaril.Wasm.Component.Engine.Lime1.lime1,
    Silmaril.Wasm.Component.Engine.Lime1.prepare?, List.map_nil, hp, Option.map_some, hst,
    Silmaril.Wasm.Component.Engine.Lime1.startAddr?]
  rw [show exportAddrs _ p.module exps = some addrs from ha]
  rfl

/-- **The Lime1 engine instantiates every module of the Lime1 domain that has a Core 3.0
instance** (`Lime1RefE.Lime1InstOk`). -/
theorem lime1Inst_proof : Silmaril.Wasm.Component.Lime1RefE.Lime1InstOk := by
  intro c hD _ hi
  obtain ⟨l, hl, hv⟩ := hD
  have hret := Silmaril.Proofs.Wasm.Component.Lime1Inst.module_retract hl
  have hofl : ofCoreL c.mod.mod = l := by simp only [ofCoreL, hl, Option.getD_some]
  obtain ⟨I', ⟨mt, hIs⟩, himp, -⟩ := hi.inst
  obtain ⟨hmt, hMimp⟩ := Silmaril.Proofs.Wasm.Component.Lime1Inst.isInst_imports hIs himp
  have hlimp : l.imports = [] := by
    simpa only [hMimp, List.map_eq_nil_iff] using
      Silmaril.Proofs.Wasm.Component.Lime1Inst.retract_imports hret
  obtain ⟨f, hinst, -⟩ := hIs.instantiated
  have hinst0 : Silmaril.Wasm.Execution.Core.instantiateOnce? (Silmaril.Wasm.Game.importStore [])
      c.mod.mod [] = some (I'.store, f, none) := by
    simpa only [hmt, Silmaril.Wasm.Validation.CExternType.funcs, List.length_nil,
      List.range_zero, List.map_nil] using hinst
  obtain ⟨vals, hvals⟩ := globals_of_core hret hv hlimp hinst0
  have hty : ∀ g ∈ l.globals, ∀ v, Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init = some v → v.type = g.type.value :=
    fun g hg v hgv => Silmaril.Proofs.Wasm.Component.Lime1Inst.constExpr?_type rfl
      (hv.globals g hg).typed hgv
  obtain ⟨p, hpR, hst⟩ := residue_prepare hret hv hlimp hvals hty hinst0
  have hp : Silmaril.Wasm.Lime1.Execution.prepare? {} l [] = some p :=
    (Silmaril.Proofs.Wasm.Component.Lime1Inst.prepare?_residue hvals).symm.trans hpR
  obtain ⟨addrs, ha⟩ := exportAddrs_some
    (Silmaril.Proofs.Wasm.Component.Lime1Inst.residue_retract hret)
    (Silmaril.Proofs.Wasm.Component.Lime1Inst.residue_valid hv) rfl hpR hi.names
  rw [hofl]
  exact ⟨_, instOf_of hp hst ha⟩

end Silmaril.Proofs.Wasm.Component.Lime1Eng

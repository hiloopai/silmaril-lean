module

public import Silmaril.Proofs.Wasm.Component.Lime1Inst.Bridge
public import Silmaril.Proofs.Wasm.Component.Lime1Inst.Residue

/-!
# The Lime1 instantiation bridge with globals

`instantiateOnce?` runs `$evalglobals` and then the direct instantiation of the Core residue
`Module.globalResidue` against the allocated globals. On the Lime1 side the same split is
`prepare?_residue`. The two `$evalglobals` agree on typed initializers (`evalGlobals_core`), the
Core residue is the image of the Lime1 residue (`residue_core`), and `prepare_runP` relates the
two residue preparations without validity of the residue. The segment run is computed by the
executable `initSegments?` (complete at `profile o` on offsets that `ModuleOk` of the module
types, `Silmaril.Proofs.Wasm.Instantiation.isOffset_exprOkConst`).

* **`instBridgeE_proof`**: `Lime1Bridge.InstBridgeE`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Inst

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Lime1Ref Silmaril.Wasm.Component.Lime1Bridge
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)
open Silmaril.Wasm.Lime1.Execution (Prepared)

/-- A successful Lime1 allocation without imports evaluates every global initializer. -/
theorem allocate?_vals {H : Type} {s : Silmaril.Wasm.Lime1.Execution.Store H}
    {m : Silmaril.Wasm.Lime1.Module} {r : Silmaril.Wasm.Lime1.Execution.Store H ×
      Silmaril.Wasm.Execution.Runtime.ModuleInst}
    (h : Silmaril.Wasm.Lime1.Execution.allocate? s m [] = some r) :
    ∃ vals, m.globals.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr? s {} g.init) =
      some vals := by
  simp only [Silmaril.Wasm.Lime1.Execution.allocate?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨vals, hv, -⟩ := h
  exact ⟨vals, hv⟩

/-- The image of the Lime1 residue is the Core residue, up to element types. -/
theorem residue_retract {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) :
    (residueL l).toCore = funcrefElems M.globalResidue := by
  rcases M with ⟨ty, im, tg, gl, me, ta, fu, da, el, st, ex⟩
  simp only [Silmaril.Wasm.Lime1.Module.toCore, funcrefElems, Silmaril.Wasm.Module.mk.injEq] at hret
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hret
  simp only [residueL, Silmaril.Wasm.Lime1.Module.toCore, funcrefElems,
    Silmaril.Wasm.Module.globalResidue, h1, ← h2, ← h3, ← h4, h5, h6, h7, h8, h9, h10, h11,
    List.map_append, List.map_map, List.map_nil]
  rfl

theorem withElems_residue {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) : withElems (residueL l) M.elems = M.globalResidue :=
  withElems_retract (residue_retract hret)

/-- The closed global types and initializers of the Core image of Lime1 globals. -/
theorem globals_image {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) :
    Silmaril.Wasm.Execution.Core.Module.closedGlobalTypes M =
        l.globals.map (fun g => ⟨g.type.mutability, .num g.type.value⟩) ∧
      M.globals.map Silmaril.Wasm.Global.init = l.globals.map fun g =>
        Silmaril.Wasm.Lime1.Expr.toCore g.init := by
  rw [Silmaril.Wasm.Execution.Core.Module.closedGlobalTypes, ← retract_globals hret]
  simp only [List.map_map]
  exact ⟨rfl, rfl⟩

/-- The Lime1 residue store, in Core, is the store left by `$evalglobals` from no imports. -/
theorem residueStore_toCore (gs : List Silmaril.Wasm.Lime1.Global)
    (vals : List Silmaril.Wasm.Execution.Runtime.Value) :
    (residueStore (H := Nat) gs vals).toCore =
      { (Silmaril.Wasm.Game.importStore []) with globals := ((Silmaril.Wasm.Game.importStore []).globals ++
        (globalInsts gs vals).map Silmaril.Wasm.Execution.Runtime.GlobalInst.toCore) } := rfl

theorem residueImports_toCore (k : Nat) :
    (residueImports k).map Silmaril.Wasm.Execution.Runtime.ExternVal.toCore =
      [] ++ Silmaril.Wasm.Execution.Core.globalAddrs 0 k := by
  simp [residueImports, Silmaril.Wasm.Execution.Core.globalAddrs, Function.comp_def,
    Silmaril.Wasm.Execution.Runtime.ExternVal.toCore]

/-- The size guard of a successful executable preparation. -/
theorem prepare?_guard {H : Type} {ev : Silmaril.Wasm.Execution.Core.Store H →
      Silmaril.Wasm.Execution.Core.Frame → Silmaril.Wasm.Expr →
        Option (Silmaril.Wasm.Execution.Core.Store H × Silmaril.Wasm.Execution.Core.Val)}
    {s : Silmaril.Wasm.Execution.Core.Store H} {m : Silmaril.Wasm.Module}
    {xas : List Silmaril.Wasm.Execution.Core.ExternAddr}
    {r : Silmaril.Wasm.Execution.Core.Config H × Option Silmaril.Wasm.FuncIdx}
    (h : Silmaril.Wasm.Execution.Core.prepare? ev s m xas = some r) :
    m.elems.length ≤ 2 ^ 32 ∧ m.data.length ≤ 2 ^ 32 ∧
      (∀ d ∈ m.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ m.elems, e.init.length < 2 ^ 32) := by
  unfold Silmaril.Wasm.Execution.Core.prepare? at h
  split at h
  · assumption
  · cases h

theorem forall₂_imp_mem {α β : Type _} {R S : α → β → Prop} {l₁ : List α}
    (h : ∀ a ∈ l₁, ∀ b, R a b → S a b) : ∀ {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, .nil => .nil
  | _, .cons hr hrs => .cons (h _ (by simp) _ hr)
      (forall₂_imp_mem (fun a ha b hab => h a (by simp [ha]) b hab) hrs)

theorem importsMatch_globals {H : Type} {S : Silmaril.Wasm.Lime1.Execution.Store H}
    {types : List Silmaril.Wasm.V1.FuncType} :
    ∀ {gs : List Silmaril.Wasm.Lime1.Global} {vals : List Silmaril.Wasm.Execution.Runtime.Value}
      (n : Nat), List.Forall₂ (fun g v => v.type = g.type.value) gs vals →
      (∀ i, i < gs.length → S.globals[n + i]? = (globalInsts gs vals)[i]?) →
      List.Forall₂ (fun i e => ∃ et, Silmaril.Wasm.Lime1.Validation.importType? types i.desc =
          some et ∧ Silmaril.Wasm.Lime1.Execution.ExternMatches S e et)
        (gs.map fun g => (⟨"", "", .global g.type⟩ : Silmaril.Wasm.V1.Import))
        ((List.range' n gs.length).map fun i => .global ⟨i⟩)
  | [], [], _, .nil, _ => .nil
  | g :: gs, v :: vals, n, .cons hv hvs, hS => by
    have h0 : S.globals[n]? = some ⟨v, g.type.mutability⟩ := by
      simpa [globalInsts] using hS 0 (by simp)
    have hrest : ∀ i, i < gs.length → S.globals[n + 1 + i]? = (globalInsts gs vals)[i]? := by
      intro i hi
      have h := hS (i + 1) (by simpa using hi)
      simpa [globalInsts, Nat.add_assoc, Nat.add_comm 1 i] using h
    refine .cons ⟨_, rfl, .global ⟨n⟩ _ g.type h0 hv rfl⟩ ?_
    exact importsMatch_globals (n + 1) hvs hrest

/-- The residue's global imports are matched by the evaluated globals, typed initializers. -/
theorem importsMatch_residue {l : Silmaril.Wasm.Lime1.Module} (hlimp : l.imports = [])
    {vals : List Silmaril.Wasm.Execution.Runtime.Value}
    (hvals : l.globals.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init) = some vals)
    (hty : ∀ g ∈ l.globals, ∀ v, Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init = some v → v.type = g.type.value) :
    Silmaril.Wasm.Lime1.Execution.ImportsMatch (residueStore (H := Nat) l.globals vals)
      (residueL l) (residueImports l.globals.length) := by
  have h2 := Silmaril.Wasm.Lime1.Execution.mapM_forall₂ hvals
  have hT : List.Forall₂ (fun g v => v.type = g.type.value) l.globals vals :=
    forall₂_imp_mem (fun g hg v hgv => hty g hg v hgv) h2
  have hS : ∀ i, i < l.globals.length → (residueStore (H := Nat) l.globals vals).globals[0 + i]? =
      (globalInsts l.globals vals)[i]? := fun i _ => by rw [Nat.zero_add]; rfl
  have hm := importsMatch_globals (types := (residueL l).types) 0 hT hS
  unfold Silmaril.Wasm.Lime1.Execution.ImportsMatch
  simpa only [residueL, hlimp, List.nil_append, residueImports, List.range_eq_range'] using hm

/-- `evalConst?` is complete on the offsets of the residue at `profile o`, from validity of the
module, at a frame of the module's allocated types. -/
theorem offsets_complete {o : Silmaril.Wasm.SingleThreaded.GrowOracle} {M : Silmaril.Wasm.Module}
    {xtI xtE : List Silmaril.Wasm.Validation.CExternType}
    (hok : Silmaril.Wasm.Validation.ModuleOk M ⟨xtI, xtE⟩) {F : Silmaril.Wasm.Execution.Core.Frame}
    (hF : F.module.types = Silmaril.Wasm.Execution.Core.allocTypes M.types) :
    ∀ e, Silmaril.Wasm.Instantiation.IsOffset M.globalResidue e →
      Silmaril.Wasm.Instantiation.OffsetCompleteAt o
        (Silmaril.Wasm.Execution.Core.evalConst? (H := Nat)) F e := by
  obtain ⟨C, hCT, hoff⟩ := Silmaril.Proofs.Wasm.Instantiation.isOffset_exprOkConst hok
  intro e he
  obtain ⟨t, het⟩ := hoff e he
  exact fun _ _ _ _ hx =>
    Silmaril.Wasm.Execution.Core.evalConst?_of_exprOkConst het (hF.trans hCT.symm) hx

/-- The segment initialisation of a successful direct preparation. -/
theorem initSegments_of_direct {H : Type}
    {ev : Silmaril.Wasm.Execution.Core.Store H → Silmaril.Wasm.Execution.Core.Frame →
      Silmaril.Wasm.Expr →
        Option (Silmaril.Wasm.Execution.Core.Store H × Silmaril.Wasm.Execution.Core.Val)}
    {s s' : Silmaril.Wasm.Execution.Core.Store H} {m : Silmaril.Wasm.Module}
    {xas : List Silmaril.Wasm.Execution.Core.ExternAddr} {f' : Silmaril.Wasm.Execution.Core.Frame}
    {st st₀ : Option Silmaril.Wasm.FuncIdx} {c : Silmaril.Wasm.Execution.Core.Config H}
    (h : Silmaril.Wasm.Execution.Core.prepareDirect? ev s m xas = some (s', f', st))
    (hp : Silmaril.Wasm.Execution.Core.prepare? ev s m xas = some (c, st₀)) :
    Silmaril.Wasm.Execution.Core.initSegments? ev c.store c.frame m = some (s', f') := by
  unfold Silmaril.Wasm.Execution.Core.prepareDirect? at h
  rw [hp] at h
  dsimp only at h
  split at h
  · cases h
  · rename_i s₁ f₁ hi
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact hi

/-- The residue instantiation of `instantiateOnce?`, for the image of a Lime1 module whose
initializers evaluate, typed, to `vals`. -/
theorem instantiateOnce_residue {M : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (hret : l.toCore = funcrefElems M) {vals : List Silmaril.Wasm.Execution.Runtime.Value}
    (hvals : l.globals.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init) = some vals)
    (hty : ∀ g ∈ l.globals, ∀ v, Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init = some v → v.type = g.type.value)
    {r : Silmaril.Wasm.Execution.Core.Store Nat × Silmaril.Wasm.Execution.Core.Frame ×
      Option Silmaril.Wasm.FuncIdx}
    (h : Silmaril.Wasm.Execution.Core.instantiateOnce? (Silmaril.Wasm.Game.importStore []) M [] =
      some r) :
    Silmaril.Wasm.Execution.Core.instantiateDirect? (residueStore (H := Nat) l.globals vals).toCore
      M.globalResidue ((residueImports l.globals.length).map
        Silmaril.Wasm.Execution.Runtime.ExternVal.toCore) = some r := by
  obtain ⟨hgt, hgi⟩ := globals_image hret
  obtain ⟨F', hEG⟩ := evalGlobals_core (H' := Nat) hvals hty (Silmaril.Wasm.Game.importStore [])
    ⟨[], Silmaril.Wasm.Execution.Core.ModuleInst.initial (Silmaril.Wasm.Game.importStore []) M []⟩
  have hlen : M.globals.length = l.globals.length := by
    rw [← retract_globals hret, List.length_map]
  unfold Silmaril.Wasm.Execution.Core.instantiateOnce? at h
  rw [hgt, hgi, hEG] at h
  rw [residueStore_toCore, residueImports_toCore, ← hlen]
  exact h

/-- The Lime1 residue store is well formed and has small tables. -/
theorem residueStore_wf (gs : List Silmaril.Wasm.Lime1.Global)
    (vals : List Silmaril.Wasm.Execution.Runtime.Value) :
    Silmaril.Wasm.Lime1.Execution.StoreWF (residueStore (H := Nat) gs vals) ∧
      ∀ t ∈ (residueStore (H := Nat) gs vals).tables, t.refs.length < 2 ^ 32 :=
  ⟨⟨fun _ _ _ _ h => by simp [residueStore] at h, fun _ _ h => by simp [residueStore] at h⟩,
    by simp [residueStore]⟩

/-- The Lime1 side of a component in the Lime1 domain whose module has an instance: the
decoding, its preparation, its residue preparation and the typed initializer values. -/
theorem lime1Side {l : Silmaril.Wasm.Lime1.Module}
    (hv : Silmaril.Wasm.Lime1.Validation.ModuleValid l) {p : Prepared Nat}
    (hp : Silmaril.Wasm.Lime1.Execution.prepare? {} l [] = some p) :
    ∃ vals, l.globals.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr?
        ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init) = some vals ∧
      (∀ g ∈ l.globals, ∀ v, Silmaril.Wasm.Lime1.Execution.constExpr?
        ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init = some v →
          v.type = g.type.value) ∧
      Silmaril.Wasm.Lime1.Execution.prepare? (residueStore l.globals vals) (residueL l)
        (residueImports l.globals.length) = some p := by
  obtain ⟨allocated, -, -, hal, -, -, -⟩ := Silmaril.Wasm.Lime1.Execution.prepare?_inv hp
  obtain ⟨vals, hvals⟩ := allocate?_vals hal
  have hty : ∀ g ∈ l.globals, ∀ v, Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store Nat) {} g.init = some v → v.type = g.type.value :=
    fun g hg v hgv => constExpr?_type rfl (hv.globals g hg).typed hgv
  exact ⟨vals, hvals, hty, (prepare?_residue hvals).trans hp⟩

/-- **`Lime1Bridge.InstBridgeE` holds** (parts (a), (b) and (c)). -/
theorem instBridgeE_proof : InstBridgeE := by
  intro c hD _ hi I hI
  obtain ⟨l, hl, hv⟩ := hD
  have hret : l.toCore = funcrefElems c.mod.mod := module_retract hl
  have hofl : ofCoreL c.mod.mod = l := by simp only [ofCoreL, hl, Option.getD_some]
  obtain ⟨I', ⟨mt, hIs⟩, himp, hexp⟩ := hi.inst
  obtain ⟨hmt, hMimp⟩ := isInst_imports hIs himp
  have hlimp : l.imports = [] := by
    simpa only [hMimp, List.map_eq_nil_iff] using retract_imports hret
  have hI0 : instOf lime1 l [] c.mod.exports = some I := hofl ▸ hI
  obtain ⟨p, hp, hpa, hIst⟩ := instOf_inv hI0
  obtain ⟨vals, hvals, hty, hpR⟩ := lime1Side hv hp
  obtain ⟨f, hinst, haddrs⟩ := hIs.instantiated
  have hinst0 : Silmaril.Wasm.Execution.Core.instantiateOnce? (Silmaril.Wasm.Game.importStore [])
      c.mod.mod [] = some (I'.store, f, none) := by
    simpa only [hmt, Silmaril.Wasm.Validation.CExternType.funcs, List.length_nil,
      List.range_zero, List.map_nil] using hinst
  have hdirR := instantiateOnce_residue hret hvals hty hinst0
  have hst : c.mod.mod.start = none :=
    (Silmaril.Wasm.Execution.Core.instantiateDirect?_start hdirR).symm
  obtain ⟨c₀, hp₀, -⟩ := Silmaril.Wasm.Execution.Core.prepareDirect?_frame hdirR
  obtain ⟨hwfR, htabR⟩ := residueStore_wf l.globals vals
  have boundsR := bounds_gen (residue_retract hret) rfl hwfR htabR (prepare?_guard hp₀)
  have hvR := residue_valid hv
  obtain ⟨cR, S, hprep, hcode, hsteps, hS, hsim, htypes⟩ := prepare_runP
    (P := Silmaril.Wasm.SingleThreaded.profile (fun _ _ _ _ => false))
    (tgt := Silmaril.Wasm.SingleThreaded.Det.noHost) (m := residueL l) (es := c.mod.mod.elems)
    (retract_elems hret).symm boundsR hvR hpR
  rw [withElems_residue hret] at hprep hcode htypes
  have hseg := initSegments_of_direct hdirR hprep
  have hsc : Silmaril.Wasm.Lime1.Execution.startCode (residueL l).toCore = [] := by
    simp only [Silmaril.Wasm.Lime1.Execution.startCode,
      congrArg Silmaril.Wasm.Module.start (residue_retract hret), funcrefElems,
      Silmaril.Wasm.Module.globalResidue, hst]
  have hrun : Silmaril.Wasm.Execution.Core.Steps
      (Silmaril.Wasm.SingleThreaded.profile (fun _ _ _ _ => false))
      Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨cR.store, cR.frame, Silmaril.Wasm.Instantiation.initCode c.mod.mod.globalResidue⟩
      ⟨S, cR.frame, []⟩ := by
    rw [← hcode, ← List.append_nil cR.code, ← hsc]; exact hsteps
  have hok : Silmaril.Wasm.Validation.ModuleOk c.mod.mod ⟨mt.imports, mt.exports⟩ :=
    Silmaril.Wasm.Validation.validate?_sound hIs.valid
  have hseg' := Silmaril.Wasm.Instantiation.initSegments?_completeAt
    (offsets_complete hok htypes) hrun
  have heq : (I'.store, f) = (S, cR.frame) := Option.some.inj (hseg.symm.trans hseg')
  have hSI : I'.store = S := congrArg Prod.fst heq
  have hfF : f = cR.frame := congrArg Prod.snd heq
  have hwf : Silmaril.Wasm.Lime1.Execution.StoreWF p.store :=
    (Silmaril.Wasm.Lime1.Execution.prepare_wf boundsR hvR
      (importsMatch_residue hlimp hvals hty) hpR).1
  have hA := exportAddrs_eq (residue_retract hret) hvR rfl hpR hi.names hpa
  have hex : cR.frame.module.exports = p.module.exports.map fun e => ⟨e.name, e.value.toCore⟩ :=
    congrArg Silmaril.Wasm.Execution.Core.ModuleInst.exports hsim
  have hA' : I'.addrs = (funcAddrs p.module.exports).map (·.value) := by
    rw [← haddrs, hfF]; exact exportFuncAddrs_of_exports hex
  have hlen : I'.store.funcs.length = I.store.funcs.length := by
    have h := congrArg (fun s => s.funcs.length) hS
    simpa only [Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase,
      Silmaril.Wasm.Execution.Runtime.Store.toCore, List.length_map, ← hSI, ← hIst] using h
  have hty' : ∀ (k a : Nat), I'.addrs[k]? = some a → a < I'.store.funcs.length := fun k a hk => by
    obtain ⟨_, -, fi, hfi, -⟩ := Silmaril.Wasm.Lime1.Execution.forall₂_getElem? hIs.exportTypes hk
    exact (List.getElem?_eq_some_iff.mp hfi).1
  refine ⟨I', ⟨⟨mt, hIs⟩, himp, hexp⟩, hIst ▸ hwf, ?_, exportsSim hA hA' hlen hty'⟩
  rw [hSI, hIst]; exact hS

end Silmaril.Proofs.Wasm.Component.Lime1Inst

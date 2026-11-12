module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.Bridge
public import Silmaril.Wasm.Versions.Thms
-- Hand copy: source namespaces kept, only import lines rewritten
-- (imports of other topics' Raw modules go through their public headers).

/-! # Core instantiation of the binary-faithful image (`toCoreBinary`)

`prepare_core` for `m.toCoreBinary`: Core instantiation followed by the segment
programs reaches the start code on a store whose erasure is the image of the
prepared Lime1 store. The element types of `m.toCoreBinary` (`(ref func)`) only
appear in the TYPE field of the allocated element instances, which the segment
programs (`table.init`/`elem.drop`) never read and `ToCore.Store.erase` forgets.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution (Runtime.Result Runtime.ExternVal Runtime.ModuleInst Runtime.ExportInst
  Runtime.FuncInst Runtime.TableInst Runtime.MemInst Runtime.GlobalInst)
open Silmaril.Wasm.Execution.Runtime (Value Value.toCore GlobalInst GlobalInst.toCore)

variable {H : Type}

theorem elems_toCoreBinary_init (es : List Elem) :
    (es.map Elem.toCoreBinary).map Wasm.Elem.init = (es.map Elem.toCore).map Wasm.Elem.init := by
  simp only [List.map_map]
  rfl

theorem runElems_toCoreBinary (k : Nat) (es : List Elem) :
    ((List.range' k es.length).zip (es.map Elem.toCoreBinary)).flatMap
        (fun (p : Nat × Wasm.Elem) => Silmaril.Wasm.Execution.Core.runElem p.1 p.2) =
      ((List.range' k es.length).zip (es.map Elem.toCore)).flatMap
        (fun (p : Nat × Wasm.Elem) => Silmaril.Wasm.Execution.Core.runElem p.1 p.2) := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
    simp only [List.length_cons, List.range'_succ, List.map_cons, List.zip_cons_cons,
      List.flatMap_cons]
    rw [ih]
    rfl

/-- `instantiate_valid` for the binary-faithful image. -/
theorem instantiate_valid_binary {before : Store H} {m : Module}
    {imports : List Runtime.ExternVal} (bounds : InstantiationBounds before m)
    (hv : Validation.ModuleValid m) (hi : ImportsMatch before m imports) :
    ∃ xtE xtI, Wasm.Validation.ModuleOk m.toCoreBinary ⟨xtI, xtE⟩ ∧
      List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk before.toCore)
        (imports.map Runtime.ExternVal.toCore) xtI := by
  obtain ⟨xtE, hok⟩ := Validation.ModuleValid.toCoreBinary_ok hv
  refine ⟨xtE, _, hok, ?_⟩
  have key : ∀ (imps : List Import) (es : List Runtime.ExternVal),
      (∀ i ∈ imps, Validation.ImportValid m.types i) →
      List.Forall₂ (fun i e => ∃ et, Validation.importType? m.types i.desc = some et ∧
        ExternMatches before e et) imps es →
      List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk before.toCore)
        (es.map Runtime.ExternVal.toCore) (imps.map fun i => Validation.importC m.types i.desc) := by
    intro imps es hvs hf
    induction hf with
    | nil => exact .nil
    | cons hh _ ih =>
      exact .cons (externAddrOk_import bounds.storeWF bounds.tables (hvs _ (by simp)) hh)
        (ih (fun i hi => hvs i (by simp [hi])))
  exact key _ _ hv.imports hi

theorem allocModule_coreBinary {before : Store H} {m : Module} {imports : List Runtime.ExternVal}
    {exports : List Runtime.ExportInst} {funcs : List (Runtime.FuncInst Func H)}
    {refsE : List (List Silmaril.Wasm.Execution.Core.Ref)}
    (hg : m.globals = [])
    (hex : m.exports.mapM (fun e => (exportValue? (baseInst before m imports) e.index).bind
      fun v => some (⟨e.name, v⟩ : Runtime.ExportInst)) = some exports)
    (hfn : m.funcs.mapM (fun f => (m.types[f.type.toNat]?).bind
      fun ft => some (Runtime.FuncInst.wasm ft { baseInst before m imports with exports := exports } f)) =
        some funcs)
    (hlenE : refsE.length = m.elems.length) :
    ∃ Sa mi, Silmaril.Wasm.Execution.Core.allocModule? before.toCore m.toCoreBinary
        (imports.map Runtime.ExternVal.toCore) [] (m.tables.map fun _ => .null) refsE =
        some (Sa, mi) ∧
      ToCore.ModuleInst.erase mi =
        ({ baseInst before m imports with exports := exports } : Runtime.ModuleInst).toCore ∧
      mi.elems = List.range m.elems.length ∧ mi.datas = List.range m.data.length ∧
      Sa.elems.map (·.refs) = refsE ∧ Sa.datas.map (·.bytes) = m.data.map (·.bytes) ∧
      Sa.globals = before.toCore.globals ∧
      ToCore.Store.erase Sa = (⟨before.funcs ++ funcs, before.tables ++ m.tables.map (fun t =>
          Runtime.TableInst.mk (List.replicate t.limits.min.val none) (t.limits.max.map Fin.val)),
        before.memories ++ m.memories.map (fun t => Runtime.MemInst.mk
          ⟨Array.replicate (t.limits.min.val * Silmaril.Wasm.Execution.Memory.pageSize) 0⟩
          (t.limits.max.map Fin.val)),
        before.globals⟩ : Store H).toCore := by
  have hT : Silmaril.Wasm.Execution.Core.allocTypes (m.types.map V1.FuncType.toCoreRec) =
      m.types.map V1.FuncType.toDefType :=
    Silmaril.Wasm.Execution.Core.allocTypes_eq (Validation.typesOk_map m.types {})
  have hfn2 := mapM_forall₂ hfn
  have hF := funcTypes_eq hfn2
  simp only [Silmaril.Wasm.Execution.Core.allocModule?, Module.toCoreBinary, Module.toCore, hg, hT, hF,
    List.mapM_nil, List.map_nil, List.zip_nil_right, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, allocMany_nil', allocMany_mem, allocMany_table, allocMany_data,
    allocMany_elem, allocMany_func]
  rw [allocExports_eq (base := baseInst before m imports) ?_ ?_ ?_ ?_ m.exports exports hex]
  rotate_left
  · simp [baseInst, externAddr_funcs_toCore, addresses, Silmaril.Wasm.Execution.Runtime.Store.toCore,
      Function.comp_def]
  · simp [baseInst, externAddr_tables_toCore, addresses, Silmaril.Wasm.Execution.Runtime.Store.toCore,
      Function.comp_def]
  · simp [baseInst, externAddr_mems_toCore, addresses, Silmaril.Wasm.Execution.Runtime.Store.toCore,
      Function.comp_def]
  · simp [baseInst, externAddr_globals_toCore]
  simp only [Option.bind_some]
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore, baseInst,
      externAddr_funcs_toCore, externAddr_tables_toCore, externAddr_mems_toCore,
      externAddr_globals_toCore, externAddr_tags_toCore, addresses,
      Silmaril.Wasm.Execution.Runtime.Store.toCore, Function.comp_def]
  · simp [Silmaril.Wasm.Execution.Runtime.Store.toCore, hlenE]
  · simp [Silmaril.Wasm.Execution.Runtime.Store.toCore]
  · simp only [Silmaril.Wasm.Execution.Runtime.Store.toCore, List.nil_append, List.map_map]
    exact List.map_snd_zip (by simp [hlenE])
  · simp [Silmaril.Wasm.Execution.Runtime.Store.toCore, Function.comp_def, Data.toCore]
  · simp only [ToCore.Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toCore, List.map_append,
      funcs_before_erase, globals_before_erase, tables_new_toCore, mems_new_toCore]
    rw [funcs_new_toCore ?_ hfn2]
    simp [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore, baseInst,
      externAddr_funcs_toCore, externAddr_tables_toCore, externAddr_mems_toCore,
      externAddr_globals_toCore, externAddr_tags_toCore, addresses,
      Function.comp_def]

theorem prepare_coreBinary {tgt : ToCore.CHostSemantics H} {before : Store H} {m : Module}
    {imports : List Runtime.ExternVal} {p : Prepared H}
    (bounds : InstantiationBounds before m) (hv : Validation.ModuleValid m)
    (hi : ImportsMatch before m imports) (hp : prepare? before m imports = some p) :
    ∃ c S, Silmaril.Wasm.Execution.Core.Instantiate coreProfile tgt before.toCore m.toCoreBinary
        (imports.map Runtime.ExternVal.toCore) c ∧
      Silmaril.Wasm.Execution.Core.Steps coreProfile tgt c ⟨S, c.frame, startCode m.toCore⟩ ∧
      ToCore.Store.erase S = p.store.toCore ∧ ToCore.ModuleInstSim p.module c.frame.module ∧
      c.frame.locals = [] := by
  have hg := bounds.noGlobals
  obtain ⟨allocated, elems, data, ha, he, hd, hst⟩ := prepare?_inv hp
  obtain ⟨exports, funcs, hex, hfn, hmod, halloc⟩ := allocate?_inv hg ha
  have he2 := mapM_forall₂ he
  have hd2 := mapM_forall₂ hd
  obtain ⟨Sa, mi, hAM, hmi, hmiE, hmiD, hSaE, hSaD, hSaG, hSaS⟩ :=
    allocModule_coreBinary (refsE := elems.map elemRefs) hg hex hfn
      (by rw [List.length_map]; exact he2.length_eq.symm)
  -- the frame module
  have hFg : mi.globals = p.module.globals.map (·.value) := by
    have := congrArg (·.globals) hmi
    rw [hmod]
    simpa [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore] using this
  have hFt : mi.tables = p.module.tables.map (·.value) := by
    have := congrArg (·.tables) hmi
    rw [hmod]
    simpa [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore] using this
  have hFm : mi.mems = p.module.memories.map (·.value) := by
    have := congrArg (·.mems) hmi
    rw [hmod]
    simpa [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore] using this
  -- the initial store
  have hG0 : Sa.globals = allocated.globals.map GlobalInst.toCore := by
    rw [hSaG, halloc]; rfl
  have hS0 : ToCore.Store.erase Sa = allocated.toCore := by rw [hSaS, halloc]
  have htab : ∀ t ∈ allocated.tables, t.refs.length < 2 ^ 32 := by
    rw [halloc]
    intro t ht
    simp only [List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨tt, -, rfl⟩
    · exact bounds.tables t ht
    · simp only [List.length_replicate]; exact tt.limits.min.isLt
  have hmem : ∀ t ∈ allocated.memories, t.data.size ≤ 2 ^ 32 := by
    rw [halloc]
    intro t ht
    simp only [List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨mt, hmt, rfl⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
      exact (bounds.storeWF.2 i t hi).1
    · have hvt := (hv.memories mt hmt).1
      simp only [ByteArray.size, Array.size_replicate, Silmaril.Wasm.Execution.Memory.pageSize]
      omega
  -- element segments
  obtain ⟨S1, h1, hS1, hG1, hD1, -⟩ := elemLoop_core (P := coreProfile) (tgt := tgt)
    (F := { module := mi }) hFg hFt htab m.elems elems 0 Sa allocated he2
    (by simpa using bounds.elemCount)
    (fun i hi => by simp [hmiE, List.getElem?_range hi])
    (fun i hi => by
      have := congrArg (·[i]?) hSaE
      simpa [List.getElem?_map] using this)
    hG0 hS0 (fun _ => rfl)
    (Silmaril.Wasm.Execution.Core.expression
      (((List.range' 0 m.data.length).zip (m.data.map Data.toCore)).flatMap fun (i, d) =>
        Silmaril.Wasm.Execution.Core.runData i d) ++ startCode m.toCore)
  -- data segments
  obtain ⟨S2, h2, hS2⟩ := dataLoop_core (P := coreProfile) (tgt := tgt)
    (F := { module := mi }) hFg hFm hmem m.data data 0 S1 (elems.foldl applyElem allocated) hd2
    bounds.data (by simpa using bounds.dataCount)
    (fun i hi => by simp [hmiD, List.getElem?_range hi])
    (fun i hi => by
      have := congrArg (·[i]?) hSaD
      rw [hD1]
      simpa [List.getElem?_map] using this)
    (hG1.trans hG0) hS1 (fun i => by rw [foldl_applyElem_memories]) (startCode m.toCore)
  have hinst : Silmaril.Wasm.Execution.Core.Instantiate coreProfile tgt before.toCore m.toCoreBinary
      (imports.map Runtime.ExternVal.toCore) ⟨Sa, { module := mi },
        Silmaril.Wasm.Execution.Core.expression
          (((List.range m.toCoreBinary.elems.length).zip m.toCoreBinary.elems).flatMap fun (i, e) =>
            Silmaril.Wasm.Execution.Core.runElem i e) ++
        Silmaril.Wasm.Execution.Core.expression
          (((List.range m.toCoreBinary.data.length).zip m.toCoreBinary.data).flatMap fun (i, d) =>
            Silmaril.Wasm.Execution.Core.runData i d) ++
        (match m.toCoreBinary.start with | some x => [.plain (.call x)] | none => [])⟩ := by
    refine ⟨instantiate_valid_binary bounds hv hi,
      ⟨by simpa [Module.toCoreBinary, Module.toCore] using bounds.elemCount,
      by simpa [Module.toCoreBinary, Module.toCore] using bounds.dataCount,
      by simpa [Module.toCoreBinary, Module.toCore, Data.toCore] using bounds.data,
      by simpa [Module.toCoreBinary, Elem.toCoreBinary, Module.toCore, Elem.toCore]
        using bounds.elemSize⟩, ?_⟩
    let mi0 := Silmaril.Wasm.Execution.Core.ModuleInst.initial before.toCore m.toCoreBinary
      (imports.map Runtime.ExternVal.toCore)
    let f0 : ToCore.CFrame := { module := mi0 }
    refine ⟨before.toCore, before.toCore, before.toCore, Sa, f0, f0, f0, [],
      m.tables.map fun _ => .null, elems.map elemRefs, mi, ?_, ?_, ?_, hAM, rfl⟩
    · simp only [Module.toCoreBinary, Module.toCore, hg, List.map_nil]; exact .nil
    · exact evalExprs_tables _ _ m.tables
    · have hf0 : (Silmaril.Wasm.Execution.Core.ModuleInst.initial before.toCore m.toCoreBinary
          (imports.map Runtime.ExternVal.toCore)).funcs = p.module.funcs.map (·.value) := by
        rw [hmod]
        simp [Silmaril.Wasm.Execution.Core.ModuleInst.initial, baseInst, externAddr_funcs_toCore,
          addresses, Silmaril.Wasm.Execution.Runtime.Store.toCore, Module.toCoreBinary,
          Module.toCore, Function.comp_def]
      show Silmaril.Wasm.Execution.Core.EvalExprss coreProfile tgt _ _
        ((m.elems.map Elem.toCoreBinary).map Wasm.Elem.init) _ _ _
      rw [elems_toCoreBinary_init]
      exact evalExprss_elems _ f0 hf0 he2
  refine ⟨_, S2, hinst, ?_, ?_, ?_, rfl⟩
  · have e1 : Silmaril.Wasm.Execution.Core.expression
          (((List.range m.toCoreBinary.elems.length).zip m.toCoreBinary.elems).flatMap fun (i, e) =>
            Silmaril.Wasm.Execution.Core.runElem i e) ++
        Silmaril.Wasm.Execution.Core.expression
          (((List.range m.toCoreBinary.data.length).zip m.toCoreBinary.data).flatMap fun (i, d) =>
            Silmaril.Wasm.Execution.Core.runData i d) ++
        (match m.toCoreBinary.start with | some x => [.plain (.call x)] | none => []) =
        Silmaril.Wasm.Execution.Core.expression
          (((List.range' 0 m.elems.length).zip (m.elems.map Elem.toCore)).flatMap fun (i, e) =>
            Silmaril.Wasm.Execution.Core.runElem i e) ++
        (Silmaril.Wasm.Execution.Core.expression
          (((List.range' 0 m.data.length).zip (m.data.map Data.toCore)).flatMap fun (i, d) =>
            Silmaril.Wasm.Execution.Core.runData i d) ++ startCode m.toCore) := by
      simp only [Module.toCoreBinary, Module.toCore, List.length_map, List.range_eq_range',
        List.append_assoc, runElems_toCoreBinary]
      rfl
    show Silmaril.Wasm.Execution.Core.Steps coreProfile tgt ⟨Sa, { module := mi }, _⟩ _
    rw [e1]
    exact h1.trans h2
  · rw [hS2, hst]
  · show ToCore.ModuleInst.erase mi = p.module.toCore
    rw [hmod]; exact hmi

end Silmaril.Wasm.Lime1.Execution

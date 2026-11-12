module

public import Silmaril.Proofs.Wasm.LimeCompile.Direct.Sim
public import Silmaril.Proofs.Wasm.LimeCompile.Direct.Ident
public import Silmaril.Proofs.Wasm.LimeCompile.Direct.Typing
public import Silmaril.Wasm.Component.Lime1Inst.Thms

/-!
# The direct 3.0 → Lime compiler, first fragment: correctness

The compiler `compile` (`Silmaril.Wasm.LimeCompile.Direct.Defs`) rewrites typed `select`s at number
types to the untyped `select` and reads the result back as a Lime1 module. Its output is
interpreted in Core 3.0 through `Lime1.Module.toCore`, the module map of `lime1Emb`. Proofs in
`Silmaril.Proofs.Wasm.LimeCompile.Direct.{Sim,Ident,Typing}`.

* `lowerModule_valid`: the lowering of a valid module is valid, with the same module type;
* `lower_exportEquiv`: a valid module and its lowering are **exactly export-equivalent**
  (`ExportEquiv (· = ·)`: instantiation and every session of export invocations, by name) at
  every numerical profile and every code-parametric host;
* `compile_toCore`: a successful compilation is the lowering, read in Core
  (`l.toCore = lowerModule m`);
* `compile_valid`: the Core image of the output of a valid module validates;
* **`compile_correct`**: for a valid Core 3.0 module `m` with `compile m = some l`, `m` and
  `l.toCore` are exactly export-equivalent;
* `compile_api`: the API is kept exactly: the Core image of the output has the types, imports,
  exports, globals, memories, tables, segments and start function of `m`;
* `lowerL_length`: size data, one instruction for one instruction;
* `lowerModule_toCore`, **`compile_lime`**: the compiler is the identity on Lime1 modules
  (`compile l.toCore = some l`, for every Lime1 module `l`).

The restrictions of the fragment are those of `Lime1.Module.ofCore?`: `compile m = none` as soon
as `m` uses anything outside Lime1 other than a typed `select` at number types, in particular any
reference-typed function type, local, global or table beyond the implicit `funcref` table (see
`compile_none_of_types`): an API using 3.0-only types is not preserved, it is rejected.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Direct

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.LimeCompile.Direct

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **The lowering of a valid module is valid**, with the same module type. -/
theorem lowerModule_valid {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    ModuleOk (lowerModule m) mt :=
  lowerModule_ok h

/-- **A valid module and its lowering are exactly export-equivalent**, at every profile and
every code-parametric host. -/
theorem lower_exportEquiv (hhost : Execution.Core.Sim.HostParametric host) {m : Module}
    (hm : ∃ mt, ModuleOk m mt) :
    ExportEquiv (· = ·) P host m (lowerModule m) := by
  have hm' : ∃ mt, ModuleOk (lowerModule m) mt :=
    let ⟨mt, h⟩ := hm
    ⟨mt, lowerModule_valid h⟩
  have hR : Execution.Core.Sim.HostRespects (Execution.Core.Sim.FuncRel selBI) host :=
    hhost.respects fun f => Execution.Core.Sim.FuncRel.refl f
  have hfl := (lowerModule_rel m).flip
  rw [selBI_flip] at hfl
  exact ⟨exportRefines_of_bodiesRel selBaseSim hR (lowerModule_rel m) hm hm',
    (exportRefines_of_bodiesRel selBaseSim hR hfl hm' hm).mono fun _ _ h => h.symm⟩

/-- The check of a successful compilation, and the read-back. -/
theorem compile_some {m : Module} {l : Lime1.Module} (h : compile m = some l) :
    funcrefElemsB (lowerModule m) = true ∧ Lime1.Module.ofCore? (lowerModule m) = some l := by
  unfold compile at h
  split at h
  · rename_i hc
    exact ⟨hc, h⟩
  · cases h

/-- Retyping element segments to `funcref` is the identity when they already are. -/
theorem funcrefElems_eq {M : Module} (h : funcrefElemsB M = true) :
    Silmaril.Wasm.Component.Lime1Inst.funcrefElems M = M := by
  simp only [funcrefElemsB, List.all_eq_true, decide_eq_true_eq] at h
  have he : M.elems.map (fun e => { e with type := V1.funcref }) = M.elems := by
    conv => rhs; rw [← List.map_id M.elems]
    exact List.map_congr_left fun e he' => by rw [← h e he']; rfl
  simp only [Silmaril.Wasm.Component.Lime1Inst.funcrefElems,
    Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElems, he]

/-- **A successful compilation is the lowering, read in Core.** -/
theorem compile_toCore {m : Module} {l : Lime1.Module} (h : compile m = some l) :
    l.toCore = lowerModule m := by
  obtain ⟨hf, hl⟩ := compile_some h
  rw [Silmaril.Wasm.Component.Lime1Inst.module_retract hl, funcrefElems_eq hf]

/-- The Core image of the output of a valid module validates, with the same module type. -/
theorem compile_valid {m : Module} {l : Lime1.Module} (h : compile m = some l)
    {mt : CModuleType} (hm : ModuleOk m mt) : ModuleOk l.toCore mt := by
  rw [compile_toCore h]
  exact lowerModule_valid hm

/-- **The direct compiler is correct**: a valid Core 3.0 module and the Core image of its Lime1
compilation are exactly export-equivalent, at every profile and every code-parametric host. -/
theorem compile_correct (hhost : Execution.Core.Sim.HostParametric host) {m : Module}
    {l : Lime1.Module} (h : compile m = some l) (hm : ∃ mt, ModuleOk m mt) :
    ExportEquiv (· = ·) P host m l.toCore := by
  rw [compile_toCore h]
  exact lower_exportEquiv hhost hm

/-- **The API is kept exactly**: only function bodies change. -/
theorem compile_api {m : Module} {l : Lime1.Module} (h : compile m = some l) :
    ({ l.toCore with funcs := [] } : Module) = { m with funcs := [] } ∧
      l.toCore.funcs.map (fun f => (f.type, f.locals)) = m.funcs.map (fun f => (f.type, f.locals)) := by
  rw [compile_toCore h]
  refine ⟨rfl, ?_⟩
  simp only [lowerModule, List.map_map]
  rfl

/-- **The compiler is the identity on Lime1**: every Lime1 module is compiled to itself. -/
theorem compile_lime (l : Lime1.Module) : compile l.toCore = some l := by
  have he : funcrefElemsB l.toCore = true := by
    simp [funcrefElemsB, Lime1.Module.toCore, Lime1.Elem.toCore]
  unfold compile
  simp only [lowerModule_toCore, he, ↓reduceIte, Lime1.Module.ofCore?_toCore]

/-- **Modules whose types leave Lime1 are rejected** (a 3.0-only API is not preserved). -/
theorem compile_none_of_types {m : Module} (h : m.types.mapM V1.FuncType.ofCoreRec? = none) :
    compile m = none := by
  unfold compile
  split
  · simp [Lime1.Module.ofCore?, lowerModule, h]
  · rfl

/-- **Size data**: the rewrite is one instruction for one instruction, in every sequence (and,
by `selBaseSim`, one step for one step). -/
theorem lowerL_length : ∀ es : List Instr, (lowerL es).length = es.length
  | [] => by rw [lowerL]
  | i :: es => by rw [lowerL, List.length_cons, List.length_cons, lowerL_length es]

/-- info: 'Silmaril.Wasm.LimeCompile.Direct.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile_correct

end Silmaril.Wasm.LimeCompile.Direct

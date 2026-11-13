module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstGlobRes

/-!
# The forward 1.0 run from V1 instantiation, modules with globals allowed

an earlier `instantiation_core10` (and so `wholeRunFwd10InvV`) assumed the copied
`InstantiationBounds`, whose field `noGlobals` excludes every module with globals: the copied
Lime1 → Core instantiation simulation is false for them, because Core's `$evalglobals` allocates
each global a second time. The component work avoided this for components through the residue
(`Lime1Inst`); `InstGlobRes` carries the residue to every store. Here:

* `InstBoundsG L l`: `InstantiationBounds` without `noGlobals`;
* **`instantiation_core10G`**: a V1 instantiation of a module **with globals** yields a valid
  Core store erasing to the image of its result, and the simulation's `StoreWF`, under
  `InstBoundsG`, from a store whose Core image is valid. The module's initializers evaluate
  (`allocate?_valsG`) to values of their types (`vals_typed`, with imported globals read through
  `ImportsMatch`); the residue is prepared against the store extended by those globals exactly
  as the module is against the store (`prepare?_residueG`); the residue has no globals, so the
  copied `prepare_core`/`start_sim` apply to it, and the extended store's Core image is valid
  (`storeOk_gstore`);
* **`wholeRunFwd10InvG`**, **`wholeRunFwd10InvGT`**: round 4's `Task.wholeRunFwd10Inv` and its
  `simEnv10T` form from such an instantiation; **`wholeRunFwd10InvG_empty`**: from the empty
  store, with only the module bounds `ModBoundsG` (32-bit segments; globals allowed).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstG

open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps Instantiation)
open Silmaril.Wasm.Execution.Runtime (Value ExternVal)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10 NoHost10 plain10_invoke)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10 Silmaril.Wasm.SpecTec.Sim10.Valid
open Silmaril.Wasm.SpecTec.Sim10.Valid (InstOk10 instantiation_emptyHost memsAligned10_of_erase
  coreTyped10_invoke_erase invokeOk_erase storeOk_coreStore10_empty storeWF_empty10)
open Silmaril.Proofs.Wasm.Component.Lime1Inst (residueL globalInsts residue_valid)

variable {H : Type}

local notation "erase" => Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase

/-- **`InstantiationBounds` without `noGlobals`.** -/
structure InstBoundsG (before : Lime1.Execution.Store H) (m : Lime1.Module) : Prop where
  storeWF : Lime1.Execution.StoreWF before
  tables : ∀ t ∈ before.tables, t.refs.length < 2 ^ 32
  data : ∀ d ∈ m.data, d.bytes.size < 2 ^ 32
  elemSize : ∀ e ∈ m.elems, e.init.length < 2 ^ 32
  elemCount : m.elems.length ≤ 2 ^ 32
  dataCount : m.data.length ≤ 2 ^ 32

/-- The residue against the extended store satisfies the copied bounds. -/
theorem InstBoundsG.residue {L : Lime1.Execution.Store H} {l : Lime1.Module}
    (hb : InstBoundsG L l) (gis : List Execution.Runtime.GlobalInst) :
    Lime1.Execution.InstantiationBounds (gstore L gis) (residueL l) :=
  ⟨hb.storeWF, rfl, hb.tables, hb.data, hb.elemSize, hb.elemCount, hb.dataCount⟩

/-- A successful allocation evaluates every global initializer. -/
theorem allocate?_valsG {L : Lime1.Execution.Store H} {l : Lime1.Module} {imps : List ExternVal}
    {r : Lime1.Execution.Store H × Execution.Runtime.ModuleInst}
    (h : Lime1.Execution.allocate? L l imps = some r) :
    ∃ vals, l.globals.mapM (fun g => Lime1.Execution.constExpr? L
      { globals := (Lime1.Execution.importedInstance imps).globals } g.init) = some vals := by
  simp only [Lime1.Execution.allocate?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vals, hv, -⟩ := h
  exact ⟨vals, hv⟩

/-- **The residue of a prepared module**: the evaluated globals, and the residue's validity,
import matching, bounds and preparation against the extended store. -/
theorem residue_of_prepare {L : Lime1.Execution.Store H} {l : Lime1.Module}
    {imps : List ExternVal} {p : Lime1.Execution.Prepared H}
    (hv : Lime1.Validation.ModuleValid l) (hi : Lime1.Execution.ImportsMatch L l imps)
    (hb : InstBoundsG L l) (hp : Lime1.Execution.prepare? L l imps = some p) :
    ∃ vals, Lime1.Validation.ModuleValid (residueL l) ∧
      Lime1.Execution.ImportsMatch (gstore L (globalInsts l.globals vals)) (residueL l)
        (gimports imps L.globals.length l.globals.length) ∧
      Lime1.Execution.InstantiationBounds (gstore L (globalInsts l.globals vals)) (residueL l) ∧
      Lime1.Execution.prepare? (gstore L (globalInsts l.globals vals)) (residueL l)
        (gimports imps L.globals.length l.globals.length) = some p := by
  obtain ⟨allocated, -, -, hal, -, -, -⟩ := Lime1.Execution.prepare?_inv hp
  obtain ⟨vals, hvals⟩ := allocate?_valsG hal
  exact ⟨vals, residue_valid hv, importsMatch_residueG hi (vals_typed hv hi hvals),
    hb.residue _, (prepare?_residueG hvals).trans hp⟩

/-- **A V1 instantiation, globals allowed, yields a valid Core store erasing to the image of its
result**, and the simulation's `StoreWF`, under `InstBoundsG`, from a store whose Core image is
valid (empty V1 host). -/
theorem instantiation_core10G {before after : Store H} {m : V1.Module}
    {imports : List ExternVal} {module : Execution.Runtime.ModuleInst}
    {outcome : Execution.Runtime.Result}
    (hI : Instantiation emptyHost10 before m imports after module outcome)
    (hb : InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before)) :
    ∃ S : Execution.Core.Store H, Execution.Core.StoreOk S ∧ erase S = coreStore10 after ∧
      Lime1.Execution.StoreWF (after.mapCode V1.Func.toLime) := by
  obtain ⟨hv, hi, p, hp, rfl, hrun⟩ := hI.toLime compatible_empty
  obtain ⟨vals, hvR, hiR, hbR, hpR⟩ := residue_of_prepare hv hi hb hp
  obtain ⟨c, S₀, hinst, hsteps, hS₀, hF, hl⟩ :=
    Lime1.Execution.prepare_core (tgt := divHostC) hbR hvR hiR hpR
  obtain ⟨c₁, hsteps₁, -, hsim₁⟩ := Lime1.Execution.start_sim hbR hvR hiR hpR hS₀ hF hl
  obtain ⟨c', hsteps', hsim'⟩ := Lime1.Execution.Steps.toCore hostCompatible_empty hrun hsim₁
  have hok := Execution.Core.Instantiate.ok hostOk_div (storeOk_gstore hsB _) hinst
  obtain ⟨hok', -⟩ :=
    Execution.Core.Steps.safe hostOk_div hok ((hsteps.trans hsteps₁).trans hsteps')
  obtain ⟨C, ⟨hS, -⟩, -⟩ := hok'
  refine ⟨c'.store, hS, ?_, hsim'.2.1⟩
  obtain ⟨hn, -⟩ := hsim'
  rcases c' with ⟨cs, cf, cl⟩
  exact (Lime1.Execution.ToCore.Config.norm_eq_toCore_iff.mp hn).1

/-- `InstOk10` from a V1 instantiation, globals allowed. -/
theorem instOk10_of_instantiationG {host : HostSemantics H} {before after : Store H}
    {m : V1.Module} {imports : List ExternVal} {module : Execution.Runtime.ModuleInst}
    {outcome : Execution.Runtime.Result}
    (hI : Instantiation host before m imports after module outcome) (hnh : NoHost10 before)
    (hs : StoreOk10 before) (hb : InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before)) : InstOk10 before after := by
  obtain ⟨S, hS, he, hwf⟩ := instantiation_core10G (instantiation_emptyHost hI hnh hs) hb hsB
  exact ⟨⟨S, hS, he⟩, hwf⟩

/-! ## The forward run -/

/-- **`Task.wholeRunFwd10Inv` from V1 instantiation, globals allowed.** -/
theorem wholeRunFwd10InvG {hn : H → String} {host host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {before s : Store H} {m : V1.Module} {imports : List ExternVal}
    {module : Execution.Runtime.ModuleInst} {outcome : Execution.Runtime.Result}
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hI : Instantiation host before m imports s module outcome) (hnh : NoHost10 before)
    (hs10 : StoreOk10 before) (hb : InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before))
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  obtain ⟨⟨S, hS, he⟩, hwf⟩ := instOk10_of_instantiationG hI hnh hs10 hb hsB
  exact wholeRunFwd10C H hn host' nd r _ c' hc (plain10_invoke args a)
    (memsAligned10_of_erase hS he)
    (coreTyped10_invoke_erase hS he (invokeOk_erase he hinv) hwf) h

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10InvGT {hn : H → String} {host host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {before s : Store H} {m : V1.Module} {imports : List ExternVal}
    {module : Execution.Runtime.ModuleInst} {outcome : Execution.Runtime.Result}
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hI : Instantiation host before m imports s module outcome) (hnh : NoHost10 before)
    (hs10 : StoreOk10 before) (hb : InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before))
    (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  obtain ⟨⟨S, hS, he⟩, hwf⟩ := instOk10_of_instantiationG hI hnh hs10 hb hsB
  exact wholeRunFwd10CT hc (plain10_invoke args a) (memsAligned10_of_erase hS he)
    (coreTyped10_invoke_erase hS he (invokeOk_erase he hinv) hwf) h

/-! ## From the empty store -/

/-- The module side of `InstBoundsG`: 32-bit segment sizes and counts (globals allowed). -/
structure ModBoundsG (m : V1.Module) : Prop where
  data : ∀ d ∈ m.data, d.bytes.size < 2 ^ 32
  elemSize : ∀ e ∈ m.elems, e.init.length < 2 ^ 32
  elemCount : m.elems.length ≤ 2 ^ 32
  dataCount : m.data.length ≤ 2 ^ 32

/-- `InstBoundsG` at the empty store, from the module side. -/
theorem boundsG_empty {m : V1.Module} (h : ModBoundsG m) :
    InstBoundsG (({} : Store H).mapCode V1.Func.toLime) m.toLime where
  storeWF := storeWF_empty10
  tables := fun _ ht => by simp [Execution.Runtime.Store.mapCode] at ht
  data := fun d hd => by
    simp only [V1.Module.toLime, List.mem_map] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    exact h.data d' hd'
  elemSize := fun e he => by
    simp only [V1.Module.toLime, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact h.elemSize e' he'
  elemCount := by simpa [V1.Module.toLime] using h.elemCount
  dataCount := by simpa [V1.Module.toLime] using h.dataCount

/-- **`Task.wholeRunFwd10Inv` from a V1 instantiation into the empty store, globals allowed**:
no hypothesis on the store but the module's segment bounds, the image typing and the
arguments' types. -/
theorem wholeRunFwd10InvG_empty {hn : H → String} {host host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {s : Store H} {m : V1.Module} {module : Execution.Runtime.ModuleInst}
    {outcome : Execution.Runtime.Result} {args : List Value} {a : Execution.Runtime.FuncAddr}
    {c' : Config H} (hI : Instantiation host {} m [] s module outcome) (hb : ModBoundsG m)
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') :=
  wholeRunFwd10InvG hI storeOk10_empty.1 storeOk10_empty.2 (boundsG_empty hb)
    storeOk_coreStore10_empty hc hinv h

end Silmaril.Wasm.SpecTec.Sim10.InstG

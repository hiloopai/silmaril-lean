module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdRun10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreValid10
public import Silmaril.Wasm.Component.Lime1Bridge.Thms

/-!
# The forward 1.0 run from an instantiated store, without Core `StoreOk`

Round 4's `Task.wholeRunFwd10Inv` (proved, `wholeRunFwd10Inv`) and round 5's `simEnv10T` form
(`wholeRunFwd10InvT`) assume that the Core image of the V1 store is valid
(`Execution.Core.StoreOk (coreStore10 s)`). That hypothesis is used twice: for `MemsAligned10`
and for `CoreTyped10` at the invocation. Neither needs the Core image itself to be valid: both
hold as soon as **some** valid Core store erases to the image, because `CoreTyped10` is read up
to the copied simulation relation `Lime1.Execution.Sim`, which is itself up to erasure.

* `memsAligned10_of_erase`, `invokeOk_erase`, **`coreTyped10_invoke_erase`**: `MemsAligned10`,
  Core's `InvokeOk` and `CoreTyped10` at the invocation, from a valid Core store `S` with
  `ToCore.Store.erase S = coreStore10 s` (`Lime1Bridge.invoke_sim_erase`).
* **`instantiation_core10`**: a V1 instantiation (validation of the module is part of it, and
  the start function runs) yields such an `S`, and the simulation's `StoreWF`, under the copied
  `InstantiationBounds` (in particular `noGlobals`): V1 instantiation is a Lime1 instantiation
  (`Instantiation.toLime`), which is simulated by Core `Instantiate` and Core steps
  (`prepare_core`, `start_sim`, `Steps.toCore`); Core `Instantiate` yields a typed configuration
  (`Instantiate.ok`) and Core steps keep it typed (`Steps.safe`).
* `instantiation_emptyHost`: an instantiation from a store with no host function and
  `StoreOk10` is one under the empty host (`storeOk10_prepare`, `step_noHost`).
* **`wholeRunFwd10InvV`**, **`wholeRunFwd10InvVT`**: `Task.wholeRunFwd10Inv` and its
  `simEnv10T` form with Core `StoreOk` of the invoked store and `StoreWF` replaced by: the store
  is the result of a V1 instantiation, under `InstantiationBounds`, from a store whose Core image
  is valid (for instance the empty store, `wholeRunFwd10InvV_empty`).

What is still assumed: `InstantiationBounds` (no module globals, 32-bit segment sizes; the
copied simulation is false without them, see `Lime1/ToCore/Instantiation`), the IL typing of the
invocation's image, Core's `InvokeOk` for the arguments, and Core `StoreOk` of the store
*before* instantiation (true of the empty store). Iterating instantiations needs `StoreOk` of
the Core image after one, which this module does not prove (only of a store erasing to it).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Valid

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps Instantiation)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10 Plain10 MemsAligned10 NoHost10 noHost10_step
  plain10_invoke)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {H : Type}

local notation "erase" => Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase

/-! ## From a valid Core store erasing to the image -/

/-- **The memories are aligned** when a valid Core store erases to the image. -/
theorem memsAligned10_of_erase {s : Store H} {S : Execution.Core.Store H}
    (hS : Execution.Core.StoreOk S) (he : erase S = coreStore10 s) : MemsAligned10 s := by
  intro m hm
  apply memAligned10_of_ok
  apply hS.mems
  have e : (erase S).mems = (coreStore10 s).mems := congrArg Execution.Core.Store.mems he
  rw [show S.mems = (erase S).mems from rfl, e]
  simp only [coreStore10, Execution.Runtime.Store.toCore, List.mem_map]
  exact ⟨m, by simpa [Execution.Runtime.Store.mapCode] using hm, rfl⟩

/-- A numeric value is typed alike in every store. -/
theorem valOk_toCore {X S : Execution.Core.Store H} {v : Execution.Runtime.Value}
    {t : CValType} (h : Execution.Core.ValOk X v.toCore t) : Execution.Core.ValOk S v.toCore t := by
  cases v
  cases h
  exact .num _

/-- **Core's `InvokeOk` moves to a store erasing to the image.** -/
theorem invokeOk_erase {s : Store H} {S : Execution.Core.Store H} (he : erase S = coreStore10 s)
    {a : Nat} {args : List Execution.Runtime.Value}
    (h : Execution.Core.InvokeOk (coreStore10 s) a (args.map Execution.Runtime.Value.toCore)) :
    Execution.Core.InvokeOk S a (args.map Execution.Runtime.Value.toCore) := by
  obtain ⟨fi, ps, rs, hfi, hexp, hvs⟩ := h
  have hf : (erase S).funcs[a]? = some fi := by rw [he]; exact hfi
  simp only [Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase, List.getElem?_map,
    Option.map_eq_some_iff] at hf
  obtain ⟨fi', hfi', rfl⟩ := hf
  refine ⟨fi', ps, rs, hfi', hexp, ?_⟩
  rw [List.forall₂_map_left_iff] at hvs ⊢
  exact hvs.imp fun _ _ h => valOk_toCore h

/-- The V1 invocation, read in Lime1, is Lime1's `$invoke`. -/
theorem toLime_invokeCfg10 (s : Store H) (args : List Execution.Runtime.Value)
    (a : Execution.Runtime.FuncAddr) :
    (invokeCfg10 s args a).toLime =
      Silmaril.Wasm.Models.Lime1Core.invokeL (s.mapCode V1.Func.toLime) a args := by
  simp only [invokeCfg10, V1.Execution.Config.toLime, Silmaril.Wasm.Models.Lime1Core.invokeL,
    V1.Execution.codeToLime_append, V1.Execution.map_values, frame0]
  rfl

/-- **The invocation is `CoreTyped10`** when a valid Core store erases to the image of `s`, the
arguments fit in it, and `s` satisfies the simulation's `StoreWF`. -/
theorem coreTyped10_invoke_erase {s : Store H} {args : List Execution.Runtime.Value}
    {a : Execution.Runtime.FuncAddr} {S : Execution.Core.Store H} (hS : Execution.Core.StoreOk S)
    (he : erase S = coreStore10 s)
    (hinv : Execution.Core.InvokeOk S a.value (args.map Execution.Runtime.Value.toCore))
    (hwf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime)) :
    CoreTyped10 (invokeCfg10 s args a) := by
  obtain ⟨fi, ps, rs, hfi, -, hok⟩ := Execution.Core.invoke_ok hS hinv
  have hlt : a.value < (s.mapCode V1.Func.toLime).funcs.length := by
    have h₁ := (List.getElem?_eq_some_iff.mp hfi).1
    have h₂ : S.funcs.length = (coreStore10 s).funcs.length := by
      have := congrArg (fun X => X.funcs.length) he
      simpa [Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase] using this
    rw [h₂] at h₁
    simpa [coreStore10, Execution.Runtime.Store.toCore] using h₁
  refine ⟨_, rs.toList, ?_, hok⟩
  rw [toLime_invokeCfg10]
  exact Silmaril.Proofs.Wasm.Component.Lime1Bridge.invoke_sim_erase hwf he hlt args

/-! ## From a V1 instantiation -/

/-- **A V1 instantiation yields a valid Core store erasing to the image of its result**, and the
simulation's `StoreWF`, under the copied `InstantiationBounds`, from a store whose Core image is
valid (empty V1 host). -/
theorem instantiation_core10 {before after : Store H} {m : V1.Module}
    {imports : List Execution.Runtime.ExternVal} {module : Execution.Runtime.ModuleInst}
    {outcome : Execution.Runtime.Result}
    (hI : Instantiation emptyHost10 before m imports after module outcome)
    (hb : Lime1.Execution.InstantiationBounds (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before)) :
    ∃ S : Execution.Core.Store H, Execution.Core.StoreOk S ∧ erase S = coreStore10 after ∧
      Lime1.Execution.StoreWF (after.mapCode V1.Func.toLime) := by
  obtain ⟨hv, hi, p, hp, rfl, hrun⟩ := hI.toLime compatible_empty
  obtain ⟨c, S₀, hinst, hsteps, hS₀, hF, hl⟩ :=
    Lime1.Execution.prepare_core (tgt := divHostC) hb hv hi hp
  obtain ⟨c₁, hsteps₁, -, hsim₁⟩ := Lime1.Execution.start_sim hb hv hi hp hS₀ hF hl
  obtain ⟨c', hsteps', hsim'⟩ := Lime1.Execution.Steps.toCore hostCompatible_empty hrun hsim₁
  have hok := Execution.Core.Instantiate.ok hostOk_div hsB hinst
  obtain ⟨hok', -⟩ :=
    Execution.Core.Steps.safe hostOk_div hok ((hsteps.trans hsteps₁).trans hsteps')
  obtain ⟨C, ⟨hS, -⟩, -⟩ := hok'
  refine ⟨c'.store, hS, ?_, hsim'.2.1⟩
  obtain ⟨hn, -⟩ := hsim'
  rcases c' with ⟨cs, cf, cl⟩
  exact (Lime1.Execution.ToCore.Config.norm_eq_toCore_iff.mp hn).1

/-- `NoHost10` along a run. -/
theorem noHost_steps10 {host : HostSemantics H} {c d : Config H} (h : Steps host c d)
    (hnh : NoHost10 c.store) : NoHost10 d.store := by
  induction h with
  | refl => exact hnh
  | tail _ hs ih => exact noHost10_step hs ih

/-- A V1 run from a store with no host function is a run under any other host. -/
theorem steps_noHost {host host' : HostSemantics H} {c d : Config H} (h : Steps host c d)
    (hnh : NoHost10 c.store) : Steps host' c d := by
  induction h with
  | refl => exact .refl
  | tail hb hs ih => exact .tail ih (step_noHost hs (noHost_steps10 hb hnh))

/-- **An instantiation from a store with no host function and `StoreOk10` is one under the
empty host.** -/
theorem instantiation_emptyHost {host : HostSemantics H} {before after : Store H} {m : V1.Module}
    {imports : List Execution.Runtime.ExternVal} {module : Execution.Runtime.ModuleInst}
    {outcome : Execution.Runtime.Result}
    (hI : Instantiation host before m imports after module outcome) (hnh : NoHost10 before)
    (hs : StoreOk10 before) : Instantiation emptyHost10 before m imports after module outcome := by
  obtain ⟨p, hp, hm, hrun⟩ := hI.prepared
  have hnh' := (storeOk10_prepare hI.valid hI.importsMatch hnh hs hp).1
  exact ⟨hI.valid, hI.importsMatch, p, hp, hm, steps_noHost hrun hnh'⟩

/-! ## The forward run from an instantiated store -/

/-- The hypotheses on the instantiated store, collected. -/
structure InstOk10 (before after : Store H) : Prop where
  core : ∃ S : Execution.Core.Store H, Execution.Core.StoreOk S ∧ erase S = coreStore10 after
  wf : Lime1.Execution.StoreWF (after.mapCode V1.Func.toLime)

/-- `InstOk10` from a V1 instantiation. -/
theorem instOk10_of_instantiation {host : HostSemantics H} {before after : Store H}
    {m : V1.Module} {imports : List Execution.Runtime.ExternVal}
    {module : Execution.Runtime.ModuleInst} {outcome : Execution.Runtime.Result}
    (hI : Instantiation host before m imports after module outcome) (hnh : NoHost10 before)
    (hs : StoreOk10 before)
    (hb : Lime1.Execution.InstantiationBounds (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before)) : InstOk10 before after := by
  obtain ⟨S, hS, he, hwf⟩ := instantiation_core10 (instantiation_emptyHost hI hnh hs) hb hsB
  exact ⟨⟨S, hS, he⟩, hwf⟩

/-- **`Task.wholeRunFwd10Inv` from V1 instantiation**: round 4's statement with Core `StoreOk` of
the invoked store and `StoreWF` replaced by "the store is the result of a V1 instantiation of a
(valid) module, under `InstantiationBounds`, from a store with no host function, `StoreOk10`,
and a valid Core image". -/
theorem wholeRunFwd10InvV {hn : H → String} {host host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {before s : Store H} {m : V1.Module}
    {imports : List Execution.Runtime.ExternVal} {module : Execution.Runtime.ModuleInst}
    {outcome : Execution.Runtime.Result} {args : List Execution.Runtime.Value}
    {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hI : Instantiation host before m imports s module outcome) (hnh : NoHost10 before)
    (hs10 : StoreOk10 before)
    (hb : Lime1.Execution.InstantiationBounds (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before))
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value
      (args.map Execution.Runtime.Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  obtain ⟨⟨S, hS, he⟩, hwf⟩ := instOk10_of_instantiation hI hnh hs10 hb hsB
  exact wholeRunFwd10C H hn host' nd r _ c' hc (plain10_invoke args a)
    (memsAligned10_of_erase hS he)
    (coreTyped10_invoke_erase hS he (invokeOk_erase he hinv) hwf) h

/-- **The same in `simEnv10T`** (stores in the code and the store's functions allowed). -/
theorem wholeRunFwd10InvVT {hn : H → String} {host host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {before s : Store H} {m : V1.Module}
    {imports : List Execution.Runtime.ExternVal} {module : Execution.Runtime.ModuleInst}
    {outcome : Execution.Runtime.Result} {args : List Execution.Runtime.Value}
    {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hI : Instantiation host before m imports s module outcome) (hnh : NoHost10 before)
    (hs10 : StoreOk10 before)
    (hb : Lime1.Execution.InstantiationBounds (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before))
    (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value
      (args.map Execution.Runtime.Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  obtain ⟨⟨S, hS, he⟩, hwf⟩ := instOk10_of_instantiation hI hnh hs10 hb hsB
  exact wholeRunFwd10CT hc (plain10_invoke args a) (memsAligned10_of_erase hS he)
    (coreTyped10_invoke_erase hS he (invokeOk_erase he hinv) hwf) h

/-! ## From the empty store -/

/-- The Core image of the empty store is valid. -/
theorem storeOk_coreStore10_empty : Execution.Core.StoreOk (coreStore10 ({} : Store H)) := by
  constructor <;>
    simp [coreStore10, Execution.Runtime.Store.toCore, Execution.Runtime.Store.mapCode]

/-- The empty store satisfies the simulation's `StoreWF`. -/
theorem storeWF_empty10 : Lime1.Execution.StoreWF (({} : Store H).mapCode V1.Func.toLime) :=
  ⟨fun _ _ _ _ h => by simp [Execution.Runtime.Store.mapCode] at h,
    fun _ _ h => by simp [Execution.Runtime.Store.mapCode] at h⟩

/-- The module side of `InstantiationBounds`: no globals, and 32-bit segment sizes and counts. -/
structure ModBounds10 (m : V1.Module) : Prop where
  noGlobals : m.globals = []
  data : ∀ d ∈ m.data, d.bytes.size < 2 ^ 32
  elemSize : ∀ e ∈ m.elems, e.init.length < 2 ^ 32
  elemCount : m.elems.length ≤ 2 ^ 32
  dataCount : m.data.length ≤ 2 ^ 32

/-- `InstantiationBounds` at the empty store, from the module side. -/
theorem bounds_empty10 {m : V1.Module} (h : ModBounds10 m) :
    Lime1.Execution.InstantiationBounds (({} : Store H).mapCode V1.Func.toLime) m.toLime where
  storeWF := storeWF_empty10
  noGlobals := by simp [V1.Module.toLime, h.noGlobals]
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

/-- **`Task.wholeRunFwd10Inv` from a V1 instantiation into the empty store**: no hypothesis on
the store but the module bounds, the image typing and the arguments' types. -/
theorem wholeRunFwd10InvV_empty {hn : H → String} {host host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {s : Store H} {m : V1.Module} {module : Execution.Runtime.ModuleInst}
    {outcome : Execution.Runtime.Result} {args : List Execution.Runtime.Value}
    {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hI : Instantiation host {} m [] s module outcome) (hb : ModBounds10 m)
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value
      (args.map Execution.Runtime.Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') :=
  wholeRunFwd10InvV hI storeOk10_empty.1 storeOk10_empty.2 (bounds_empty10 hb)
    storeOk_coreStore10_empty hc hinv h

end Silmaril.Wasm.SpecTec.Sim10.Valid

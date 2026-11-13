module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstErase10

/-!
# The 1.0 instantiation route with host functions

an earlier `instantiation_core10G` (and with it `wholeRunFwd10InvG` and the iterated
`wholeRunFwd10InvRU`) read the V1 instantiation under the empty V1 host, so it assumed a store
with no host function and `StoreOk10` (`instantiation_emptyHost`). An earlier step  removed the
corresponding assumption on the 2.0 side (`V2CoreInstHostFn.instantiate_imports_any`), where it
was used only to conclude something about the result. Here the same is done for 1.0:

* **`instantiation_core10GH`**: a V1 instantiation under **any** V1 host that is compatible with
  a Lime1 host, itself compatible with a Core host satisfying Core's `HostOk`, yields a valid
  Core store erasing to the image of its result, and `StoreWF`. The proof is an earlier, with the
  hosts as parameters: the copied `prepare_core`/`start_sim`/`Steps.toCore` already take any
  compatible hosts, and Core's `Instantiate.ok`/`Steps.safe` take any `HostOk` host.
  `NoHost10` and `StoreOk10` of the store before are no longer used.
* `HostChain10 host`: the compatibility chain. `hostChain10_empty`: the empty V1 host has one.
* **`ReachH10 s₀`**: stores reached from a base store `s₀` (which may hold host functions) by V1
  instantiations under hosts with a chain. **`reachH10_ok`**: each has a valid Core image and
  `StoreWF`, given a valid Core image and `StoreWF` of `s₀` (through `storeOkErase10`).
* **`wholeRunFwd10InvGH`**, `wholeRunFwd10InvGHT`, **`wholeRunFwd10InvRH`**, `wholeRunFwd10InvRHT`:
  round 4's `Task.wholeRunFwd10Inv` from such instantiations, with no `NoHost10`/`StoreOk10`
  hypothesis on any store.

What the forward run cannot drop:

* **`noHost10_of_typed10_invoke`**, `noHost10_of_typed10T_invoke`: the image of an invocation is
  typed in `simEnv10` (or `simEnv10T`) only over a store **with no host function**. The 1.0
  script's `funcinst` has `CODE func` only; it has no host function instance, so the state of a
  store with one is not a typed `state`. So the hypothesis `hc` of the forward theorems
  excludes host functions from the *invoked* store, and the forward theorems are vacuous there.
  This is a property of the 1.0 script, not of the proof; covering such stores would need an
  erratum of the script adding host function instances (not attempted).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstH

open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps Instantiation)
open Silmaril.Wasm.Execution.Runtime (Value ExternVal)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10 NoHost10 plain10_invoke noHost10_of_typed
  noHost10_of_typedT typedV_state_of_typed10 typedV_state_of_typed10T)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10 Silmaril.Wasm.SpecTec.Sim10.Valid Silmaril.Wasm.SpecTec.Sim10.InstG
open Silmaril.Wasm.SpecTec.Sim10.Valid (memsAligned10_of_erase coreTyped10_invoke_erase
  invokeOk_erase)

variable {H : Type}

local notation "erase" => Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase

/-! ## The instantiation with any compatible hosts -/

/-- A V1 host with a compatible Lime1 host, itself compatible with a Core host satisfying
Core's `HostOk`. -/
def HostChain10 (host : HostSemantics H) : Prop :=
  ∃ (tL : Lime1.Execution.HostSemantics H) (tC : Execution.Core.HostSemantics H),
    Execution.Runtime.HostSemantics.Compatible V1.Func.toLime host tL ∧
      Lime1.Execution.HostCompatible tL tC ∧ Execution.Core.HostOk tC

/-- The empty V1 host has a chain (to the diverging Core host). -/
theorem hostChain10_empty : HostChain10 (emptyHost10 (H := H)) :=
  ⟨_, _, compatible_empty, hostCompatible_empty, hostOk_div⟩

/-- **A V1 instantiation under any host with a chain yields a valid Core store erasing to the
image of its result**, and the simulation's `StoreWF`, under `InstBoundsG`, from a store whose
Core image is valid. No hypothesis on the host functions of the store. -/
theorem instantiation_core10GH {host : HostSemantics H} (hh : HostChain10 host)
    {before after : Store H} {m : V1.Module} {imports : List ExternVal}
    {module : Execution.Runtime.ModuleInst} {outcome : Execution.Runtime.Result}
    (hI : Instantiation host before m imports after module outcome)
    (hb : InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before)) :
    ∃ S : Execution.Core.Store H, Execution.Core.StoreOk S ∧ erase S = coreStore10 after ∧
      Lime1.Execution.StoreWF (after.mapCode V1.Func.toLime) := by
  obtain ⟨tL, tC, hcL, hcC, hokC⟩ := hh
  obtain ⟨hv, hi, p, hp, rfl, hrun⟩ := hI.toLime hcL
  obtain ⟨vals, hvR, hiR, hbR, hpR⟩ := residue_of_prepare hv hi hb hp
  obtain ⟨c, S₀, hinst, hsteps, hS₀, hF, hl⟩ :=
    Lime1.Execution.prepare_core (tgt := tC) hbR hvR hiR hpR
  obtain ⟨c₁, hsteps₁, -, hsim₁⟩ := Lime1.Execution.start_sim hbR hvR hiR hpR hS₀ hF hl
  obtain ⟨c', hsteps', hsim'⟩ := Lime1.Execution.Steps.toCore hcC hrun hsim₁
  have hok := Execution.Core.Instantiate.ok hokC (storeOk_gstore hsB _) hinst
  obtain ⟨hok', -⟩ :=
    Execution.Core.Steps.safe hokC hok ((hsteps.trans hsteps₁).trans hsteps')
  obtain ⟨C, ⟨hS, -⟩, -⟩ := hok'
  refine ⟨c'.store, hS, ?_, hsim'.2.1⟩
  obtain ⟨hn, -⟩ := hsim'
  rcases c' with ⟨cs, cf, cl⟩
  exact (Lime1.Execution.ToCore.Config.norm_eq_toCore_iff.mp hn).1

/-- The Core image of the instantiated store is itself valid. -/
theorem instantiation_core10GH_ok {host : HostSemantics H} (hh : HostChain10 host)
    {before after : Store H} {m : V1.Module} {imports : List ExternVal}
    {module : Execution.Runtime.ModuleInst} {outcome : Execution.Runtime.Result}
    (hI : Instantiation host before m imports after module outcome)
    (hb : InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before)) :
    Execution.Core.StoreOk (coreStore10 after) ∧
      Lime1.Execution.StoreWF (after.mapCode V1.Func.toLime) := by
  obtain ⟨S, hS, he, hwf⟩ := instantiation_core10GH hh hI hb hsB
  exact ⟨storeOkErase10 H after S hS he, hwf⟩

/-! ## The forward run -/

/-- **`Task.wholeRunFwd10Inv` from a V1 instantiation under any host with a chain**, globals
allowed, with no hypothesis on the host functions of the store before. -/
theorem wholeRunFwd10InvGH {hn : H → String} {host host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {before s : Store H} {m : V1.Module} {imports : List ExternVal}
    {module : Execution.Runtime.ModuleInst} {outcome : Execution.Runtime.Result}
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hh : HostChain10 host) (hI : Instantiation host before m imports s module outcome)
    (hb : InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before))
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  obtain ⟨S, hS, he, hwf⟩ := instantiation_core10GH hh hI hb hsB
  exact wholeRunFwd10C H hn host' nd r _ c' hc (plain10_invoke args a)
    (memsAligned10_of_erase hS he)
    (coreTyped10_invoke_erase hS he (invokeOk_erase he hinv) hwf) h

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10InvGHT {hn : H → String} {host host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {before s : Store H} {m : V1.Module} {imports : List ExternVal}
    {module : Execution.Runtime.ModuleInst} {outcome : Execution.Runtime.Result}
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hh : HostChain10 host) (hI : Instantiation host before m imports s module outcome)
    (hb : InstBoundsG (before.mapCode V1.Func.toLime) m.toLime)
    (hsB : Execution.Core.StoreOk (coreStore10 before))
    (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  obtain ⟨S, hS, he, hwf⟩ := instantiation_core10GH hh hI hb hsB
  exact wholeRunFwd10CT hc (plain10_invoke args a) (memsAligned10_of_erase hS he)
    (coreTyped10_invoke_erase hS he (invokeOk_erase he hinv) hwf) h

/-! ## Iterated, from any base store -/

/-- **Stores reached from `s₀` by V1 instantiations** under hosts with a chain and
`InstBoundsG`. The base store may hold host functions. -/
inductive ReachH10 (s₀ : Store H) : Store H → Prop where
  | base : ReachH10 s₀ s₀
  | inst {host : HostSemantics H} {before after : Store H} {m : V1.Module}
      {imports : List ExternVal} {module : Execution.Runtime.ModuleInst}
      {outcome : Execution.Runtime.Result} :
      ReachH10 s₀ before → HostChain10 host →
      Instantiation host before m imports after module outcome →
      InstBoundsG (before.mapCode V1.Func.toLime) m.toLime → ReachH10 s₀ after

/-- **Every store reached from a base store with a valid Core image and `StoreWF` has a valid
Core image and `StoreWF`.** -/
theorem reachH10_ok {s₀ s : Store H} (h : ReachH10 s₀ s)
    (h₀ : Execution.Core.StoreOk (coreStore10 s₀))
    (hw₀ : Lime1.Execution.StoreWF (s₀.mapCode V1.Func.toLime)) :
    Execution.Core.StoreOk (coreStore10 s) ∧ Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime) := by
  induction h with
  | base => exact ⟨h₀, hw₀⟩
  | inst _ hh hI hb ih => exact instantiation_core10GH_ok hh hI hb ih.1

/-- `Reach10` (from the empty store, any host, no host function) is `ReachH10 {}`. -/
theorem reachH10_of_reach10 {s : Store H} (h : Reach10 s) : ReachH10 {} s := by
  induction h with
  | empty => exact .base
  | @inst host before after m imports module outcome hR hI hb ih =>
    have ok := reach10_okU hR
    exact .inst ih hostChain10_empty (instantiation_emptyHost hI ok.noHost ok.storeOk10) hb

/-- **`Task.wholeRunFwd10Inv` at every store reached from a base store** with a valid Core image
and `StoreWF`, through instantiations under hosts with a chain. -/
theorem wholeRunFwd10InvRH {hn : H → String} {host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {s₀ s : Store H} (hR : ReachH10 s₀ s)
    (h₀ : Execution.Core.StoreOk (coreStore10 s₀))
    (hw₀ : Lime1.Execution.StoreWF (s₀.mapCode V1.Func.toLime))
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  obtain ⟨hS, hwf⟩ := reachH10_ok hR h₀ hw₀
  have he := erase_coreStore10 s
  exact wholeRunFwd10C H hn host' nd r _ c' hc (plain10_invoke args a)
    (memsAligned10_of_erase hS he) (coreTyped10_invoke_erase hS he (invokeOk_erase he hinv) hwf) h

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10InvRHT {hn : H → String} {host' : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {s₀ s : Store H} (hR : ReachH10 s₀ s)
    (h₀ : Execution.Core.StoreOk (coreStore10 s₀))
    (hw₀ : Lime1.Execution.StoreWF (s₀.mapCode V1.Func.toLime))
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  obtain ⟨hS, hwf⟩ := reachH10_ok hR h₀ hw₀
  have he := erase_coreStore10 s
  exact wholeRunFwd10CT hc (plain10_invoke args a) (memsAligned10_of_erase hS he)
    (coreTyped10_invoke_erase hS he (invokeOk_erase he hinv) hwf) h

/-! ## What the forward run cannot drop -/

/-- **A typed invocation image has no host function in its store** (`simEnv10`). -/
theorem noHost10_of_typed10_invoke {hn : H → String} {B : Silmaril.SpecTec.Sem.Builtins} {s : Store H}
    {args : List Value} {a : Execution.Runtime.FuncAddr}
    (hc : Typed10 (simEnv10 B) hn (invokeCfg10 s args a)) : NoHost10 s :=
  noHost10_of_typed (typedV_state_of_typed10 hc)

/-- **The same in `simEnv10T`.** -/
theorem noHost10_of_typed10T_invoke {hn : H → String} {B : Silmaril.SpecTec.Sem.Builtins} {s : Store H}
    {args : List Value} {a : Execution.Runtime.FuncAddr}
    (hc : Typed10 (simEnv10T B) hn (invokeCfg10 s args a)) : NoHost10 s :=
  noHost10_of_typedT (typedV_state_of_typed10T hc)

end Silmaril.Wasm.SpecTec.Sim10.InstH

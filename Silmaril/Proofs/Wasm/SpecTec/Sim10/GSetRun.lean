module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.GSetCore
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdWhole

/-!
# `GSetOk` along V1 runs, from Core typing

`CoreTyped10 c`: the V1 configuration `c` is related, through the lock-step `V1 → Lime1` transport
and the copied `Lime1 → Core` simulation relation, to a Core 3.0 configuration that is typed
(`ConfigOk`). This is validation of `c`, read through Core 3.0's type system: V1 has no
configuration typing of its own.

* `step_noHost`: with no host function in the store, a V1 step does not depend on the host.
* `coreTyped10_step`, `coreTyped10_steps`: `CoreTyped10` is invariant along V1 runs from a store
  with no host function. The V1 step is a Lime1 step (`Step.toLime`), which is one or more Core
  steps along the simulation relation (`Lime1.Execution.Step.toCore`), and Core steps preserve
  `ConfigOk` (`Execution.Core.Step.preservation`). The hosts are the empty V1 and Lime1 hosts and a
  Core host that only diverges, which satisfies Core's `HostOk`.
* `gsetOk_steps`: so `GSetOk` holds at every configuration of such a run (`gsetOk_of_core`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Valid

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps)
open Silmaril.Wasm.SpecTec.Sim10.Whole (NoHost10 noHost10_step)

variable {H : Type}

/-- The V1 host with no behaviour. -/
def emptyHost10 : HostSemantics H := fun _ _ _ _ => False

/-- **With no host function in the store, a V1 step does not depend on the host.** -/
theorem step_noHost {host host' : HostSemantics H} {c d : Config H} (h : Step host c d)
    (hnh : NoHost10 c.store) : Step host' c d := by
  induction h with
  | pure s f h => exact .pure s f h
  | context _ vs tail ih => exact .context (ih hnh) vs tail
  | label _ n cont ih => exact .label (ih hnh) n cont
  | frame _ n outer ih => exact .frame (ih hnh) n outer
  | localGet s f i v found => exact .localGet s f i v found
  | localSet s f i v old found => exact .localSet s f i v old found
  | globalGet s f i a g index found => exact .globalGet s f i a g index found
  | globalSet s f i a g v index found mutable => exact .globalSet s f i a g v index found mutable
  | call s f i a found => exact .call s f i a found
  | callIndirect s f i c table a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact .callIndirect s f i c table a fn ft h₁ h₂ h₃ h₄ h₅
  | callIndirectBounds s f i c table h₁ h₂ => exact .callIndirectBounds s f i c table h₁ h₂
  | callIndirectNull s f i c table h₁ h₂ => exact .callIndirectNull s f i c table h₁ h₂
  | callIndirectType s f i c table a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact .callIndirectType s f i c table a fn ft h₁ h₂ h₃ h₄ h₅
  | invokeWasm s f a ft module fn args found arity resultArity =>
    exact .invokeWasm s f a ft module fn args found arity resultArity
  | invokeHost s s' f a ft fn args r found _ _ => exact absurd found (hnh _ _ _)
  | invokeHostDiverges s f a ft fn args found _ _ => exact absurd found (hnh _ _ _)
  | intLoad s f t p arg c a m v h₁ h₂ => exact .intLoad s f t p arg c a m v h₁ h₂
  | intLoadTrap s f t p arg c a m h₁ h₂ => exact .intLoadTrap s f t p arg c a m h₁ h₂
  | floatLoad s f t arg c a m v h₁ h₂ => exact .floatLoad s f t arg c a m v h₁ h₂
  | floatLoadTrap s f t arg c a m h₁ h₂ => exact .floatLoadTrap s f t arg c a m h₁ h₂
  | intStore s f t p arg c x a m b h₁ h₂ => exact .intStore s f t p arg c x a m b h₁ h₂
  | intStoreTrap s f t p arg c x a m h₁ h₂ => exact .intStoreTrap s f t p arg c x a m h₁ h₂
  | floatStore s f t arg c x a m b h₁ h₂ => exact .floatStore s f t arg c x a m b h₁ h₂
  | floatStoreTrap s f t arg c x a m h₁ h₂ => exact .floatStoreTrap s f t arg c x a m h₁ h₂
  | memorySize s f a m h₁ => exact .memorySize s f a m h₁
  | memoryGrow s f a m c r b h₁ h₂ => exact .memoryGrow s f a m c r b h₁ h₂

/-! ## Hosts -/

/-- The Lime1 host with no behaviour. -/
def emptyHostL : Lime1.Execution.HostSemantics H := fun _ _ _ _ => False

/-- The Core host that only diverges. -/
def divHostC : Execution.Core.HostSemantics H := fun _ _ _ out => out = .diverged

theorem compatible_empty :
    Execution.Runtime.HostSemantics.Compatible V1.Func.toLime (emptyHost10 (H := H)) emptyHostL :=
  fun _ _ _ _ h => h.elim

theorem hostCompatible_empty :
    Lime1.Execution.HostCompatible (emptyHostL (H := H)) divHostC :=
  ⟨fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩

theorem hostOk_div : Execution.Core.HostOk (divHostC (H := H)) := by
  intro s fi h vs ps rs _ _ _ _ _
  refine ⟨⟨.diverged, rfl⟩, ?_⟩
  intro out hout
  cases hout
  trivial

/-! ## The invariant -/

/-- **`c` is typed through Core 3.0**: the simulation relation relates its Lime1 image to a
Core configuration that is typed. -/
def CoreTyped10 (c : Config H) : Prop :=
  ∃ (cc : Execution.Core.Config H) (ts : List CValType),
    Lime1.Execution.Sim c.toLime cc ∧ Execution.Core.ConfigOk cc ts

/-- Core runs preserve `ConfigOk`. -/
theorem configOk_transGen {host : Execution.Core.HostSemantics H} (hh : Execution.Core.HostOk host)
    {c c' : Execution.Core.Config H} {ts : List CValType}
    (h : Relation.TransGen (Execution.Core.Step Lime1.Execution.coreProfile host) c c')
    (hc : Execution.Core.ConfigOk c ts) : Execution.Core.ConfigOk c' ts := by
  induction h with
  | single h => exact (Execution.Core.Step.preservation hh hc h).1
  | tail _ h ih => exact (Execution.Core.Step.preservation hh ih h).1

/-- **`CoreTyped10` is invariant along every V1 step from a store with no host function.** -/
theorem coreTyped10_step {host : HostSemantics H} {c d : Config H} (h : Step host c d)
    (hnh : NoHost10 c.store) (hc : CoreTyped10 c) : CoreTyped10 d := by
  obtain ⟨cc, ts, hsim, hok⟩ := hc
  have h₀ : Step emptyHost10 c d := step_noHost h hnh
  have hL := h₀.toLime compatible_empty
  obtain ⟨cc', hrun, hsim'⟩ := Lime1.Execution.Step.toCore hostCompatible_empty hL hsim
  exact ⟨cc', ts, hsim', configOk_transGen hostOk_div hrun hok⟩

/-- **`CoreTyped10` along every V1 run from a store with no host function.** -/
theorem coreTyped10_steps {host : HostSemantics H} {c d : Config H} (h : Steps host c d)
    (hnh : NoHost10 c.store) (hc : CoreTyped10 c) : NoHost10 d.store ∧ CoreTyped10 d := by
  induction h with
  | refl => exact ⟨hnh, hc⟩
  | tail _ hs ih => exact ⟨noHost10_step hs ih.1, coreTyped10_step hs ih.1 ih.2⟩

/-- **`GSetOk` at a `CoreTyped10` configuration.** -/
theorem gsetOk_of_coreTyped10 {c : Config H} (hc : CoreTyped10 c) :
    Silmaril.Wasm.SpecTec.Sim10.GSetOk c.store c.frame c.code := by
  obtain ⟨_, _, hsim, hok⟩ := hc
  exact gsetOk_of_core hsim hok

/-- **`GSetOk` at every configuration of a V1 run** from a `CoreTyped10` configuration whose
store has no host function. -/
theorem gsetOk_steps {host : HostSemantics H} {c d : Config H} (h : Steps host c d)
    (hnh : NoHost10 c.store) (hc : CoreTyped10 c) :
    Silmaril.Wasm.SpecTec.Sim10.GSetOk d.store d.frame d.code :=
  gsetOk_of_coreTyped10 (coreTyped10_steps h hnh hc).2

/-! ## At an invocation -/

/-- The empty frame, the frame of an invocation (Core's `$invoke` uses the empty frame too). -/
def frame0 : Execution.Runtime.Frame := ⟨[], {}⟩

/-- The V1 invocation of `a` on `args` in `s`. -/
def invokeCfg10 (s : Store H) (args : List Execution.Runtime.Value) (a : Execution.Runtime.FuncAddr) : Config H :=
  ⟨s, frame0, V1.Execution.values args ++ [.invoke a]⟩

/-- The Core image of a V1 store. -/
abbrev coreStore10 (s : Store H) : Execution.Core.Store H := (s.mapCode V1.Func.toLime).toCore

/-- The image of the invocation is Core's `$invoke`. -/
theorem toCore_invokeCfg10 (s : Store H) (args : List Execution.Runtime.Value) (a : Execution.Runtime.FuncAddr) :
    (invokeCfg10 s args a).toLime.toCore =
      Execution.Core.invoke (coreStore10 s) a.value (args.map Execution.Runtime.Value.toCore) := by
  simp only [invokeCfg10, V1.Execution.Config.toLime, Execution.Runtime.Config.toCore,
    Execution.Core.invoke, V1.Execution.codeToLime_append, V1.Execution.map_values,
    Lime1.Execution.listToCore_append, Lime1.Execution.values_toCore]
  congr 2
  simp only [V1.Execution.codeToLime_cons, V1.Execution.codeToLime_nil,
    Execution.Runtime.AdminInstr.map, Lime1.Execution.listToCore_cons,
    Lime1.Execution.listToCore_nil, List.append_nil, Lime1.Execution.Admin.toCore]
  congr 3
  simp only [Execution.Runtime.Store.funcDefType, Execution.Runtime.Store.toCore,
    List.getElem?_map, Option.map_map]
  congr 2
  funext fi
  cases fi <;> rfl

/-- **The invocation is `CoreTyped10`** when the Core image of the store is valid (`StoreOk`), the
arguments fit the function's type (`InvokeOk`), and the store satisfies the simulation's
well-formedness (`Lime1.Execution.StoreWF`: function modules name allocated functions, memories
fit 32-bit addresses). -/
theorem coreTyped10_invoke {s : Store H} {args : List Execution.Runtime.Value} {a : Execution.Runtime.FuncAddr}
    (hs : Execution.Core.StoreOk (coreStore10 s))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Execution.Runtime.Value.toCore))
    (hwf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime)) :
    CoreTyped10 (invokeCfg10 s args a) := by
  obtain ⟨fi, ps, rs, hfi, -, hok⟩ := Execution.Core.invoke_ok hs hinv
  have hlt : a.value < s.funcs.length := by
    have := (List.getElem?_eq_some_iff.mp hfi).1
    simpa [coreStore10, Execution.Runtime.Store.toCore, Execution.Runtime.Store.mapCode] using this
  refine ⟨_, rs.toList, Lime1.Execution.Sim.refl_toCore _ ⟨hwf, ?_, ?_⟩, ?_⟩
  · intro b hb
    simp [invokeCfg10, frame0, V1.Execution.Config.toLime] at hb
  · simp only [invokeCfg10, V1.Execution.Config.toLime, V1.Execution.codeToLime_append,
      V1.Execution.map_values]
    refine (Lime1.Execution.ToCoreSim.listWF_append _ _ _).mpr
      ⟨Lime1.Execution.ToCoreSim.listWF_values _ _, ?_⟩
    simpa [Execution.Runtime.Store.mapCode, Execution.Runtime.AdminInstr.map] using hlt
  · rw [toCore_invokeCfg10]
    exact hok

end Silmaril.Wasm.SpecTec.Sim10.Valid

module

public import Silmaril.Raw.Wasm.Versions.Lime1.Execution.FromV1Pure

/-! # Operational preservation of the Wasm1 injection

The theorem preserves every individual step, hence finite runs and infinite
traces. Hosts are related by an explicit store/outcome transport; the canonical
transported host interpretation is always compatible. No typing, determinism,
or termination premise is required for the transition theorem.
-/

@[expose] public section
namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-- One source reduction maps to one target reduction, including administrative steps. -/
theorem Step.toLime {H : Type*} {source : Silmaril.Wasm.Execution.Runtime.HostSemantics H}
    {target : Lime1.Execution.HostSemantics H}
    (hosts : Runtime.HostSemantics.Compatible Func.toLime source target)
    {a b : Silmaril.Wasm.Execution.Runtime.Config H} (h : Step source a b) :
    Lime1.Execution.Step target a.toLime b.toLime := by
  induction h with
  | pure s f h => exact .pure _ _ (h.toLime f.module.types)
  | context h vs tail ih =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime] using Lime1.Execution.Step.context ih vs (codeToLime tail)
  | label h n cont ih =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, ← Expr.toLime_eq_map] using
      Lime1.Execution.Step.label ih n (Expr.toLime cont)
  | frame h n outer ih =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map] using Lime1.Execution.Step.frame ih n outer
  | localGet s f i v found =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.localGet (host := target) (s.mapCode Func.toLime) f i v found
  | localSet s f i v old found =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.localSet (host := target) (s.mapCode Func.toLime) f i v old found
  | globalGet s f i a g index found =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.globalGet (host := target) (s.mapCode Func.toLime) f i a g index found
  | globalSet s f i a g v index found mutable =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.globalSet (host := target) (s.mapCode Func.toLime) f i a g v index found mutable
  | call s f i a found =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.call (host := target) (s.mapCode Func.toLime) f i a found
  | callIndirect s f i c table a fn ft tableFound typeFound element found typeMatch =>
    have lookup : (s.mapCode Func.toLime).funcs[a.value]? = some (fn.mapCode Func.toLime) := by
      simp [found]
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.callIndirect (host := target) (s.mapCode Func.toLime) f i c table a
        (fn.mapCode Func.toLime) ft tableFound typeFound element lookup (by simpa using typeMatch)
  | callIndirectBounds s f i c table tableFound bounds =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.callIndirectBounds (host := target) (s.mapCode Func.toLime) f i c
        table tableFound bounds
  | callIndirectNull s f i c table tableFound null =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.callIndirectNull (host := target) (s.mapCode Func.toLime) f i c
        table tableFound null
  | callIndirectType s f i c table a fn ft tableFound typeFound element found mismatch =>
    have lookup : (s.mapCode Func.toLime).funcs[a.value]? = some (fn.mapCode Func.toLime) := by
      simp [found]
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.callIndirectType (host := target) (s.mapCode Func.toLime) f i c table a
        (fn.mapCode Func.toLime) ft tableFound typeFound element lookup (by simpa using mismatch)
  | invokeWasm s f a ft module fn args found arity _resultArity =>
    have lookup : (s.mapCode Func.toLime).funcs[a.value]? = some (.wasm ft module fn.toLime) := by
      simp [found, FuncInst.mapCode]
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Func.toLime] using
      Lime1.Execution.Step.invokeWasm (host := target) (s.mapCode Func.toLime) f a ft module
        fn.toLime args lookup arity
  | invokeHost s s' f a ft fn args r found arity behavior =>
    have lookup : (s.mapCode Func.toLime).funcs[a.value]? = some (.host ft fn) := by
      simp [found, FuncInst.mapCode]
    have behavior' := hosts fn s args (.returned s' r) behavior
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map] using
      Lime1.Execution.Step.invokeHost (host := target) (s.mapCode Func.toLime) (s'.mapCode Func.toLime)
        f a ft fn args r lookup arity behavior'
  | invokeHostDiverges s f a ft fn args found arity behavior =>
    have lookup : (s.mapCode Func.toLime).funcs[a.value]? = some (.host ft fn) := by
      simp [found, FuncInst.mapCode]
    have behavior' := hosts fn s args .diverged behavior
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map] using
      Lime1.Execution.Step.invokeHostDiverges (host := target) (s.mapCode Func.toLime) f a ft fn args
        lookup arity behavior'
  | intLoad s f t packed arg c a m v memory loaded =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.intLoad (host := target) (s.mapCode Func.toLime) f t packed arg c a m v memory loaded
  | intLoadTrap s f t packed arg c a m memory loaded =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.intLoadTrap (host := target) (s.mapCode Func.toLime) f t packed arg c a m memory loaded
  | floatLoad s f t arg c a m v memory loaded =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.floatLoad (host := target) (s.mapCode Func.toLime) f t arg c a m v memory loaded
  | floatLoadTrap s f t arg c a m memory loaded =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.floatLoadTrap (host := target) (s.mapCode Func.toLime) f t arg c a m memory loaded
  | intStore s f t packed arg c x a m bytes memory stored =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.intStore (host := target) (s.mapCode Func.toLime) f t packed arg c x a m bytes memory stored
  | intStoreTrap s f t packed arg c x a m memory stored =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.intStoreTrap (host := target) (s.mapCode Func.toLime) f t packed arg c x a m memory stored
  | floatStore s f t arg c x a m bytes memory stored =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.floatStore (host := target) (s.mapCode Func.toLime) f t arg c x a m bytes memory stored
  | floatStoreTrap s f t arg c x a m memory stored =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.floatStoreTrap (host := target) (s.mapCode Func.toLime) f t arg c x a m memory stored
  | memorySize s f a m memory =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.memorySize (host := target) (s.mapCode Func.toLime) f a m memory
  | memoryGrow s f a m c r bytes memory grown =>
    simpa [Silmaril.Wasm.Execution.Runtime.Config.toLime, AdminInstr.map, Instr.toLime] using
      Lime1.Execution.Step.memoryGrow (host := target) (s.mapCode Func.toLime) f a m c r bytes memory grown

/-- Finite reductions preserve their complete final configuration. -/
theorem Steps.toLime {H : Type*} {source : Silmaril.Wasm.Execution.Runtime.HostSemantics H}
    {target : Lime1.Execution.HostSemantics H}
    (hosts : Runtime.HostSemantics.Compatible Func.toLime source target)
    {a b : Silmaril.Wasm.Execution.Runtime.Config H} (h : Steps source a b) : Lime1.Execution.Steps target a.toLime b.toLime := by
  induction h with
  | refl => exact .refl
  | tail h step ih => exact ih.tail (step.toLime hosts)

/-- Infinite traces map pointwise; this does not identify divergence with stuckness. -/
theorem Diverges.toLime {H : Type*} {source : Silmaril.Wasm.Execution.Runtime.HostSemantics H}
    {target : Lime1.Execution.HostSemantics H}
    (hosts : Runtime.HostSemantics.Compatible Func.toLime source target)
    {a : Silmaril.Wasm.Execution.Runtime.Config H} (h : Diverges source a) : Lime1.Execution.Diverges target a.toLime :=
  InfiniteTrace.map (S := Lime1.Execution.Step target) Silmaril.Wasm.Execution.Runtime.Config.toLime
    (fun _ _ step => step.toLime hosts) h

/-- A canonical compatible host interpretation needs no additional host premise. -/
theorem Step.toLime_mapHost {H : Type*} {host : Silmaril.Wasm.Execution.Runtime.HostSemantics H} {a b : Silmaril.Wasm.Execution.Runtime.Config H}
    (h : Step host a b) :
    Lime1.Execution.Step (host.mapCode Func.toLime) a.toLime b.toLime :=
  h.toLime (Runtime.HostSemantics.compatible_mapCode _ _)

end Silmaril.Wasm.V1.Execution

module

public import Silmaril.Compiler.Native.Optimize.Open.Cleanup.Defs
public import Silmaril.Compiler.Native.Optimize.Open.ConstProp.Thms
public import Silmaril.Compiler.Native.Optimize.Open.CSE.Thms
public import Silmaril.Compiler.Native.Optimize.Open.DeadCode.Thms
public import Silmaril.Compiler.Native.Optimize.Open.JumpThread.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Open.Cleanup
open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Semantics

theorem shape (cfg : Config) : Mir.FuncPass.Shape (cleanupFunc cfg) := by
  rcases cfg with ⟨ssaEnabled, lambdaEnabled, cp, cse, dce, jt⟩
  constructor <;> intro function <;> cases cp <;> cases cse <;> cases dce <;> cases jt <;>
    simp only [cleanupFunc, propagate, common, dead, jumps, Bool.false_eq_true, ↓reduceIte,
      Mir.ConstProp.shape.name, Mir.ConstProp.shape.params, Mir.ConstProp.shape.results,
      Mir.ConstProp.shape.weak, Mir.ConstProp.shape.size, Mir.ConstProp.shape.refs,
      Mir.CSE.shape.name, Mir.CSE.shape.params, Mir.CSE.shape.results,
      Mir.CSE.shape.weak, Mir.CSE.shape.size, Mir.CSE.shape.refs,
      Mir.DeadCode.shape.name, Mir.DeadCode.shape.params, Mir.DeadCode.shape.results,
      Mir.DeadCode.shape.weak, Mir.DeadCode.shape.size, Mir.DeadCode.shape.refs,
      Mir.JumpThread.shape.name, Mir.JumpThread.shape.params, Mir.JumpThread.shape.results,
      Mir.JumpThread.shape.weak, Mir.JumpThread.shape.size, Mir.JumpThread.shape.refs]

theorem cleanupWith_eq_mapFuncs (cfg : Config) (units : Array Mir.Unit) :
    cleanupWith cfg units = Mir.FuncPass.mapFuncs (cleanupFunc cfg) units := by
  rcases cfg with ⟨ssaEnabled, lambdaEnabled, cp, cse, dce, jt⟩
  cases cp <;> cases cse <;> cases dce <;> cases jt <;>
    simp [cleanupWith, cleanupPasses, cleanupFunc, propagate, common, dead, jumps,
      Mir.Pass.runAll, Mir.ConstProp.run, Mir.CSE.run, Mir.CSE.pass, Mir.DeadCode.run,
      Mir.JumpThread.run, Mir.FuncPass.mapFuncs, Array.map_map, Function.comp_def]
  change units = units.map (fun unit => { unit with funcs := unit.funcs.map id })
  simp

theorem optimizeWith_eq_mapFuncs (cfg : Config) (units : Array Mir.Unit) :
    optimizeWith cfg units = Mir.FuncPass.mapFuncs (optimizeFunc cfg) units := by
  change cleanupWith cfg (if cfg.localSSA then Mir.FuncPass.mapFuncs (versionFunc cfg) units else units) = _
  rw [cleanupWith_eq_mapFuncs]
  cases enabled : cfg.localSSA <;>
    simp [optimizeFunc, enabled, Mir.FuncPass.mapFuncs, Array.map_map, Function.comp_def]

theorem optimize_name (cfg : Config) (function : Mir.Func) :
    (optimizeFunc cfg function).name = function.name := by
  rw [optimizeFunc, (shape cfg).name]
  cases cfg.localSSA <;> rfl

theorem optimize_params (cfg : Config) (function : Mir.Func) :
    (optimizeFunc cfg function).params = function.params := by
  rw [optimizeFunc, (shape cfg).params]
  cases cfg.localSSA <;> rfl

/-- Generic actual cleanup transport. Constant propagation requires its real
entry facts only when its flag is enabled; other gates need no extra premise. -/
theorem run (cfg : Config) (summaries : OpenCalls) {function : Mir.Func} {source : OpenFrame.State} {behavior : Lir.Behavior}
    (entry : cfg.constantPropagation = true → ConstProp.Entry function source)
    (executed : OpenFrame.Run summaries function source behavior) (successful : behavior ≠ .stuck) :
    OpenFrame.Run summaries (cleanupFunc cfg function) source behavior := by
  have propagated : OpenFrame.Run summaries (propagate cfg function) source behavior := by
    cases enabled : cfg.constantPropagation with
    | false => simpa only [propagate, enabled, Bool.false_eq_true, ↓reduceIte] using executed
    | true => simpa only [propagate, enabled, ↓reduceIte] using ConstProp.run summaries (entry enabled) executed successful
  have eliminated : OpenFrame.Run summaries (common cfg (propagate cfg function)) source behavior := by
    cases enabled : cfg.commonSubexpressions with
    | false => simpa only [common, enabled, Bool.false_eq_true, ↓reduceIte] using propagated
    | true => simpa only [common, enabled, ↓reduceIte] using CSE.run summaries propagated successful
  have removed : OpenFrame.Run summaries (dead cfg (common cfg (propagate cfg function))) source behavior := by
    cases enabled : cfg.deadCode with
    | false => simpa only [dead, enabled, Bool.false_eq_true, ↓reduceIte] using eliminated
    | true => simpa only [dead, enabled, ↓reduceIte] using DeadCode.run summaries eliminated successful
  cases enabled : cfg.jumpThreading with
  | false => simpa only [cleanupFunc, jumps, enabled, Bool.false_eq_true, ↓reduceIte] using removed
  | true => simpa only [cleanupFunc, jumps, enabled, ↓reduceIte] using JumpThread.run summaries removed successful

theorem run_entry_zero (cfg : Config) (summaries : OpenCalls) {function : Mir.Func}
    {frame : Lir.Frame Nat} {memory : Lir.Memory} {behavior : Lir.Behavior}
    (executed : OpenFrame.Run summaries function ⟨0, frame, memory⟩ behavior) (successful : behavior ≠ .stuck) :
    OpenFrame.Run summaries (cleanupFunc cfg function) ⟨0, frame, memory⟩ behavior :=
  run cfg summaries (fun _ => ConstProp.entry_zero function frame memory) executed successful

theorem function_call_free (cfg : Config) {function : Mir.Func} (free : OpenFrame.FunctionCallFree function) :
    OpenFrame.FunctionCallFree (cleanupFunc cfg function) := by
  have propagated : OpenFrame.FunctionCallFree (propagate cfg function) := by
    cases enabled : cfg.constantPropagation with
    | false => simpa only [propagate, enabled, Bool.false_eq_true, ↓reduceIte] using free
    | true => simpa only [propagate, enabled, ↓reduceIte] using ConstProp.function_call_free free
  have eliminated : OpenFrame.FunctionCallFree (common cfg (propagate cfg function)) := by
    cases enabled : cfg.commonSubexpressions with
    | false => simpa only [common, enabled, Bool.false_eq_true, ↓reduceIte] using propagated
    | true => simpa only [common, enabled, ↓reduceIte] using CSE.function_call_free propagated
  have removed : OpenFrame.FunctionCallFree (dead cfg (common cfg (propagate cfg function))) := by
    cases enabled : cfg.deadCode with
    | false => simpa only [dead, enabled, Bool.false_eq_true, ↓reduceIte] using eliminated
    | true => simpa only [dead, enabled, ↓reduceIte] using DeadCode.function_call_free eliminated
  cases enabled : cfg.jumpThreading with
  | false => simpa only [cleanupFunc, jumps, enabled, Bool.false_eq_true, ↓reduceIte] using removed
  | true => simpa only [cleanupFunc, jumps, enabled, ↓reduceIte] using JumpThread.function_call_free removed

theorem observations_exact (cfg : Config) (summaries : OpenCalls) {function : Mir.Func}
    (free : OpenFrame.FunctionCallFree function) (frame : Lir.Frame Nat) (memory : Lir.Memory) {behavior : Lir.Behavior}
    (executed : OpenFrame.Run summaries function ⟨0, frame, memory⟩ behavior) (successful : behavior ≠ .stuck)
    (other : Lir.Behavior) :
    OpenFrame.Behaves summaries (cleanupFunc cfg function) ⟨0, frame, memory⟩ other ↔ other = behavior := by
  have candidate : OpenFrame.Run summaries (cleanupFunc cfg function) ⟨0, frame, memory⟩ behavior :=
    run_entry_zero cfg summaries executed successful
  have candidateFree : OpenFrame.FunctionCallFree (cleanupFunc cfg function) := function_call_free cfg free
  constructor
  · intro observed
    cases other with
    | diverges => exact False.elim (OpenFrame.run_no_infinite candidateFree candidate observed)
    | returned values memory | trapped memory | stuck =>
      obtain ⟨final, steps, stopped⟩ := observed
      exact (OpenFrame.run_unique candidateFree candidate (OpenFrame.run_prepend steps (.stop stopped))).symm
  · rintro rfl
    exact OpenFrame.run_behaves candidate

end Silmaril.Compiler.Native.Optimize.Open.Cleanup

module

public import Silmaril.Compiler.Native.Optimize.Validation.Cleanup.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Finite.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Cleanup
open Silmaril.Machine Silmaril.Compile
open Silmaril.Compile.Contract

private theorem map_start {transform : Mir.Func → Mir.Func} (shape : Mir.FuncPass.Iface transform)
    {units : Array Mir.Unit} {placement : MirSem.Placement} {size : Nat} {state : MirSem.State}
    (started : MirSem.start units placement size = some state) :
    MirSem.start (Mir.FuncPass.mapFuncs transform units) placement size =
      some { state with func := transform state.func, stack := [] } := by
  simp only [MirSem.start, Option.bind_eq_some_iff, Option.map_eq_some_iff] at started
  obtain ⟨function, found, frame, entered, rfl⟩ := started
  simp [MirSem.start, Mir.FuncPass.funcDefs_eq shape, List.head?_map, found,
    Mir.FuncPass.enter_eq shape, entered, Mir.FuncPass.initMem_eq shape]

private theorem simulated_preserves {transform : Mir.Func → Mir.Func} {relation : Mir.FuncPass.PointRel}
    (shape : Mir.FuncPass.Iface transform) (simulation : Mir.FuncPass.Sim transform relation) :
    Preserves (Mir.FuncPass.mapFuncs transform) := by
  intro units placement size behavior nonstuck source
  obtain ⟨state, started, executed⟩ := source
  have related : Mir.FuncPass.Rel transform relation state { state with func := transform state.func, stack := [] } := by
    simp only [MirSem.start, Option.bind_eq_some_iff, Option.map_eq_some_iff] at started
    obtain ⟨function, found, frame, entered, rfl⟩ := started
    exact ⟨rfl, rfl, rfl, (simulation function).entry frame, .nil⟩
  exact ⟨_, map_start shape started,
    Mir.FuncPass.behaves shape simulation units placement related executed nonstuck⟩

/-- The concrete constant propagation simulation, with actual entry and memory. -/
theorem constProp_preserves : Preserves Mir.ConstProp.run :=
  simulated_preserves Mir.ConstProp.shape.iface Mir.ConstProp.sim

theorem constProp_initMem : KeepsInitialMemory Mir.ConstProp.run :=
  Mir.FuncPass.initMem_eq Mir.ConstProp.shape.iface

/-- The concrete common-subexpression simulation, at the same placement. -/
theorem cse_preserves : Preserves Mir.CSE.run :=
  simulated_preserves Mir.CSE.shape.iface Mir.CSE.sim

theorem cse_initMem : KeepsInitialMemory Mir.CSE.run :=
  Mir.FuncPass.initMem_eq Mir.CSE.shape.iface

/-- The concrete checked dead-code simulation includes its actual fallback. -/
theorem deadCode_preserves : Preserves Mir.DeadCode.run :=
  simulated_preserves Mir.DeadCode.shape.iface Mir.DeadCode.sim

theorem deadCode_initMem : KeepsInitialMemory Mir.DeadCode.run :=
  Mir.FuncPass.initMem_eq Mir.DeadCode.shape.iface

/-- Jump threading's real backward simulation covers every actual output
behavior. Existing actual behavior existence and source uniqueness turn it
into forward preservation at the exact real lifted startup. -/
theorem jumpThread_preserves : Preserves Mir.JumpThread.run := by
  intro units placement size behavior _ source
  obtain ⟨state, started, executed⟩ := source
  have emptyStack : state.stack = [] := by
    simp only [MirSem.start, Option.bind_eq_some_iff, Option.map_eq_some_iff] at started
    obtain ⟨function, found, frame, entered, rfl⟩ := started
    rfl
  have targetStart : MirSem.start (Mir.JumpThread.run units) placement size = some (Mir.JumpThread.lift state) := by
    simpa only [Mir.JumpThread.run, Mir.JumpThread.lift, emptyStack, List.map_nil] using
      map_start Mir.JumpThread.shape.iface started
  obtain ⟨actualBehavior, actualExecuted⟩ :=
    MirSem.Behaves.exists (Mir.JumpThread.run units) placement (Mir.JumpThread.lift state)
  have same : behavior = actualBehavior := MirSem.Behaves.unique executed (Mir.JumpThread.behaves actualExecuted)
  exact ⟨_, targetStart, same ▸ actualExecuted⟩

theorem jumpThread_initMem : KeepsInitialMemory Mir.JumpThread.run :=
  Mir.FuncPass.initMem_eq Mir.JumpThread.shape.iface

private theorem optional_mem {α : Type} {flag : Bool} {selected member : α}
    (inside : member ∈ (if flag then [selected] else [])) : member = selected := by
  cases flag <;> simp_all

/-- Every stage in the actual selected cleanup list has its concrete proof.
No simulation or contract is supplied by a caller. -/
theorem cleanup_passes (cfg : Config) :
    ∀ stage ∈ cleanupPasses cfg, Preserves stage.run ∧ KeepsInitialMemory stage.run := by
  intro stage member
  simp only [cleanupPasses, List.mem_append] at member
  rcases member with ((constant | common) | dead) | jump
  · have same := optional_mem constant
    subst stage
    exact ⟨constProp_preserves, constProp_initMem⟩
  · have same := optional_mem common
    subst stage
    exact ⟨cse_preserves, cse_initMem⟩
  · have same := optional_mem dead
    subst stage
    exact ⟨deadCode_preserves, deadCode_initMem⟩
  · have same := optional_mem jump
    subst stage
    exact ⟨jumpThread_preserves, jumpThread_initMem⟩

private theorem runAll_preserves (passes : List Mir.Pass)
    (proved : ∀ stage ∈ passes, Preserves stage.run) : Preserves (Mir.Pass.runAll passes) := by
  induction passes with
  | nil => exact fun _ _ _ _ _ source => source
  | cons first rest ih =>
    intro units placement size behavior nonstuck source
    have initial := proved first (by simp) units placement size behavior nonstuck source
    exact ih (fun stage member => proved stage (by simp [member]))
      (first.run units) placement size behavior nonstuck initial

private theorem runAll_initMem (passes : List Mir.Pass)
    (proved : ∀ stage ∈ passes, KeepsInitialMemory stage.run) : KeepsInitialMemory (Mir.Pass.runAll passes) := by
  induction passes with
  | nil => exact fun _ _ _ => rfl
  | cons first rest ih =>
    intro units placement size
    exact (ih (fun stage member => proved stage (by simp [member])) (first.run units) placement size).trans
      (proved first (by simp) units placement size)

/-- Same-placement preservation for the exact actual ordered cleanup list,
for every flag configuration and every real non-stuck source behavior. -/
theorem cleanup_preserves (cfg : Config) : Preserves (Mir.Pass.runAll (cleanupPasses cfg)) :=
  runAll_preserves (cleanupPasses cfg) (fun stage member => (cleanup_passes cfg stage member).1)

theorem cleanup_initMem (cfg : Config) : KeepsInitialMemory (Mir.Pass.runAll (cleanupPasses cfg)) :=
  runAll_initMem (cleanupPasses cfg) (fun stage member => (cleanup_passes cfg stage member).2)

/-- The existing optimizer, including all selected concrete cleanup passes,
preserves the same actual initial memory at the same placement. -/
theorem optimizeWith_initMem (cfg : Config) : KeepsInitialMemory (optimizeWith cfg) := by
  intro units placement size
  unfold optimizeWith
  rw [cleanup_initMem]
  cases enabled : cfg.localSSA with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]
  | true =>
    simp only [↓reduceIte]
    exact Finite.initMem_versionUnits cfg units placement size

/-- Finite successful actual source behavior from real startup is preserved by
the existing complete configured optimizer, with the same placement and exact
returned words/final memory or trapped final memory. -/
theorem optimizeWith_program (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (cfg : Config) (size : Nat) (function : Mir.Func) (frame : Lir.Frame Nat)
    (admitted : Finite.AdmittedFunction function) (outcome : Finite.Outcome)
    (started : MirSem.start units placement size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩)
    (source : MirSem.Behaves units placement
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩ outcome.behavior) :
    ProgramBehaves (optimizeWith cfg units) placement size outcome.behavior := by
  have before : ProgramBehaves
      (if cfg.localSSA then Finite.versionUnits cfg units else units) placement size outcome.behavior := by
    cases enabled : cfg.localSSA with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, started, source⟩
    | true =>
      simp only [↓reduceIte]
      exact Finite.program_behaves calls units placement cfg size function frame admitted outcome started source
  have nonstuck : outcome.behavior ≠ .stuck := by
    cases outcome <;> simp [Finite.Outcome.behavior]
  exact cleanup_preserves cfg _ placement size outcome.behavior nonstuck before

/-- The actual default optimizer uses all four cleanup passes and both local
SSA stages; no disabled-pass premise is required. -/
theorem optimize_program (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (size : Nat) (function : Mir.Func) (frame : Lir.Frame Nat)
    (admitted : Finite.AdmittedFunction function) (outcome : Finite.Outcome)
    (started : MirSem.start units placement size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩)
    (source : MirSem.Behaves units placement
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩ outcome.behavior) :
    ProgramBehaves (optimize units) placement size outcome.behavior :=
  optimizeWith_program calls units placement {} size function frame admitted outcome started source

/-- Universal uniqueness is for the existing actual relation, including
stuckness and divergence, from its exact actual startup. -/
theorem programBehaves_unique {units : Array Mir.Unit} {placement : MirSem.Placement} {size : Nat}
    {first second : Lir.Behavior} (left : ProgramBehaves units placement size first)
    (right : ProgramBehaves units placement size second) : first = second := by
  obtain ⟨sourceState, sourceStart, sourceExec⟩ := left
  obtain ⟨targetState, targetStart, targetExec⟩ := right
  have same : targetState = sourceState := Option.some.inj (targetStart.symm.trans sourceStart)
  subst targetState
  exact MirSem.Behaves.unique sourceExec targetExec

/-- Complete actual-start behavior models agree on the independent pure
finite-success source domain. Target stuckness/divergence are not filtered out;
the real target finite witness and real universal uniqueness exclude them. -/
theorem optimizeWith_models (calls : OpenCalls) (units : Array Mir.Unit) (placement : MirSem.Placement)
    (cfg : Config) (size : Nat) (function : Mir.Func) (frame : Lir.Frame Nat)
    (admitted : Finite.AdmittedFunction function) (outcome : Finite.Outcome)
    (started : MirSem.start units placement size = some
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩)
    (source : MirSem.Behaves units placement
      ⟨function, 0, 0, frame, [], MirSem.initMem units placement size⟩ outcome.behavior)
    (behavior : Lir.Behavior) :
    ProgramBehaves units placement size behavior ↔ ProgramBehaves (optimizeWith cfg units) placement size behavior := by
  have sourceWitness : ProgramBehaves units placement size outcome.behavior := ⟨_, started, source⟩
  have targetWitness := optimizeWith_program calls units placement cfg size function frame admitted outcome started source
  constructor
  · intro actual
    exact programBehaves_unique sourceWitness actual ▸ targetWitness
  · intro actual
    exact programBehaves_unique targetWitness actual ▸ sourceWitness

theorem optimize_initMem : KeepsInitialMemory optimize := optimizeWith_initMem {}

end Silmaril.Compiler.Native.Optimize.Validation.Cleanup

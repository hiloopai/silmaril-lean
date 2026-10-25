module

public import Silmaril.Wasm.Link.LeafSimulation
public import Silmaril.Wasm.Link.AdminRelation
public import Silmaril.Wasm.Link.SimulationDefs
public import Silmaril.Wasm.Link.AggregateSimulation

/-! # Leaf execution under the administrative linking relation

Runtime operands stay equal. Source annotation scopes preserve reference casts
and tests, while module views relocate global and function indices. Pure scalar
rules retain their original profile-dependent result relations.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.LeafControlSimulation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open AdminRelation

variable {H : Type}

private theorem values_instruction {mode : Mode} {left right : ModuleInst}
    {vs : List Val} {i : Instr} {code : List Execution.Core.Admin}
    (nonvalue : (Execution.Core.Admin.plain i).val? = none)
    (h : Control mode left right (vals vs ++ [.plain i]) code)
    (nonthrow : i ≠ .throwRef := by intro h; cases h) :
    ∃ j, code = vals vs ++ [.plain j] ∧ Instruction mode i j :=
  h.values_instruction nonvalue nonthrow

private theorem same_view {source target : ModuleInst} (view : View .same source target) :
    source = target := by cases view; rfl

private theorem relocated_view {r : Relocation} {source target : ModuleInst}
    (view : View (.relocated r) source target) : Views.Successful r source target := by
  cases view
  assumption

/-- Every reference rule transports across corresponding module views.
Tests and casts use the scopes supplied by source execution typing. -/
theorem reference_control {source target : Store H} {left right : Frame}
    {mode : Mode} {code out targetCode : List Execution.Core.Admin}
    (stores : StoreRelation.Related source target) (view : View mode left.module right.module)
    (scope : AdminScope.Admins left.module.types.length code)
    (step : RefStep ⟨source, left, code⟩ ⟨source, left, out⟩)
    (control : Control mode left.module right.module code targetCode) :
    RefStep ⟨target, right, targetCode⟩ ⟨target, right, out⟩ ∧
      Control mode left.module right.module out out := by
  cases mode with
  | same =>
    have modules := same_view view
    have original := step
    cases step
    all_goals
      first
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .ref _]) (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _]) (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.i32 _]) (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := []) (h := control) (by rfl)
    all_goals
      change _ = j at rewrite
      subst j
      refine ⟨LeafSimulation.reference_same stores modules original, ?_⟩
      rw [← modules]
      exact Control.same _ _
  | relocated r =>
    have views := relocated_view view
    have original := step
    cases step
    all_goals
      first
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .ref _]) (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _]) (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.i32 _]) (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := []) (h := control) (by rfl)
    all_goals
      simp only [Instruction, instruction?, Option.map_eq_map, Option.map_eq_some_iff,
        Option.some.injEq] at rewrite
    case refNull =>
      obtain ⟨ht', hht, rfl⟩ := rewrite
      exact ⟨.refNull ht', .ref .nil⟩
    case refFunc =>
      obtain ⟨y, hy, rfl⟩ := rewrite
      exact ⟨.refFunc (views.functions hy (by assumption)), .ref .nil⟩
    case testTrue =>
      obtain ⟨rt', hrt, rfl⟩ := rewrite
      exact ⟨LeafSimulation.testTrue_of_tag stores
        (ControlViews.closed_ref_type views hrt
          (by simpa [AdminScope.Admins, AdminScope.Admin, CodeScope.Instruction] using scope))
        (by assumption), .val .nil⟩
    case testFalse =>
      obtain ⟨rt', hrt, rfl⟩ := rewrite
      exact ⟨LeafSimulation.testFalse_of_tag stores
        (ControlViews.closed_ref_type views hrt
          (by simpa [AdminScope.Admins, AdminScope.Admin, CodeScope.Instruction] using scope))
        (by assumption), .val .nil⟩
    case castSucceed =>
      obtain ⟨rt', hrt, rfl⟩ := rewrite
      exact ⟨LeafSimulation.castSucceed_of_tag stores
        (ControlViews.closed_ref_type views hrt
          (by simpa [AdminScope.Admins, AdminScope.Admin, CodeScope.Instruction] using scope))
        (by assumption), .ref .nil⟩
    case castFail =>
      obtain ⟨rt', hrt, rfl⟩ := rewrite
      exact ⟨LeafSimulation.castFail_of_tag stores
        (ControlViews.closed_ref_type views hrt
          (by simpa [AdminScope.Admins, AdminScope.Admin, CodeScope.Instruction] using scope))
        (by assumption), .trap .nil⟩
    all_goals
      subst j
      refine ⟨LeafSimulation.reference_independent original (by trivial), ?_⟩
      first | exact .ref .nil | exact .val .nil | exact .trap .nil


/-- Local writes update both frames; global writes update both stores. -/
theorem variable_control {source target source' : Store H} {left right left' : Frame}
    {mode : Mode} {code out targetCode : List Execution.Core.Admin}
    (stores : StoreRelation.Related source target) (frames : Frames mode left right)
    (step : VariableStep ⟨source, left, code⟩ ⟨source', left', out⟩)
    (control : Control mode left.module right.module code targetCode) :
    ∃ target' right' targetOut,
      VariableStep ⟨target, right, targetCode⟩ ⟨target', right', targetOut⟩ ∧
      StoreRelation.Related source' target' ∧ Frames mode left' right' ∧
      Control mode left'.module right'.module out targetOut := by
  cases mode with
  | same =>
    have modules := same_view frames.view
    have original := step
    cases step
    all_goals
      first
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [_]) (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := []) (h := control) (by rfl)
    all_goals
      change _ = j at rewrite
      subst j
      obtain ⟨target', right', targetStep, related, modules', locals'⟩ :=
        LeafSimulation.variable_same stores modules frames.locals original
      refine ⟨target', right', _, targetStep, related, ⟨?_, locals'⟩, ?_⟩
      · rw [modules']; exact .same _
      · rw [← modules']; exact Control.same _ _
  | relocated r =>
    have views := relocated_view frames.view
    cases step
    all_goals
      first
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [_]) (h := control) (by rfl)
      | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := []) (h := control) (by rfl)
    all_goals
      simp only [Instruction, instruction?, Option.map_eq_map,
        Option.map_eq_some_iff, Option.some.injEq] at rewrite
    case localGet =>
      subst j
      exact ⟨_, _, _, .localGet (by rwa [Frame.local?, ← frames.locals]),
        stores, frames, .val .nil⟩
    case localSet =>
      subst j
      exact ⟨_, _, _, .localSet (by rwa [← frames.locals]), stores,
        frames.setLocal _ _, .nil⟩
    case localTee =>
      subst j
      exact ⟨_, _, _, .localTee, stores, frames, .val (.val (.plain (by simp [Instruction, instruction?]) .nil))⟩
    case globalGet =>
      obtain ⟨y, hy, rfl⟩ := rewrite
      exact ⟨_, _, _, .globalGet (LeafSimulation.global_lookup stores views hy (by assumption)),
        stores, frames, .val .nil⟩
    case globalSet =>
      obtain ⟨y, hy, rfl⟩ := rewrite
      exact ⟨_, _, _, .globalSet (LeafSimulation.global_lookup stores views hy (by assumption)),
        stores.setGlobal _ _, frames, .nil⟩


/-- Scalar numeric instructions preserve their exact result or trap in either
mode, including the original nondeterministic floating-point profile. -/
theorem numeric_control {P : Profile} {mode : Mode} {left right : ModuleInst}
    {code out targetCode : List Execution.Core.Admin} (step : NumericStep P code out)
    (control : Control mode left right code targetCode) :
    NumericStep P targetCode out ∧ Control mode left right out out := by
  have original := step
  cases step
  all_goals
    first
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction
        (vs := [.num ⟨.int _, _⟩, .num ⟨.int _, _⟩]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction
        (vs := [.num ⟨.float _, _⟩, .num ⟨.float _, _⟩]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction
        (vs := [.num ⟨.int _, _⟩]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction
        (vs := [.num ⟨.float _, _⟩]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [_]) (h := control) (by rfl)
  all_goals
    cases mode <;> simp only [Instruction, instruction?, Option.some.injEq] at rewrite <;> subst j
  all_goals
    refine ⟨original, ?_⟩
    first
    | exact .val .nil
    | exact .trap .nil
    | exact .plain (by simp [Instruction, instruction?]) .nil

/-- Vector computation remains available to unchanged ambient code. The
linker's current fragment rejects every vector operator, even though dynamic
vector values may still occur as operands in relocated code. -/
theorem vector_control {P : Profile} {mode : Mode} {left right : ModuleInst}
    {code out targetCode : List Execution.Core.Admin} (step : VectorStep P code out)
    (control : Control mode left right code targetCode) :
    VectorStep P targetCode out ∧ Control mode left right out out := by
  have original := step
  cases step
  all_goals
    first
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction
        (vs := [.vec _, .vec _, .vec _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction
        (vs := [.vec _, .vec _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction
        (vs := [.vec _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction
        (vs := [.vec _, _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.vec _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [_]) (h := control) (by rfl)
  all_goals
    cases mode <;> simp only [Instruction, instruction?, reduceCtorEq] at rewrite
  all_goals
    subst j
    refine ⟨original, ?_⟩
    first
    | exact .val .nil
    | exact .trap .nil
    | exact .plain rfl .nil


private theorem select_shape {mode : Mode} {ts : Option (List ValType)} {j : Instr}
    (rewrite : Instruction mode (.select ts) j) : ∃ ts', j = .select ts' := by
  cases mode with
  | same =>
    change _ = j at rewrite
    subst j
    exact ⟨ts, rfl⟩
  | relocated r =>
    cases ts with
    | none =>
      simp only [Instruction, instruction?, Option.some.injEq] at rewrite
      subst j
      exact ⟨none, rfl⟩
    | some ts =>
      simp only [Instruction, instruction?, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at rewrite
      obtain ⟨ts', _, rfl⟩ := rewrite
      exact ⟨some ts', rfl⟩

/-- Select may relocate its annotation; it retains the actual selected value. -/
theorem parametric_control {mode : Mode} {left right : ModuleInst}
    {code out targetCode : List Execution.Core.Admin} (step : ParametricStep code out)
    (control : Control mode left right code targetCode) :
    ParametricStep targetCode out ∧ Control mode left right out out := by
  have original := step
  cases step
  all_goals
    first
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [_, _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [_]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := []) (h := control) (by rfl)
  case selectTrue =>
    obtain ⟨ts', rfl⟩ := select_shape rewrite
    exact ⟨.selectTrue (by assumption), .val .nil⟩
  case selectFalse =>
    obtain ⟨ts', rfl⟩ := select_shape rewrite
    exact ⟨.selectFalse _ _ _, .val .nil⟩
  all_goals
    cases mode <;> simp only [Instruction, instruction?, Option.some.injEq] at rewrite <;> subst j
  all_goals
    refine ⟨original, ?_⟩
    first | exact .nil | exact .trap .nil


open Simulation

variable {P : Profile} {host : HostSemantics H}

/-- Lift the pure parametric family to paired whole configurations. -/
theorem parametric {mode : Mode} {source target : Config H} {out : List Execution.Core.Admin}
    (step : ParametricStep source.code out) (matching : Matching mode source target) :
    ∃ target', Step P host target target' ∧
      Matching mode ⟨source.store, source.frame, out⟩ target' := by
  obtain ⟨actual, code⟩ := parametric_control step matching.code
  exact ⟨⟨target.store, target.frame, out⟩, .parametric actual,
    ⟨matching.stores, matching.frames, code⟩⟩

/-- Scalar numeric steps preserve paired configurations. -/
theorem numeric {mode : Mode} {source target : Config H} {out : List Execution.Core.Admin}
    (step : NumericStep P source.code out) (matching : Matching mode source target) :
    ∃ target', Step P host target target' ∧
      Matching mode ⟨source.store, source.frame, out⟩ target' := by
  obtain ⟨actual, code⟩ := numeric_control step matching.code
  exact ⟨⟨target.store, target.frame, out⟩, .numeric actual,
    ⟨matching.stores, matching.frames, code⟩⟩

/-- Unchanged ambient vector steps preserve paired configurations. -/
theorem vector {mode : Mode} {source target : Config H} {out : List Execution.Core.Admin}
    (step : VectorStep P source.code out) (matching : Matching mode source target) :
    ∃ target', Step P host target target' ∧
      Matching mode ⟨source.store, source.frame, out⟩ target' := by
  obtain ⟨actual, code⟩ := vector_control step matching.code
  exact ⟨⟨target.store, target.frame, out⟩, .vector actual,
    ⟨matching.stores, matching.frames, code⟩⟩

private theorem reference_shape {source result : Config H} (step : RefStep source result) :
    result.store = source.store ∧ result.frame = source.frame := by
  cases step <;> exact ⟨rfl, rfl⟩

/-- The reference family lifts scoped casts and tests to paired configurations. -/
theorem reference {mode : Mode} {source source' target : Config H}
    (step : RefStep source source') (matching : Matching mode source target)
    (scope : AdminScope.Admins source.frame.module.types.length source.code) :
    ∃ target', Step P host target target' ∧ Matching mode source' target' := by
  rcases source' with ⟨store', frame', out⟩
  obtain ⟨storesEqual, framesEqual⟩ := reference_shape step
  change store' = source.store at storesEqual
  change frame' = source.frame at framesEqual
  subst store'
  subst frame'
  obtain ⟨actual, code⟩ := reference_control matching.stores matching.frames.view scope step matching.code
  exact ⟨⟨target.store, target.frame, out⟩, .reference actual,
    ⟨matching.stores, matching.frames, code⟩⟩

/-- Local and global updates lift to paired configurations. -/
theorem «variable» {mode : Mode} {source source' target : Config H}
    (step : VariableStep source source') (matching : Matching mode source target) :
    ∃ target', Step P host target target' ∧ Matching mode source' target' := by
  rcases source with ⟨store, frame, code⟩
  rcases source' with ⟨store', frame', out⟩
  rcases target with ⟨targetStore, targetFrame, targetCode⟩
  obtain ⟨resultStore, resultFrame, resultCode, actual, stores, frames, resultControl⟩ :=
    variable_control matching.stores matching.frames step matching.code
  exact ⟨⟨resultStore, resultFrame, resultCode⟩, .variable actual,
    ⟨stores, frames, resultControl⟩⟩

private theorem aggregate_frame {source result : Config H} (step : AggregateStep source result) :
    result.frame = source.frame := by
  cases step <;> rfl

/-- Matching heap allocation, mutation, traps and copy/fill unrolling lift to
paired whole configurations. -/
theorem aggregate_step {mode : Mode} {source source' target : Config H}
    (step : AggregateStep source source') (matching : Matching mode source target) :
    ∃ target', Step P host target target' ∧ Matching mode source' target' := by
  rcases source' with ⟨store', frame', out⟩
  have framesEqual := aggregate_frame step
  change frame' = source.frame at framesEqual
  subst frame'
  obtain ⟨resultStore, resultCode, actual, stores, code⟩ :=
    AggregateSimulation.aggregate matching.stores matching.frames.view step matching.code
  exact ⟨⟨resultStore, target.frame, resultCode⟩, .aggregate actual,
    ⟨stores, matching.frames, code⟩⟩

end Silmaril.Wasm.Link.GC.LeafControlSimulation

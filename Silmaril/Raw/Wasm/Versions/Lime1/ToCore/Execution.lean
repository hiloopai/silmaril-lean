module

public import Silmaril.Foundations.ForwardSim
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Runtime
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.Context
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.Variable
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.Call
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.Memory
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.PureBasic
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.PureAdmin
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.PureBlock
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.MemoryCopy
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.MemoryFill

@[expose] public section

/-! # Lime1 execution is simulated by Core 3.0 execution (milestones U23–U25)

Forward simulation into `TransGen` (one Lime1 step is one or more Core steps),
over the simulation relation `Sim` of `Lime1/ToCore/Runtime.lean`, for the spec
semantics `Profile.spec` (NaN sets and nondeterministic grow failure, which is
exactly Lime1's nondeterminism). `Step.toCore` is therefore a
`Silmaril.LockstepSim` (`Foundations/ForwardSim.lean`), and finite runs
(`Steps.toCore`) and divergence (`Diverges.toCore`, which is why `TransGen`
rather than `ReflTransGen` is needed) are that kit's generic consequences.
Result transport (`Sim.result`) is not uniform across the subset theorems and
stays here, as does instantiation.

Multi-step cases: `call` (Core: `call → ref.func; call_ref`, then the call),
`call_indirect` (Core: `table.get; ref.cast; call_ref`, with `Type` traps as cast
failures, relying on `V1.FuncType.toDefType_sub_iff`).
-/

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution (Runtime.Result Runtime.ExternVal Runtime.ModuleInst)

variable {H : Type}

/-- Core profile used for the subset theorems. -/
abbrev coreProfile : Profile := Profile.spec

/-- **Milestone.** One Lime1 step is simulated by at least one Core step. -/
theorem Step.toCore {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {a b : Config H} {c : ToCore.CConfig H}
    (h : Step src a b) (hs : Sim a c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step coreProfile tgt) c c' ∧ Sim b c' := by
  induction h generalizing c with
  | context h vs tail ih =>
    exact ToCoreSim.context (fun _ h => ih h) (ToCoreSim.storeExt hosts.1 h hs.2.1) (ToCoreSim.module_eq h)
      vs tail hs
  | label h n cont ih => exact ToCoreSim.label (fun _ h => ih h) n cont hs
  | frame h n outer ih =>
    exact ToCoreSim.frame (fun _ h => ih h) (ToCoreSim.storeExt hosts.1 h hs.2.1) n outer hs
  | pure s f hp =>
    cases hp with
    | nop => exact ToCoreSim.pure_nop hs
    | unreachable => exact ToCoreSim.pure_unreachable hs
    | drop v => exact ToCoreSim.pure_drop hs
    | selectZero a b st => exact ToCoreSim.pure_selectZero st hs
    | selectNonzero a b st cc hc => exact ToCoreSim.pure_selectNonzero st hc hs
    | block => exact ToCoreSim.pure_block ‹_› ‹_› hs
    | loop => exact ToCoreSim.pure_loop ‹_› ‹_› hs
    | ifZero => exact ToCoreSim.pure_ifZero hs
    | ifNonzero => exact ToCoreSim.pure_ifNonzero ‹_› hs
    | brIfZero => exact ToCoreSim.pure_brIfZero hs
    | brIfNonzero => exact ToCoreSim.pure_brIfNonzero ‹_› hs
    | brTable => exact ToCoreSim.pure_brTable hs
    | labelDone n cont vs => exact ToCoreSim.pure_labelDone hs
    | labelBranch n cont extra vs tail ar => exact ToCoreSim.pure_labelBranch ar hs
    | labelBranchOuter n cont vs tail l ho => exact ToCoreSim.pure_labelBranchOuter ho hs
    | labelReturn n cont vs tail => exact ToCoreSim.pure_labelReturn hs
    | frameDone n fr vs ar => exact ToCoreSim.pure_frameDone ar hs
    | frameReturn n fr extra vs tail ar => exact ToCoreSim.pure_frameReturn ar hs
    | trapValues v vs tail => exact ToCoreSim.pure_trapValues hs
    | trapTail i tail => exact ToCoreSim.pure_trapTail hs
    | labelTrap n cont => exact ToCoreSim.pure_labelTrap hs
    | frameTrap n fr => exact ToCoreSim.pure_frameTrap hs
    | localTee i v => exact ToCoreSim.pure_localTee hs
    | intUnary t op x hv => exact ToCoreSim.pure_intUnary hv hs
    | intBinary t op x y z hz => exact ToCoreSim.pure_intBinary hz hs
    | intBinaryTrap t op x y err he => exact ToCoreSim.pure_intBinaryTrap he hs
    | intTest t op x => exact ToCoreSim.pure_intTest hs
    | intRel t op x y => exact ToCoreSim.pure_intRel hs
    | floatUnary t op x y hr => exact ToCoreSim.pure_floatUnary hr hs
    | floatBinary t op x y z hr => exact ToCoreSim.pure_floatBinary hr hs
    | floatRel t op x y => exact ToCoreSim.pure_floatRel hs
    | convert op x y hr => exact ToCoreSim.pure_convert hr hs
    | convertTrap op x err hr => exact ToCoreSim.pure_convertTrap hr hs
  | localGet s f i v found => exact ToCoreSim.localGet found hs
  | localSet s f i v old found => exact ToCoreSim.localSet found hs
  | globalGet s f i a g index found => exact ToCoreSim.globalGet index found hs
  | globalSet s f i a g v index found mutable => exact ToCoreSim.globalSet index found mutable hs
  | call s f i a found => exact ToCoreSim.call found hs
  | callIndirect s f i cc table a fn ft tf tyf el found tm =>
    exact ToCoreSim.callIndirect tf tyf el found tm hs
  | callIndirectBounds s f i cc table tf oob => exact ToCoreSim.callIndirectBounds tf oob hs
  | callIndirectNull s f i cc table tf nl => exact ToCoreSim.callIndirectNull tf nl hs
  | callIndirectType s f i cc table a fn ft tf tyf el found tm =>
    exact ToCoreSim.callIndirectType tf tyf el found tm hs
  | invokeWasm s f a ft module fn args found arity => exact ToCoreSim.invokeWasm found arity hs
  | invokeHost s s' f a ft fn args r found arity behavior =>
    exact ToCoreSim.invokeHost hosts found arity behavior hs
  | invokeHostDiverges s f a ft fn args found arity behavior =>
    exact ToCoreSim.invokeHostDiverges hosts found arity behavior hs
  | intLoad s f t packed arg cc a m v memory loaded => exact ToCoreSim.intLoad memory loaded hs
  | intLoadTrap s f t packed arg cc a m memory loaded =>
    exact ToCoreSim.intLoadTrap memory loaded hs
  | floatLoad s f t arg cc a m v memory loaded => exact ToCoreSim.floatLoad memory loaded hs
  | floatLoadTrap s f t arg cc a m memory loaded => exact ToCoreSim.floatLoadTrap memory loaded hs
  | intStore s f t packed arg cc x a m bytes memory stored =>
    exact ToCoreSim.intStore memory stored hs
  | intStoreTrap s f t packed arg cc x a m memory stored =>
    exact ToCoreSim.intStoreTrap memory stored hs
  | floatStore s f t arg cc x a m bytes memory stored => exact ToCoreSim.floatStore memory stored hs
  | floatStoreTrap s f t arg cc x a m memory stored =>
    exact ToCoreSim.floatStoreTrap memory stored hs
  | memorySize s f a m memory => exact ToCoreSim.memorySize memory hs
  | memoryGrow s f a m cc r bytes memory grown => exact ToCoreSim.memoryGrow memory grown hs
  | memoryCopy => exact ToCoreSim.memoryCopy ‹_› ‹_› hs
  | memoryCopyTrap => exact ToCoreSim.memoryCopyTrap ‹_› ‹_› hs
  | memoryFill => exact ToCoreSim.memoryFill ‹_› ‹_› hs
  | memoryFillTrap => exact ToCoreSim.memoryFillTrap ‹_› ‹_› hs

/-- **Milestone.** Finite runs are simulated. -/
theorem Steps.toCore {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {a b : Config H} {c : ToCore.CConfig H}
    (h : Steps src a b) (hs : Sim a c) :
    ∃ c', Silmaril.Wasm.Execution.Core.Steps coreProfile tgt c c' ∧ Sim b c' :=
  LockstepSim.steps (R := Sim) ⟨Step.toCore hosts⟩ h hs

/-- **Milestone.** Divergence is preserved. -/
theorem Diverges.toCore {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {a : Config H} {c : ToCore.CConfig H}
    (h : Diverges src a) (hs : Sim a c) :
    Silmaril.Wasm.Execution.Core.Diverges coreProfile tgt c :=
  LockstepSim.diverges (R := Sim) ⟨Step.toCore hosts⟩ h hs

/-- A terminal Lime1 result is a terminal Core result. -/
theorem Sim.result {a : Config H} {c : ToCore.CConfig H} {r : Runtime.Result}
    (hs : Sim a c) (hr : a.code = result r) : c.code = r.toCore.toAdmin := by
  obtain ⟨hn, -⟩ := hs
  obtain ⟨cs, cf, cl⟩ := c
  rw [ToCore.Config.norm_eq_toCore_iff] at hn
  obtain ⟨-, -, hl⟩ := hn
  rw [hr] at hl
  cases r with
  | values vs =>
    simp only [Silmaril.Wasm.Lime1.Execution.result, values_toCore] at hl
    show cl = Silmaril.Wasm.Execution.Core.vals _
    exact ToCore.map_norm_vals hl
  | trap =>
    simp only [Silmaril.Wasm.Lime1.Execution.result, listToCore_cons, trap_toCore, listToCore_nil,
      List.append_nil] at hl
    show cl = [.trap]
    exact ToCore.map_norm_eq_of_rigid (by simp [ToCore.Rigid]) hl

end Silmaril.Wasm.Lime1.Execution

module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Suite
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Execution
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Producer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Consumer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Definition
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Functions (Program DeclarationId Actual BoundArguments prepareExpanded activate)
open Defaults.Nested.Sequence (PreservesDeclarations)
open Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Defaults.Nested.Sequence.Recursive.Call.Named (SiteBinding)
open Lists (State)
open Loader (Session)

/-- The independent positional binder supplies the wrapper's own slots
in declaration order. Required positional formals introduce no defaults. -/
theorem wrapper_positional_binding {importName aliases globals}
    (relay : WrapperDeclaration importName aliases globals) (positionalOnly : relay.keywordOnly = [])
    (noVarargs : relay.varargs = none) (requiredOnly : relay.parameters.optional = [])
    {values : List Lists.Value}
    {result : Except Lists.Error (List (Binding × Lists.Value))}
    (checked : relay.site.declaration.signature.validate = .ok ())
    (source : Entry.Binds relay.parameters.required values result) :
    Functions.bindArguments relay.site.declaration.signature [] ⟨values, []⟩ =
      result.map (fun bound => ⟨bound, [], []⟩) := by
  rw [Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.wrapper_required_signature relay positionalOnly noVarargs requiredOnly] at checked ⊢
  exact Entry.required_binds checked source

/-- Preparing a positional call uses the actual saved values of the reached
wrapper. Omitted arguments, explicit overrides and arity failures use the
ordinary binder, with the original capture vector on success. -/
theorem wrapper_prepare_saved {importName aliases globals}
    (relay : WrapperDeclaration importName aliases globals) (positionalOnly : relay.keywordOnly = [])
    (noVarargs : relay.varargs = none) {commands : List Command} {seed : Program} {resolved : ResolvedModule}
    (checked : resolve commands seed = .ok resolved) (id : DeclarationId)
    (available : List DeclarationId) (permitted : id ∈ available)
    (found : resolved.program[id]? = some relay.site.declaration)
    {state defining : State} {address : Nat} (record : ClosureAt relay.site id defining state address)
    {actuals : List Lists.Value} {result : Except Lists.Error (List (Binding × Lists.Value))}
    (source : Defaults.Binds (relay.parameters.slots record.defaults) actuals result) :
    prepareExpanded resolved.program available ⟨actuals, []⟩ (.function address) state =
      match result with
      | .error error => .error error state
      | .ok assigned => .ok (.closure ⟨id, permitted, relay.site.declaration.body⟩)
        (activate state relay.site.declaration record.captures assigned) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.wrapper_prepare_saved
    relay positionalOnly noVarargs checked id available permitted found record source

/-- The ordinary named binder prepares the reached wrapper using its saved
defaults. A binding failure leaves the operand state intact. Success
activates the original capture vector without either collector allocation. -/
theorem wrapper_prepare_named {importName aliases globals}
    (relay : WrapperDeclaration importName aliases globals) (noVarargs : relay.varargs = none) (program : Program)
    (id : DeclarationId) (available : List DeclarationId) (permitted : id ∈ available)
    (found : program[id]? = some relay.site.declaration)
    {state defining : State} {address : Nat} (record : ClosureAt relay.site id defining state address)
    (actual : Actual) {result : Except Lists.Error BoundArguments}
    (binding : SiteBinding relay.site record.defaults actual result) :
    prepareExpanded program available actual (.function address) state =
      match result with
      | .error error => .error error state
      | .ok assigned => .ok (.closure ⟨id, permitted, relay.site.declaration.body⟩)
        (activate state relay.site.declaration record.captures assigned.named) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.wrapper_prepare_named
    relay noVarargs program id available permitted found record actual binding

/-- After ordinary positional and named binding, pack the exact surplus
in encounter order at a fresh address. The empty tuple has its canonical
key. Preparation preserves the original capture vector and retains the
operand heap, including on binding failure. -/
theorem wrapper_prepare_varargs {importName aliases globals}
    (relay : WrapperDeclaration importName aliases globals) {collector : String}
    (positionalCollector : relay.varargs = some collector) (program : Program)
    (id : DeclarationId) (available : List DeclarationId) (permitted : id ∈ available)
    (found : program[id]? = some relay.site.declaration)
    {state defining : State} {address : Nat} (record : ClosureAt relay.site id defining state address)
    (actual : Actual) {result : Except Lists.Error BoundArguments}
    (binding : SiteBinding relay.site record.defaults actual result) :
    match result with
    | .error error => prepareExpanded program available actual (.function address) state = .error error state
    | .ok bound =>
      let surplus := actual.positional.drop relay.site.declaration.signature.positional.length
      let assigned := (fileSlot collector, .tuple state.heap.size) :: bound.named
      ∃ packed, Defaults.Body.Keeps state.heap.size state packed ∧ packed.bindings = state.bindings ∧
        Lists.tupleElements state.heap.size packed = .ok surplus packed ∧
        (surplus = [] → packed.heap[state.heap.size]? = some ⟨.tuple [] (some [.openTuple, .closeTuple]), false⟩) ∧
        prepareExpanded program available actual (.function address) state =
          .ok (.closure ⟨id, permitted, relay.site.declaration.body⟩)
            (activate packed relay.site.declaration record.captures assigned) := by
  have prepared := Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.wrapper_prepare_varargs
    relay positionalCollector program id available permitted found record actual binding
  cases result <;> exact prepared

/-- The importer elaborates in source order and appends each declaration to the linked table. -/
theorem consumer_layout (plan : Consumer) {program : Program} {consumer : ResolvedModule}
    (checked : resolve plan.commands program = .ok consumer) :
    consumer.program = (compileSuite program plan.body).2 ∧ consumer.source.commands = plan.code program ∧
    consumer.source.globals = plan.globals ∧ consumer.source.fileNames = [plan.alias] :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.consumer_layout
    plan checked

/-- All producer declaration lookups survive a checked importer suite. -/
theorem consumer_preserves (plan : Consumer) {program : Program} {consumer : ResolvedModule}
    (checked : resolve plan.commands program = .ok consumer) :
    PreservesDeclarations program consumer.program :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.consumer_preserves plan checked

/-- Leading loads preserve declaration indices, while the suite appends checked definitions. -/
theorem ordered_preserves (plan : OrderedConsumer) {program : Program} {consumer : ResolvedModule}
    (checked : resolve plan.commands program = .ok consumer) :
    PreservesDeclarations program consumer.program :=
  (Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.ordered_layout plan checked).1.symm ▸
    Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.preserves_suite plan.body program

/-- Preserving the heap entries transports the exact published callable,
including the original frozen closure record and its captures. -/
theorem cached_publication {exports : Environment} {program : Program} {published : Modules.Published}
    {state next : State} (live : PublishedLive exports program published state)
    (kept : ∀ (address : Nat) cell, state.heap[address]? = some cell → next.heap[address]? = some cell) :
    PublishedLive exports program published next :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.cached_publication live kept

/-- The finite importer suite derives the exact first error or final live bindings. -/
theorem run_suite {source : List Command} {seed producer : Program} {resolved : ResolvedModule}
    (checked : resolve source seed = .ok resolved)
    {manifest : Modules.Loader.Manifest} {active : List Nat} {id : Nat}
    {aliases globals : List String} (separate : ∀ name ∈ globals, name ∉ aliases)
    (steps : List (Step aliases globals)) (prefixTable : Program)
    (producerPrefix : PreservesDeclarations producer prefixTable)
    (table : PreservesDeclarations (compileSuite prefixTable steps).2 resolved.program)
    {env : Tracked} (admitted : ReadyFor prefixTable env steps)
    (unique : (steps.map Step.destination).Nodup)
    (session : Session) (frame : Frame aliases globals session.runtime)
    (pending : ∀ step ∈ steps, Blank session.runtime (globalSlot step.destination))
    (live : Live aliases producer resolved.program env session.runtime) :
    ∃ out, SuiteRuns prefixTable session.runtime steps out ∧
      Modules.Loader.Runs resolved.program manifest active (.commands id (compileSuite prefixTable steps).1) session
        (Modules.Loader.liftResult id session out) ∧
      ∀ reached, out = .ok () reached →
        Frame aliases globals reached ∧ Live aliases producer resolved.program (trackSuite prefixTable env steps) reached :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.run_suite
    checked separate steps prefixTable producerPrefix table admitted unique session frame pending live

/-- Cold loader agreement derives imported and consumer-owned callable provenance from reached bindings. -/
theorem cold_agrees {commands : List Command} {linked final : Program}
    {code : List Modules.Command} {producer consumer : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (producerChecked : resolve commands linked = .ok producer)
    (plan : Consumer) (consumerChecked : resolve plan.commands producer.program = .ok consumer)
    (covered : Covered exports commands plan producer.program) (caller : State) :
    Agrees commands producer consumer plan exports ⟨caller, []⟩ :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.cold_agrees
    profile producerChecked plan consumerChecked covered caller

/-- An actual producer preload establishes the cache publication and closure records reused by the importer. -/
theorem preloaded_agrees {commands : List Command} {linked final : Program}
    {code : List Modules.Command} {producer consumer : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (producerChecked : resolve commands linked = .ok producer)
    (plan : Consumer) (consumerChecked : resolve plan.commands producer.program = .ok consumer)
    (covered : Covered exports commands plan producer.program) (caller : State) :
    ∃ preload, Producer commands producer.source ⟨caller, []⟩ preload ∧
      Modules.Loader.load consumer.program (graph producer consumer plan) 0 ⟨caller, []⟩ = preload ∧
      ∀ published reached, preload = .ok published reached →
        reached.cache = [(0, published)] ∧ Agrees commands producer consumer plan exports reached :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.preloaded_agrees
    profile producerChecked plan consumerChecked covered caller

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

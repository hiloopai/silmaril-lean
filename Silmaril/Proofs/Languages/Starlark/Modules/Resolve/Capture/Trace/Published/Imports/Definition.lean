module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms
import Silmaril.Languages.Starlark.Modules.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (compile_site parameterNames site_slots lexical_defaults default_layout)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
  (resolves_at runs_at SiteBinding Packs prepare_exact packed_tuple packed_empty_key binding_positional_surplus)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (Capture Cell Slot State Outcome)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

theorem wrapper_import_origin {importName aliases globals} (relay : WrapperDeclaration importName aliases globals) :
    importName ∉ relay.site.block.owned ∧ importName ∈ relay.site.block.enclosing := by
  change importName ∉ (wrapperBlock relay.parameters relay.keywordOnly relay.varargs aliases globals).owned ∧ importName ∈ aliases ++ []
  exact ⟨by simpa [wrapperBlock] using relay.unshadowed,
    by simpa using relay.visible⟩

theorem wrapper_signature {importName aliases globals} (relay : WrapperDeclaration importName aliases globals)
    (positionalOnly : relay.keywordOnly = []) (noVarargs : relay.varargs = none) :
    relay.site.declaration.signature = relay.parameters.signature (relay.defaults.map PlainPositionalDefault.value) := by
  simp [WrapperDeclaration.site, Nested.Sequence.Recursive.Site.declaration, Parameters.signature, positionalOnly, noVarargs]

theorem wrapper_required_signature {importName aliases globals} (relay : WrapperDeclaration importName aliases globals)
    (positionalOnly : relay.keywordOnly = []) (noVarargs : relay.varargs = none) (requiredOnly : relay.parameters.optional = []) :
    relay.site.declaration.signature = requiredSignature relay.parameters.required := by
  rw [wrapper_signature relay positionalOnly noVarargs]
  simp [Parameters.signature, requiredOnly, requiredSignature]

theorem wrapper_import_slot {importName aliases globals}
    (relay : WrapperDeclaration importName aliases globals) (state : State) (cell : Nat)
    (assigned : List (Binding × Lists.Value)) :
    (activate state relay.site.declaration [⟨fileSlot importName, cell, true⟩] assigned).slots (fileSlot importName) =
      some (.captured cell true) := by
  let capture : Capture := ⟨fileSlot importName, cell, true⟩
  apply activate_capture state relay.site.declaration [capture] capture assigned (by simp [capture])
  change fileSlot importName ∉ relay.site.declaration.signature.slots ++ relay.site.declaration.locals
  rw [site_slots]
  intro member
  obtain ⟨name, declared, same⟩ := List.mem_map.mp member
  have equal : name = importName := congrArg Binding.name same
  exact (wrapper_import_origin relay).1 (equal ▸ declared)

theorem wrapper_compiles {importName aliases globals} (relay : WrapperDeclaration importName aliases globals) (program : Program) :
    elaborateCommand ⟨(block aliases globals).context, .global⟩ (.define relay.name relay.site.sourceSignature relay.site.source)
      program = .ok (.exec (.define relay.name program.size), program.push relay.site.declaration) := by
  obtain ⟨notOwned, enclosing⟩ := wrapper_import_origin relay
  have imported : Body.Operand relay.site.block (.scalar (.read importName))
      (Leaf.readOperand (fileSlot importName)) [fileSlot importName] :=
    .read relay.legalAlias
      (.enclosing notOwned enclosing) (.enclosing notOwned enclosing)
  have compiled : compileBody ⟨relay.site.block.context, .local⟩ relay.site.source program =
      .ok (relay.site.body, program) :=
    compileBody_plainReturn _ _ _ _ _
      (resolves_at _ imported relay.operands relay.keywords relay.star relay.mapping)
  exact elaborateCommand_nativeDefinition ⟨(block aliases globals).context, .local⟩ .global
    relay.name relay.site.sourceSignature relay.site.source program (program.push relay.site.declaration)
    _ _ (compile_site relay.site relay.keywordLexical compiled)

theorem wrapper_returns {importName aliases globals} (relay : WrapperDeclaration importName aliases globals) {producer : Program} {consumer : ResolvedModule}
    {commands : List Modules.Resolve.Command} {seed : Program}
    (checked : resolve commands seed = .ok consumer) {callee : Callable}
    (extension : PreservesDeclarations producer consumer.program) (id : DeclarationId)
    (after : producer.size ≤ id)
    (known : callee.Linked producer) {installed defining : State} {origin aliasCell : Nat} {frozen : Bool}
    (record : ClosureAt callee.site callee.id defining installed origin)
    (aliasStored : installed.heap[aliasCell]? = some ⟨.binding (some (.function origin)), frozen⟩)
    (packed : State) (kept : Body.Keeps installed.heap.size installed packed) (assigned : List (Binding × Lists.Value)) :
    let capture : Capture := ⟨fileSlot importName, aliasCell, true⟩
    let active := activate packed relay.site.declaration [capture] assigned
    ∃ out, relay.Returns callee active out ∧
      Exec consumer.program (withoutDeclaration (List.range consumer.program.size) id)
        active relay.site.body.code out ∧
      Body.Keeps packed.heap.size packed (finishState (Leaf.returnTo packed out)) := by
  intro capture active
  let available := withoutDeclaration (List.range consumer.program.size) id
  have guarded : List.Subset (List.range producer.size) available := by
    intro index member
    have bound := List.mem_range.mp member
    have found : producer[index]? = some producer[index] := Array.getElem?_eq_getElem bound
    exact mem_withoutDeclaration.mpr ⟨List.mem_range.mpr (Array.getElem?_eq_some_iff.mp (extension _ _ found)).choose,
      Nat.ne_of_lt (Nat.lt_of_lt_of_le bound after)⟩
  have native := enter_callable_for checked known extension available guarded
  have extended := linked_extends known extension
  have present : callee.id ∈ available :=
    guarded (List.mem_range.mpr (Array.getElem?_eq_some_iff.mp known.1).choose)
  have captures : active.slots (fileSlot importName) = some (.captured aliasCell true) :=
    wrapper_import_slot relay packed aliasCell assigned
  have stored := kept.2 _ _ (Array.getElem?_eq_some_iff.mp aliasStored).choose aliasStored
  have sameHeap (address : Nat) (cell : Cell) (found : packed.heap[address]? = some cell) :
      active.heap[address]? = some cell :=
    (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.activation_preserves packed
      relay.site.declaration [capture] assigned address (Array.getElem?_eq_some_iff.mp found).choose).trans found
  have aliasRead : active.bindingValue (fileSlot importName) = .ok (.function origin) := by
    simp [State.bindingValue, captures, Slot.address, sameHeap _ _ stored]
  obtain ⟨notOwned, enclosing⟩ := wrapper_import_origin relay
  have read := Body.Evaluates.read (state := active)
    (Assignment.ReadResolves.enclosing (block := relay.site.block) (name := importName)
      notOwned enclosing)
  change Body.Evaluates _ _ _ _ (active.read (.bound (fileSlot importName))) at read
  rw [State.read, aliasRead] at read
  obtain ⟨packedRecord⟩ := keep_record record kept
  let reached : ClosureAt callee.site callee.id defining active origin := {
    packedRecord with
    recorded := sameHeap _ _ packedRecord.recorded
    live := fun selected member => by
      obtain ⟨value, flag, found⟩ := packedRecord.live selected member
      exact ⟨value, flag, sameHeap _ _ found⟩ }
  obtain ⟨result, source, exec, _, preserved⟩ :=
    runs_at callee.site callee.BodyRuns checked callee.id extended.1 available present
      native (fileSlot importName) read reached relay.operands relay.keywords relay.star relay.mapping
  have finished : finishState (result.resume (fun value => pure (Flow.returned value))) = finishState result := by
    cases result <;> rfl
  refine ⟨_, ⟨result, source, rfl⟩, .returnExpr exec, Body.returned_keeps packed relay.site.declaration
    [capture] assigned _ ?_⟩
  rw [finished]
  exact ⟨preserved.1, fun address cell _ found => preserved.2 address cell
    (Array.getElem?_eq_some_iff.mp found).choose found⟩

private theorem wrapper_positional_sources {importName aliases globals}
    (relay : WrapperDeclaration importName aliases globals) (positionalOnly : relay.keywordOnly = []) :
    relay.site.defaultSources = relay.parameters.optional := by
  cases relay
  cases positionalOnly
  rfl

theorem wrapper_prepare_saved {importName aliases globals}
    (relay : WrapperDeclaration importName aliases globals) (positionalOnly : relay.keywordOnly = []) (noVarargs : relay.varargs = none)
    {commands : List Modules.Resolve.Command} {seed : Program} {resolved : ResolvedModule}
    (checked : resolve commands seed = .ok resolved) (id : DeclarationId)
    (available : List DeclarationId) (permitted : id ∈ available)
    (found : resolved.program[id]? = some relay.site.declaration)
    {state defining : State} {address : Nat} (record : ClosureAt relay.site id defining state address)
    {actuals : List Lists.Value} {result : Except Lists.Error (List (Binding × Lists.Value))}
    (source : Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Binds (relay.parameters.slots record.defaults) actuals result) :
    prepareExpanded resolved.program available ⟨actuals, []⟩ (.function address) state =
      match result with
      | .error error => .error error state
      | .ok assigned => .ok (.closure ⟨id, permitted, relay.site.declaration.body⟩)
        (activate state relay.site.declaration record.captures assigned) := by
  have count : (relay.defaults.map PlainPositionalDefault.value).length = relay.parameters.optional.length := by
    simpa using congrArg List.length (Lexical.translates relay.lexical).1
  have agreement := Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.checked_prepare_positional checked id available permitted relay.parameters relay.site.declaration
    _ found (wrapper_signature relay positionalOnly noVarargs)
    count state address record.frozen record.captures record.defaults actuals
    (by simpa only [wrapper_positional_sources relay positionalOnly] using record.length)
    (by simpa only [Nested.Sequence.Recursive.Site.defaultKeys, wrapper_positional_sources relay positionalOnly]
      using record.recorded) source
  cases result <;> exact agreement

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
        (activate state relay.site.declaration record.captures assigned.named) := by
  have prepared := prepare_exact relay.site program available id permitted found record actual binding
  cases result with
  | error => exact prepared
  | ok bound =>
    obtain ⟨assigned, packed, packing, _, _, agreed⟩ := prepared
    have varargs : relay.site.declaration.signature.varargs = none := by
      change relay.varargs.map fileSlot = none
      rw [noVarargs]
      rfl
    change Packs relay.site.declaration.signature.varargs none state bound assigned packed at packing
    rw [varargs] at packing
    obtain ⟨_, _, positional, keywords⟩ := packing
    cases positional
    cases keywords
    exact agreed

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
      ∃ packed, Body.Keeps state.heap.size state packed ∧ packed.bindings = state.bindings ∧
        Lists.tupleElements state.heap.size packed = .ok surplus packed ∧
        (surplus = [] → packed.heap[state.heap.size]? = some ⟨.tuple [] (some [.openTuple, .closeTuple]), false⟩) ∧
        prepareExpanded program available actual (.function address) state =
          .ok (.closure ⟨id, permitted, relay.site.declaration.body⟩)
            (activate packed relay.site.declaration record.captures assigned) := by
  have prepared := prepare_exact relay.site program available id permitted found record actual binding
  cases result with
  | error => exact prepared
  | ok bound =>
    obtain ⟨assigned, packed, packing, kept, bindings, agreed⟩ := prepared
    have varargs : relay.site.declaration.signature.varargs = some (fileSlot collector) := by
      change relay.varargs.map fileSlot = some (fileSlot collector)
      rw [positionalCollector]
      rfl
    change Packs relay.site.declaration.signature.varargs none state bound assigned packed at packing
    rw [varargs] at packing
    obtain ⟨sameAssigned, elements⟩ := packed_tuple packing
    have surplus := binding_positional_surplus binding
    refine ⟨packed, kept, bindings, surplus ▸ elements, ?_, sameAssigned ▸ agreed⟩
    intro empty
    exact packed_empty_key packing (surplus.trans empty)

/-- Defaults run in the reached defining frame. Installation records their
values and the original alias cell only after all default operands succeed. -/
theorem wrapper_defines {importName aliases globals}
    (relay : WrapperDeclaration importName aliases globals) (program : Program) (id : Nat)
    (found : program[id]? = some relay.site.declaration) {state : State} {aliasCell : Nat}
    {value : Option Lists.Value} {frozen : Bool}
    (owned : state.slots (fileSlot importName) = some (.owned aliasCell))
    (stored : state.heap[aliasCell]? = some ⟨.binding value, frozen⟩) :
    let target := globalSlot relay.name
    let capture : Capture := ⟨fileSlot importName, aliasCell, true⟩
    ∃ out, Lexical.DefinesFor (block aliases globals) target id relay.site.free
        relay.site.defaultKeys relay.site.defaultsInOrder state out ∧
      Exec program (List.range program.size) state (.define target id) out ∧
      denoteBody program (List.range program.size) (.define target id) state = out ∧
      match out with
      | .error _ stopped => Body.Keeps state.heap.size state stopped
      | .ok .next next =>
        ∃ evaluated values grown, Lexical.Evaluates (block aliases globals) state relay.site.defaultsInOrder
            (.ok values evaluated) ∧
          next = grown.write target (.function evaluated.heap.size) ∧
          Body.Keeps state.heap.size state grown ∧
          ∃ record : ClosureAt relay.site id state grown evaluated.heap.size,
            record.captures = [capture] ∧ record.defaults = values
      | .ok _ _ => False := by
  intro target capture
  have installed : Installs state relay.site.free [capture] := .cons (.enclosing owned) .nil
  have lexical := lexical_defaults relay.site relay.keywordLexical
  obtain ⟨keys, codes⟩ := default_layout relay.site relay.keywordLexical
  obtain ⟨out, ran, native, denoted, _⟩ := Lexical.defines_for_total program (List.range program.size)
    target id relay.site.declaration lexical found keys codes state [capture] installed
  refine ⟨out, ran, native, denoted, ?_⟩
  cases ran with
  | failed evaluated => exact Lexical.evaluates_keeps lexical evaluated
  | @installed evaluated values captures ran installedAt =>
    have kept := Lexical.evaluates_keeps lexical ran
    have same : captures = [capture] := Except.ok.inj
      ((installs_lookup evaluated installedAt).symm.trans
        (installs_lookup evaluated (installs_in_same_slots kept.1 installed)))
    subst captures
    let cell : Cell := ⟨.function ⟨id, [capture], relay.site.defaultKeys.zip values⟩, false⟩
    let grown := {evaluated with heap := evaluated.heap.push cell}
    have preserved : Body.Keeps state.heap.size state grown := by
      refine ⟨kept.1, fun index old below present => ?_⟩
      have reached : evaluated.heap[index]? = some old := kept.2 index old below present
      have bound := (Array.getElem?_eq_some_iff.mp reached).choose
      simp [grown, Array.getElem?_push, Nat.ne_of_lt bound, reached]
    let record : ClosureAt relay.site id state grown evaluated.heap.size :=
      ⟨[capture], values, false, Lexical.evaluated_length lexical ran, Array.getElem?_push_size, installed, by
        intro selected member
        simp only [List.mem_singleton] at member
        subst selected
        exact ⟨value, frozen, preserved.2 _ _ (Array.getElem?_eq_some_iff.mp stored).choose stored⟩⟩
    exact ⟨evaluated, values, grown, ran, rfl, preserved, record, rfl, rfl⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

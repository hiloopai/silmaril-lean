module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Mapping
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Binder
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Execution

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Assignment (LexicalBlock)
open Recursive (Site)
open Recursive.Call (ClosureAt)
open Functions
open Functions.Lowering.Resolve (resolveTracked)
open Lists (State Outcome)
open Lists.Iteration (Flow finishState)

local notation "Value" => Lists.Value
local notation "Error" => Lists.Error
local notation "Positional" =>
  Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Arguments
local notation "NamedArgs" => Arguments

theorem binds_total (positional named : List Parameter) (varargs kwargs : Option Binding)
    (saved : Bindings) (actual : Actual) : ∃ result, Binds positional named varargs kwargs saved actual result :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.binds_total
    positional named varargs kwargs saved actual

/-- Independent binding agrees with the native binder including both collectors. -/
theorem binding_exact (signature : Signature)
    {saved : Bindings} {actual : Actual} {result : Except Error BoundArguments}
    (source : Binds signature.positional signature.named signature.varargs signature.kwargs saved actual result) :
    bindArguments signature saved actual = result :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.binding_exact
    signature source

/-- Successful binding packs the declared collectors while retaining the reached caller and cells. -/
theorem packs_total (signature : Signature)
    (caller : State) (bound : BoundArguments) :
    ∃ assigned packed, Packs signature.varargs signature.kwargs caller bound assigned packed ∧
      Body.Keeps caller.heap.size caller packed ∧ packed.bindings = caller.bindings ∧
      packArgs signature bound caller = .ok assigned packed :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.packs_total
    signature caller bound

/-- Preparation uses the reached record, performs the ordinary binder and
packs its result before activation. Binding failure leaves the operand state intact. -/
theorem prepare_exact {parent : LexicalBlock} {formals : List PlainKeywordParameter}
    {varargs kwargs : Option String} {scope : Scope} (site : Site parent formals varargs kwargs scope)
    (program : Program) (available : List DeclarationId) (id : DeclarationId) (permitted : id ∈ available)
    (found : program[id]? = some site.declaration)
    {defining state : State} {address : Nat} (record : ClosureAt site id defining state address)
    (actual : Actual) {result : Except Error BoundArguments} (binding : SiteBinding site record.defaults actual result) :
    match result with
    | .error error => prepareExpanded program available actual (.function address) state = .error error state
    | .ok bound =>
      ∃ assigned packed, Packs site.declaration.signature.varargs site.declaration.signature.kwargs state bound assigned packed ∧
        Body.Keeps state.heap.size state packed ∧ packed.bindings = state.bindings ∧
        prepareExpanded program available actual (.function address) state =
          .ok (.closure ⟨id, permitted, site.declaration.body⟩)
            (activate packed site.declaration record.captures assigned) := by
  have agreement := Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.prepare_exact
    site program available id permitted found record actual binding
  cases result <;> exact agreement

/-- The tuple payload starts after the ordinary positional parameters. -/
theorem binding_positional_surplus {positional named : List Parameter} {varargs kwargs : Option Binding}
    {saved : Bindings} {actual : Actual} {assigned : BoundArguments}
    (binding : Binds positional named varargs kwargs saved actual (.ok assigned)) :
    assigned.surplusPositional = actual.positional.drop positional.length := by
  cases binding
  rfl

/-- The collector gets the exact ordered surplus at a fresh tuple address. -/
theorem packed_tuple {slot : Binding} {caller packed : State} {bound : BoundArguments} {assigned : Bindings}
    (packing : Packs (some slot) none caller bound assigned packed) :
    assigned = (slot, .tuple caller.heap.size) :: bound.named ∧
      Lists.tupleElements caller.heap.size packed = .ok bound.surplusPositional packed :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.packed_tuple
    packing

/-- The empty collector tuple uses the ordinary canonical empty tuple key. -/
theorem packed_empty_key {slot : Binding} {caller packed : State} {bound : BoundArguments} {assigned : Bindings}
    (packing : Packs (some slot) none caller bound assigned packed) (empty : bound.surplusPositional = []) :
    packed.heap[caller.heap.size]? = some ⟨.tuple [] (some [.openTuple, .closeTuple]), false⟩ :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.packed_empty_key
    packing empty

/-- Collection preserves exactly the unmatched explicit names and their original values in encounter order. -/
theorem binding_surplus {positional named : List Parameter} {varargs kwargs : Option Binding} {saved : Bindings}
    {actual : Actual} {bound : BoundArguments}
    (source : Binds positional named varargs kwargs saved actual (.ok bound)) :
    bound.surplusKeywords =
      actual.keywords.filter (fun (name, _) => (named.find? (fun formal => formal.slot.name == name)).isNone) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.binding_surplus
    source

/-- The terminal collector receives a fresh unfrozen dictionary even for an empty surplus. -/
theorem packed_dictionary {varargs : Option Binding} {slot : Binding} {caller packed : State}
    {bound : BoundArguments} {assigned : Bindings} (packing : Packs varargs (some slot) caller bound assigned packed) :
    assigned.head? = some (slot, .dict (caller.heap.size + varargs.isSome.toNat)) ∧
      packed.heap[caller.heap.size + varargs.isSome.toNat]? =
        some ⟨.dict (keywordEntries bound.surplusKeywords), false⟩ :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.packed_dictionary
    packing

/-- When both slots are present, the tuple occupies the first fresh address and the dictionary the next. -/
theorem packed_both {positional keyword : Binding} {caller packed : State} {bound : BoundArguments}
    {assigned : Bindings} (packing : Packs (some positional) (some keyword) caller bound assigned packed) :
    assigned = (keyword, .dict (caller.heap.size + 1)) :: (positional, .tuple caller.heap.size) :: bound.named ∧
      Lists.tupleElements caller.heap.size packed = .ok bound.surplusPositional packed ∧
      packed.heap[caller.heap.size + 1]? = some ⟨.dict (keywordEntries bound.surplusKeywords), false⟩ :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.packed_both
    packing

theorem argument_origins {block : LexicalBlock}
    {source : List (String × Lowering.Resolve.SourceExpr)} {codes : List (String × Lowering.Expr)} {reads : List Binding}
    (related : NamedArgs block source codes reads) :
    ∀ binding ∈ reads, ∃ origin, Silmaril.Languages.Starlark.Modules.Resolve.Capture.ReadOrigin block binding origin :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.argument_origins
    related

/-- A mapping transfers each original value under its string key in insertion order. -/
theorem keyword_entries_exact {entries : List Lists.Entry} {result : Except Error Keywords}
    (source : KeywordEntries entries result) :
    (entries.mapM fun entry => match entry.key with
      | .string name => .ok (name, entry.value)
      | key => .error (.keywordMustBeString key)) = result :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.keyword_entries_exact
    source

/-- Normalized resolution keeps the callee, positional reads and named reads in their source order. -/
theorem resolves_at {block : LexicalBlock} {name : String}
    {positional : List Lowering.Resolve.SourceExpr} {posCodes : List Lowering.Expr} {posReads : List Binding}
    (slot : Binding) (callee : Body.Operand block (.scalar (.read name)) (Leaf.readOperand slot) [slot])
    (related : Positional block positional posCodes posReads) (keywords : Operands block)
    (star : Option (Spread block) := none) (mapping : Option (Mapping block) := none) :
    resolveTracked block.context
      (.call (.scalar (.read name)) positional keywords.source (star.map Spread.source) (mapping.map Mapping.source)) =
      .ok (expressionAt slot posCodes keywords.codes (star.map Spread.code) (mapping.map Mapping.code),
        slot :: ((posReads ++ keywords.reads) ++ spreadReads star ++ mappingReads mapping)) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.resolves_at
    slot callee related keywords star mapping

theorem resolves {block : LexicalBlock} {name : String}
    {positional : List Lowering.Resolve.SourceExpr} {posCodes : List Lowering.Expr} {posReads : List Binding}
    (legal : name.toList.head? ≠ some '$') (owned : name ∈ block.owned)
    (related : Positional block positional posCodes posReads) (keywords : Operands block)
    (star : Option (Spread block) := none) (mapping : Option (Mapping block) := none) :
    resolveTracked block.context
      (.call (.scalar (.read name)) positional keywords.source (star.map Spread.source) (mapping.map Mapping.source)) =
      .ok (expression name posCodes keywords.codes (star.map Spread.code) (mapping.map Mapping.code),
        fileSlot name :: ((posReads ++ keywords.reads) ++ spreadReads star ++ mappingReads mapping)) :=
  resolves_at (fileSlot name) (.read legal (.owned owned) (.owned owned)) related keywords star mapping

theorem spread_origins {block : LexicalBlock} (star : Option (Spread block)) :
    ∀ binding ∈ spreadReads star, ∃ origin, Silmaril.Languages.Starlark.Modules.Resolve.Capture.ReadOrigin block binding origin :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.spread_origins
    star

theorem mapping_origins {block : LexicalBlock} (mapping : Option (Mapping block)) :
    ∀ binding ∈ mappingReads mapping, ∃ origin, Silmaril.Languages.Starlark.Modules.Resolve.Capture.ReadOrigin block binding origin :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.mapping_origins
    mapping

/-- The accepted operand profile emits distinct explicit keyword names. -/
theorem distinct_names {block : LexicalBlock} (keywords : Operands block) :
    firstDuplicate (keywords.codes.map Prod.fst) = none :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.distinct_names
    keywords

/-- Repeated explicit names are rejected during validation, before the call can run. -/
theorem rejects_duplicate (name : String) (positional : List Lowering.Expr)
    (keywords : List (String × Lowering.Expr)) (duplicate : String)
    (repeated : firstDuplicate (keywords.map Prod.fst) = some duplicate) :
    (expression name positional keywords).validateCalls = .error (.duplicateExplicitKeyword duplicate) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.rejects_duplicate
    name positional keywords duplicate repeated

/-- The reached closure uses its saved defaults and live captures under the same declaration guard. -/
theorem runs_at_reached {parent block : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent formals varargs kwargs scope)
    (bodyRuns : State → Outcome Flow → Prop)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : DeclarationId)
    (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    {name : String} (slot : Binding) {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand slot)
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    (enterReached : ∀ packed, Body.Keeps state.heap.size state packed →
      ∀ assigned : List (Binding × Lists.Value),
      let active := activate packed site.declaration record.captures assigned
      ∃ out, bodyRuns active out ∧ Exec resolved.program (withoutDeclaration available id) active site.body.code out ∧
        Body.Keeps packed.heap.size packed (finishState (Leaf.returnTo packed out)))
    {arguments : List Lowering.Resolve.SourceExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Positional block arguments codes reads) (keywords : Operands block) (star : Option (Spread block) := none) (mapping : Option (Mapping block) := none) :
    ∃ out, RunsAt site bodyRuns block id name slot arguments codes keywords.source keywords.codes star mapping state out ∧
      ExecExpr resolved.program available state (expressionAt slot codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code)) out ∧
      Lowering.denoteExpr resolved.program available (expressionAt slot codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code)) state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.runs_at_reached
    site bodyRuns checked id found available permitted slot callee record enterReached related keywords star mapping

theorem runs_at {parent block : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent formals varargs kwargs scope)
    (bodyRuns : State → Outcome Flow → Prop)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : DeclarationId)
    (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    (enterBody : BodyEntry site resolved.program available id bodyRuns)
    {name : String} (slot : Binding) {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand slot)
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    {arguments : List Lowering.Resolve.SourceExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Positional block arguments codes reads) (keywords : Operands block) (star : Option (Spread block) := none) (mapping : Option (Mapping block) := none) :
    ∃ out, RunsAt site bodyRuns block id name slot arguments codes keywords.source keywords.codes star mapping state out ∧
      ExecExpr resolved.program available state (expressionAt slot codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code)) out ∧
      Lowering.denoteExpr resolved.program available (expressionAt slot codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code)) state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.runs_at
    site bodyRuns checked id found available permitted enterBody slot callee record related keywords star mapping

theorem runs {parent block : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent formals varargs kwargs)
    (bodyRuns : State → Outcome Flow → Prop)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : DeclarationId)
    (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    (enterBody : BodyEntry site resolved.program available id bodyRuns)
    {name : String} {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    {arguments : List Lowering.Resolve.SourceExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Positional block arguments codes reads) (keywords : Operands block) (star : Option (Spread block) := none) (mapping : Option (Mapping block) := none) :
    ∃ out, RunsWith site bodyRuns block id name arguments codes keywords.source keywords.codes star mapping state out ∧
      ExecExpr resolved.program available state (expression name codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code)) out ∧
      Lowering.denoteExpr resolved.program available (expression name codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code)) state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  runs_at site bodyRuns checked id found available permitted enterBody (fileSlot name) callee record related keywords star mapping

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Assignment (LexicalBlock)
open Defaults
open Defaults.Nested.Sequence.Recursive (Site parameterNames)
open Defaults.Nested.Sequence.Recursive.Call (Arguments)
open Defaults.Nested.Sequence.Recursive.Call.Named
  (Mapping Operands RunsAt Spread expressionAt spreadReads mappingReads)
open Lists.Iteration (Flow)
open Functions (Declaration Program)
open Lists (State Outcome)

/-- A consumer definition with no parameters or locals returns a call
through its captured load alias. The operands use the checked call grammar. -/
structure Wrapper where
  label : String
  imported : String
  alias : String
  name : String
  destination : String
  publicImport : Modules.isPublic imported = true
  legalAlias : alias.toList.head? ≠ some '$'
  legalName : name.toList.head? ≠ some '$'
  separate : name ≠ alias
  arguments : List Functions.Lowering.Resolve.SourceExpr
  codes : List Functions.Lowering.Expr
  reads : List Binding
  operands : Arguments ⟨[], [alias], [name, destination]⟩ arguments codes reads
  keywords : Operands ⟨[], [alias], [name, destination]⟩
  star : Option (Spread ⟨[], [alias], [name, destination]⟩) := none
  mapping : Option (Mapping ⟨[], [alias], [name, destination]⟩) := none
  selects : Selects ⟨[], [alias], [name, destination]⟩
    (fileSlot alias :: (reads ++ keywords.reads ++ spreadReads star ++
      mappingReads mapping)) [⟨fileSlot alias, fileSlot alias⟩]

@[expose] def Wrapper.parent (wrapper : Wrapper) : LexicalBlock :=
  block [wrapper.alias] [wrapper.name, wrapper.destination]

@[expose] def Wrapper.declaration (wrapper : Wrapper) :
    WrapperDeclaration wrapper.alias [wrapper.alias] [wrapper.name, wrapper.destination] where
  name := wrapper.name
  target := by simp
  visible := by simp
  legalAlias := wrapper.legalAlias
  parameters := ⟨[], []⟩
  keywordOnly := []
  varargs := none
  arguments := wrapper.arguments
  codes := wrapper.codes
  reads := wrapper.reads
  operands := wrapper.operands
  keywords := wrapper.keywords
  star := wrapper.star
  mapping := wrapper.mapping
  selects := wrapper.selects

@[expose] def Wrapper.expression (wrapper : Wrapper) : Functions.Lowering.Resolve.SourceExpr := wrapper.declaration.expression

@[expose] def Wrapper.code (wrapper : Wrapper) : Functions.Lowering.Expr := wrapper.declaration.code

@[expose] def Wrapper.site (wrapper : Wrapper) : Site wrapper.parent [] none none .global := wrapper.declaration.site

@[expose] def Wrapper.invoke (wrapper : Wrapper) : Functions.Lowering.Resolve.SourceExpr :=
  .call (.scalar (.read wrapper.name)) [] [] none none

@[expose] def Wrapper.invokeCode (wrapper : Wrapper) : Functions.Lowering.Expr :=
  expressionAt (globalSlot wrapper.name) [] [] none none

@[expose] def Wrapper.commands (wrapper : Wrapper) : List Command :=
  [.load wrapper.label [⟨wrapper.imported, wrapper.alias⟩],
   .define wrapper.name wrapper.site.sourceSignature wrapper.site.source,
   .assign wrapper.destination wrapper.invoke]

@[expose] def Wrapper.moduleCode (wrapper : Wrapper) (producer : Program) : List Modules.Command :=
  [.load wrapper.label [⟨wrapper.imported, wrapper.alias⟩],
   .exec (.define wrapper.name producer.size),
   .exec (.assignExpr wrapper.destination wrapper.invokeCode)]

@[expose] def Wrapper.graph (wrapper : Wrapper) (producer consumer : ResolvedModule) : Loader.Manifest :=
  #[⟨producer.source, []⟩, ⟨consumer.source, [(wrapper.label, 0)]⟩]

abbrev Wrapper.Returns (wrapper : Wrapper) (callee : Callable) :=
  wrapper.declaration.Returns callee

/-- The checked suffix installs the definition, then calls it and writes
the answer only on success. -/
inductive Wrapper.Runs (wrapper : Wrapper) (id : Nat) (callee : Callable) (state : State) :
    Modules.Result Unit → Prop where
  | invoked {installed : State} {out : Outcome Lists.Value} :
      Lexical.DefinesFor wrapper.parent (globalSlot wrapper.name) id wrapper.site.free [] [] state
        (.ok .next installed) →
      RunsAt wrapper.site (wrapper.Returns callee) wrapper.parent id wrapper.name (globalSlot wrapper.name)
        [] [] [] [] none none installed out →
      wrapper.Runs id callee state (afterWrite wrapper.destination out)

/-- The source rules consume the actual dependency publication. Its
export gives the address written to the local import slot. -/
inductive Wrapper.Loads (wrapper : Wrapper) (producer consumer : ResolvedModule)
    (commands : List Command) (exports : Environment) (caller : Loader.Session) :
    Loader.Result Modules.Published → Prop where
  | dependencyError {error : Loader.Error} {reached : Loader.Session} :
      Producer commands producer.source {caller with runtime := Modules.enter consumer.source caller.runtime}
        (.error error reached) →
      wrapper.Loads producer consumer commands exports caller
        (.error error {reached with runtime := Modules.restoreThread caller.runtime reached.runtime})
  | missing {published : Modules.Published} {reached : Loader.Session} :
      Producer commands producer.source {caller with runtime := Modules.enter consumer.source caller.runtime}
        (.ok published reached) →
      published.exports.lookup wrapper.imported = none →
      wrapper.Loads producer consumer commands exports caller
        (observed 1 consumer.source caller.runtime reached.cache
          (.error (.missingExport wrapper.label wrapper.imported) reached.runtime))
  | invoked {published : Modules.Published} {reached : Loader.Session} {address : Nat}
      {callee : Callable} {out : Modules.Result Unit} :
      Producer commands producer.source {caller with runtime := Modules.enter consumer.source caller.runtime}
        (.ok published reached) →
      published.exports.lookup wrapper.imported = some (.function address) →
      exports wrapper.imported = some callee →
      wrapper.Runs producer.program.size callee
        (reached.runtime.write (fileSlot wrapper.alias) (.function address)) out →
      wrapper.Loads producer consumer commands exports caller
        (observed 1 consumer.source caller.runtime reached.cache out)

abbrev Wrapper.Agrees (wrapper : Wrapper) (producer consumer : ResolvedModule)
    (commands : List Command) (exports : Environment) (caller : Loader.Session) : Prop :=
  ∃ out, wrapper.Loads producer consumer commands exports caller out ∧
    Loader.Runs consumer.program (wrapper.graph producer consumer) [] (.initialize 1) caller out ∧
    Loader.load consumer.program (wrapper.graph producer consumer) 1 caller = out

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs
public import Silmaril.Languages.Starlark.Modules.Loader.Operational.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Assignment (LexicalBlock)
open Defaults
open Defaults.Nested.Sequence (PreservesDeclarations)
open Defaults.Nested.Sequence.Recursive (Site KeywordLexical parameterNames)
open Defaults.Nested.Sequence.Recursive.Call (Arguments ClosureAt)
open Lists.Iteration (Flow)
open Defaults.Nested.Sequence.Recursive.Call.Named (Mapping Operands RunsAt Spread expressionAt spreadReads mappingReads)
open Functions
open Lists (State Outcome)
open Loader (Manifest Session)

local notation "Expr" => Lowering.Resolve.SourceExpr

@[expose] def block (aliases : List String) (globals : List String) : LexicalBlock :=
  ⟨aliases, [], globals⟩

/-- Loads bind file-local names. Ordinary module assignments write globals. -/
@[expose] def readSlot (aliases : List String) (name : String) : Binding :=
  if name ∈ aliases then fileSlot name else globalSlot name

structure Invocation (aliases : List String) (globals : List String) where
  callee : String
  declared : callee ∈ aliases ∨ callee ∈ globals
  legal : callee.toList.head? ≠ some '$'
  destination : String
  destinationGlobal : destination ∈ globals
  arguments : List Expr
  codes : List Lowering.Expr
  reads : List Binding
  operands : Arguments (block aliases globals) arguments codes reads
  keywords : Operands (block aliases globals)
  star : Option (Spread (block aliases globals)) := none
  mapping : Option (Mapping (block aliases globals)) := none

@[expose] def Invocation.source {aliases globals} (call : Invocation aliases globals) : Expr :=
  .call (.scalar (.read call.callee)) call.arguments call.keywords.source
    (call.star.map Spread.source) (call.mapping.map Mapping.source)

@[expose] def Invocation.code {aliases globals} (call : Invocation aliases globals) : Lowering.Expr :=
  expressionAt (readSlot aliases call.callee) call.codes call.keywords.codes
    (call.star.map Spread.code) (call.mapping.map Mapping.code)

/-- The wrapper owns its parameter slots, with no body
locals, and resolves the imported callee in the enclosing alias block. -/
@[expose] def wrapperBlock (parameters : Parameters) (keywordOnly : List PlainKeywordParameter)
    (varargs : Option String) (aliases globals : List String) : LexicalBlock :=
  ⟨parameterNames parameters keywordOnly varargs none ++ [], aliases ++ [], globals⟩

/-- An importer declaration returns a checked call through the immutable
file-local import. Its only capture is that binding's address. -/
structure WrapperDeclaration (alias : String) (aliases globals : List String) where
  name : String
  target : name ∈ globals
  visible : alias ∈ aliases
  legalAlias : alias.toList.head? ≠ some '$'
  parameters : Parameters := ⟨[], []⟩
  keywordOnly : List PlainKeywordParameter := []
  varargs : Option String := none
  unshadowed : alias ∉ parameterNames parameters keywordOnly varargs none := by
    simp [Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.parameterNames, Parameters.names]
  defaults : List PlainPositionalDefault := []
  lexical : Lexical.Elaborates (block aliases globals) parameters.optional defaults := by exact .nil
  keywordLexical : KeywordLexical (block aliases globals) keywordOnly := by exact .nil
  arguments : List Expr
  codes : List Lowering.Expr
  reads : List Binding
  operands : Arguments (wrapperBlock parameters keywordOnly varargs aliases globals) arguments codes reads
  keywords : Operands (wrapperBlock parameters keywordOnly varargs aliases globals)
  star : Option (Spread (wrapperBlock parameters keywordOnly varargs aliases globals)) := none
  mapping : Option (Mapping (wrapperBlock parameters keywordOnly varargs aliases globals)) := none
  selects : Selects (wrapperBlock parameters keywordOnly varargs aliases globals)
    (fileSlot alias :: (reads ++ keywords.reads ++ spreadReads star ++ mappingReads mapping))
    [⟨fileSlot alias, fileSlot alias⟩]

@[expose] def WrapperDeclaration.expression {alias aliases globals} (relay : WrapperDeclaration alias aliases globals) : Expr :=
  .call (.scalar (.read alias)) relay.arguments relay.keywords.source
    (relay.star.map Spread.source) (relay.mapping.map Mapping.source)

@[expose] def WrapperDeclaration.code {alias aliases globals} (relay : WrapperDeclaration alias aliases globals) : Lowering.Expr :=
  expressionAt (fileSlot alias) relay.codes relay.keywords.codes (relay.star.map Spread.code) (relay.mapping.map Mapping.code)

@[expose] def WrapperDeclaration.site {alias aliases globals} (relay : WrapperDeclaration alias aliases globals) : Site (block aliases globals) relay.keywordOnly relay.varargs none .global where
  name := relay.name
  target := relay.target
  parameters := relay.parameters
  source := .ret (some relay.expression)
  binders := []
  locals := []
  collects := .ret _
  localOrder := .nil
  body := ⟨.returnExpr relay.code, fileSlot alias ::
    (relay.reads ++ relay.keywords.reads ++ spreadReads relay.star ++ mappingReads relay.mapping)⟩
  free := [⟨fileSlot alias, fileSlot alias⟩]
  selects := relay.selects
  defaults := relay.defaults
  lexical := relay.lexical

/-- An independent return rule for a call through the captured import. -/
@[expose] def WrapperDeclaration.Returns {alias aliases globals} (relay : WrapperDeclaration alias aliases globals) (callee : Callable)
    (active : State) (out : Outcome Flow) : Prop :=
  ∃ result, RunsAt callee.site callee.BodyRuns relay.site.block callee.id alias (fileSlot alias)
      relay.arguments relay.codes relay.keywords.source relay.keywords.codes relay.star relay.mapping active result ∧
    out = result.resume (fun value => pure (.returned value))

/-- A wrapper records the source shape of the imported callable that it
will invoke. Runtime provenance separately follows the actual capture cell. -/
inductive Callee where
  | regular (callee : Callable)
  | wrapper {alias : String} {aliases globals : List String}
      (declaration : WrapperDeclaration alias aliases globals) (id : DeclarationId) (imported : Callee)

@[expose] def Callee.layout : Callee → Callable
  | .regular callee => callee
  | .wrapper (aliases := aliases) (globals := globals) declaration id _ =>
    ⟨block aliases globals, .global, declaration.keywordOnly, declaration.varargs, none, declaration.site, id, none⟩

@[expose] def Callee.BodyRuns : Callee → State → Outcome Flow → Prop
  | .regular callee => callee.BodyRuns
  | .wrapper (alias := alias) declaration _ imported => fun active out =>
    ∃ result, RunsAt imported.layout.site imported.BodyRuns declaration.site.block imported.layout.id alias (fileSlot alias)
      declaration.arguments declaration.codes declaration.keywords.source declaration.keywords.codes
      declaration.star declaration.mapping active result ∧
      out = result.resume (fun value => pure (.returned value))

@[expose] def Callee.returned : Callee → Option Callable
  | .regular callee => callee.returned.map Callable.nested
  | .wrapper _ _ imported => imported.returned

abbrev Tracked := String → Option Callee

@[expose] def track (env : Tracked) (name : String) (entry : Option Callee) : Tracked :=
  fun read => if read = name then entry else env read

/-- A live wrapper's own closure points to its original load cell. The
value stored there has recursive provenance at a strictly earlier index. -/
inductive Callee.At (origin final : Program) (state : State) : Callee → Nat → Prop where
  | regular {callee : Callable} {defining : State} {address : Nat} :
      callee.Linked origin → ClosureAt callee.site callee.id defining state address →
      At origin final state (.regular callee) address
  | wrapper {alias : String} {aliases globals : List String} {declaration : WrapperDeclaration alias aliases globals}
      {id : Nat} {imported : Callee} {defining : State} {address cell target : Nat} {frozen : Bool} :
      final[id]? = some declaration.site.declaration →
      imported.layout.id < id →
      (record : ClosureAt declaration.site id defining state address) →
      record.captures = [⟨fileSlot alias, cell, true⟩] →
      state.heap[cell]? = some ⟨.binding (some (.function target)), frozen⟩ →
      At origin final state imported target →
      At origin final state (.wrapper declaration id imported) address

/-- A checked name copy propagates the original callable. Other assignments
forget the destination's previous provenance. -/
inductive Copy (aliases : List String) : Expr → Lowering.Expr → Type where
  | forget {source code} : Copy aliases source code
  | name (name : String) : Copy aliases (.scalar (.read name)) (Leaf.readOperand (readSlot aliases name))

@[expose] def Copy.track {aliases source code} (copy : Copy aliases source code) (env : Tracked) : Option (Callee) :=
  match copy with
  | .forget => none
  | .name read => env read

inductive Step (aliases globals : List String) where
  | assign (destination : String) (declared : destination ∈ globals) {source : Expr}
      {code : Lowering.Expr} {reads : List Binding} :
      Body.Operand (block aliases globals) source code reads → Copy aliases source code → Step aliases globals
  | invoke (call : Invocation aliases globals)
  | define {alias : String} (declaration : WrapperDeclaration alias aliases globals)

@[expose] def Step.destination {aliases globals} : Step aliases globals → String
  | .assign name .. => name
  | .invoke call => call.destination
  | .define declaration => declaration.name

@[expose] def Step.source {aliases globals} : Step aliases globals → Command
  | .assign name _ (source := source) _ _ => .assign name source
  | .invoke call => .assign call.destination call.source
  | .define declaration => .define declaration.name declaration.site.sourceSignature declaration.site.source

@[expose] def Step.code {aliases globals} (program : Program) : Step aliases globals → Modules.Command
  | .assign name _ (code := code) _ _ => .exec (.assignExpr name code)
  | .invoke call => .exec (.assignExpr call.destination call.code)
  | .define declaration => .exec (.define declaration.name program.size)

@[expose] def Step.emit {aliases globals} (program : Program) : Step aliases globals → Program
  | .define declaration => program.push declaration.site.declaration
  | _ => program

@[expose] def Step.advance {aliases globals} (program : Program) (env : Tracked) :
    Step aliases globals → Tracked
  | .assign destination _ _ copy => track env destination (copy.track env)
  | .invoke call =>
    track env call.destination ((env call.callee).bind (fun callee => callee.returned.map Callee.regular))
  | .define (alias := alias) declaration =>
    track env declaration.name ((env alias).map (Callee.wrapper declaration program.size))

@[expose] def compileSuite {aliases globals} (program : Program) :
    List (Step aliases globals) → List Modules.Command × Program
  | [] => ([], program)
  | head :: tail =>
    let compiled := compileSuite (head.emit program) tail
    (head.code program :: compiled.1, compiled.2)

@[expose] def trackSuite {aliases globals} (program : Program) (env : Tracked) :
    List (Step aliases globals) → Tracked
  | [] => env
  | head :: tail => trackSuite (head.emit program) (head.advance program env) tail

/-- Source-order provenance enables each call and describes the destination
after its successful return. Declaration IDs follow the current table. -/
@[expose] def ReadyFor {aliases : List String} {globals : List String} (program : Program)
    (env : Tracked) : List (Step aliases globals) → Prop
  | [] => True
  | first :: rest =>
    let tail := ReadyFor (first.emit program) (first.advance program env) rest
    match first with
    | .invoke call => ∃ callee, env call.callee = some callee ∧ tail
    | .define (alias := alias) _ => ∃ callee, env alias = some callee ∧ callee.layout.id < program.size ∧ tail
    | .assign .. => tail

/-- A requested public symbol and its file-local alias. -/
structure ImportBinding where
  name : String
  alias : String
  publicName : Modules.isPublic name = true

@[expose] def ImportBinding.item (binding : ImportBinding) : Modules.Import :=
  ⟨binding.name, binding.alias⟩

/-- A single load command. Bindings are stored in source order. -/
structure ImportSite where
  label : String
  bindings : List ImportBinding
  nonempty : bindings ≠ []

@[expose] def ImportSite.single (label name alias : String) (publicName : Modules.isPublic name = true) :
    ImportSite :=
  ⟨label, [⟨name, alias, publicName⟩], by simp⟩

@[expose] def ImportSite.aliases (site : ImportSite) : List String :=
  site.bindings.map ImportBinding.alias

@[expose] def ImportSite.source (site : ImportSite) : Command :=
  .load site.label (site.bindings.map ImportBinding.item)

@[expose] def ImportSite.code (site : ImportSite) : Modules.Command :=
  .load site.label (site.bindings.map ImportBinding.item)

/-- All load aliases are in lexical scope throughout the normalized suite. -/
structure OrderedConsumer where
  imports : List ImportSite
  globals : List String
  body : List (Step (imports.flatMap ImportSite.aliases) globals)
  declared : body.map Step.destination = globals

@[expose] def OrderedConsumer.aliases (plan : OrderedConsumer) : List String :=
  plan.imports.flatMap ImportSite.aliases

@[expose] def OrderedConsumer.commands (plan : OrderedConsumer) : List Command :=
  plan.imports.map ImportSite.source ++ plan.body.map Step.source

@[expose] def OrderedConsumer.code (plan : OrderedConsumer) (program : Program) : List Modules.Command :=
  plan.imports.map ImportSite.code ++ (compileSuite program plan.body).1

/-- The consumer declares one renamed public import and a finite suite.
The globals are collected from the suite's definition and assignment targets. -/
structure Consumer where
  label : String
  name : String
  alias : String
  publicName : Modules.isPublic name = true
  globals : List String
  body : List (Step [alias] globals)
  declared : body.map Step.destination = globals
  separate : alias ∉ globals

@[expose] def Consumer.item (plan : Consumer) : Modules.Import :=
  ⟨plan.name, plan.alias⟩

@[expose] def Consumer.commands (plan : Consumer) : List Command :=
  .load plan.label [plan.item] :: plan.body.map Step.source

@[expose] def Consumer.code (plan : Consumer) (program : Program) : List Modules.Command :=
  .load plan.label [plan.item] :: (compileSuite program plan.body).1

@[expose] def initial (alias : String) (callee : Callee) : Tracked :=
  track (fun _ => none) alias (some callee)

/-- Producer zero has no dependencies. Consumer one has just the one
requester-relative label. Both use the final linked table. -/
@[expose] def graph (producer consumer : ResolvedModule) (plan : Consumer) : Manifest :=
  #[⟨producer.source, []⟩, ⟨consumer.source, [(plan.label, 0)]⟩]

/-- The source profile tracks either a producer export or a name outside the
producer's declared globals. The consumer supplies no declaration or address. -/
@[expose] def Covered (exports : Environment) (producer : List Command) (plan : Consumer) (program : Program) : Prop :=
  (∃ callee, exports plan.name = some callee ∧ ReadyFor program (initial plan.alias (.regular callee)) plan.body) ∨
    plan.name ∉ Trace.names producer

@[expose] def reachedSession {α : Type} : Loader.Result α → Session
  | .ok _ s | .error _ s => s

/-- Use module publication, with the loader's error attribution and success
cache. This observation is shared by the independent source rules. -/
@[expose] def observed (id : Loader.ModuleId) (source : Modules.Source) (caller : State)
    (cache : List (Loader.ModuleId × Modules.Published)) (out : Modules.Result Unit) :
    Loader.Result Modules.Published :=
  match Modules.finish source caller out with
  | .error error final => .error (.initialization id error) ⟨final, cache⟩
  | .ok published final => .ok published ⟨final, (id, published) :: cache⟩

/-- A cache hit reuses the published value and the exact runtime heap. -/
inductive Producer (commands : List Command) (source : Modules.Source) :
    Session → Loader.Result Modules.Published → Prop where
  | cold {state : Session} {out : Modules.Result Unit} :
      state.cache.lookup 0 = none →
      ExecutesAll (Trace.names commands) (Modules.enter source state.runtime) commands out →
      Producer commands source state (observed 0 source state.runtime state.cache out)
  | cached {state : Session} {published : Modules.Published} :
      state.cache.lookup 0 = some published →
      Producer commands source state (.ok published state)

/-- Look up the requested name before any caller operand runs. -/
inductive BindsAlias (plan : Consumer) (published : Modules.Published) (state : State) :
    Modules.Result Unit → Prop where
  | missing : published.exports.lookup plan.name = none →
      BindsAlias plan published state (.error (.missingExport plan.label plan.name) state)
  | found {value : Lists.Value} : published.exports.lookup plan.name = some value →
      BindsAlias plan published state (.ok () (state.write (fileSlot plan.alias) value))

/-- The reached importer owns its import and declared globals in one frame. -/
@[expose] def Frame (aliases globals : List String) (state : State) : Prop :=
  RootCall.DistinctOwned state ∧
    ∀ binding ∈ aliases.map fileSlot ++ globals.map globalSlot,
      ∃ address value frozen, state.slots binding = some (.owned address) ∧
        state.heap[address]? = some ⟨.binding value, frozen⟩

/-- Importer writes use the cells allocated by the current module entry. -/
@[expose] def FreshSlots (floor : Nat) (state : State) : Prop :=
  ∀ binding address, state.slots binding = some (.owned address) → floor ≤ address

/-- Initialization can fill a blank slot. Previously initialized binding
contents and stored functions retain their identities. -/
structure KeepsClosureCells (before after : State) : Prop where
  functions : ∀ (address : Nat) closure flag, before.heap[address]? = some ⟨.function closure, flag⟩ →
    ∃ next, after.heap[address]? = some ⟨.function closure, next⟩
  bindings : ∀ (address : Nat) value flag, before.heap[address]? = some ⟨.binding value, flag⟩ →
    ∃ next frozen, after.heap[address]? = some ⟨.binding next, frozen⟩ ∧ (value ≠ none → next = value)

@[expose] def Blank (state : State) (binding : Binding) : Prop :=
  ∃ address frozen, state.slots binding = some (.owned address) ∧
    state.heap[address]? = some ⟨.binding none, frozen⟩

/-- A tracked slot contains the actual function value and its recursive
provenance, even if its defining module frame is inactive. -/
@[expose] def Live (aliases : List String) (producer final : Program) (env : Tracked) (state : State) : Prop :=
  ∀ name callee, env name = some callee →
    ∃ (slot address : Nat) (frozen : Bool),
      state.slots (readSlot aliases name) = some (.owned slot) ∧
      state.heap[slot]? = some ⟨.binding (some (.function address)), frozen⟩ ∧ callee.At producer final state address

/-- Each importer statement uses the independent operand, definition and call rules. -/
inductive Executes {aliases globals : List String}
    (program : Program) (state : State) : Step aliases globals → Modules.Result Unit → Prop where
  | assign {name declared source code reads} {operand : Body.Operand (block aliases globals) source code reads}
      {copy : Copy aliases source code} {out : Outcome Lists.Value} :
      Body.Evaluates (block aliases globals) state source code out →
      Executes program state (.assign name declared operand copy) (afterWrite name out)
  | define {alias : String} {declaration : WrapperDeclaration alias aliases globals} {out : Outcome Flow} :
      Lexical.DefinesFor (block aliases globals) (globalSlot declaration.name) program.size declaration.site.free
        declaration.site.defaultKeys declaration.site.defaultsInOrder state out →
      Executes program state (.define declaration) (Modules.afterCode out)
  | invoke {call : Invocation aliases globals} (callee : Callee) {out : Outcome Lists.Value} :
      RunsAt callee.layout.site callee.BodyRuns (block aliases globals) callee.layout.id call.callee (readSlot aliases call.callee)
        call.arguments call.codes call.keywords.source call.keywords.codes call.star call.mapping state out →
      Executes program state (.invoke call) (afterWrite call.destination out)

/-- Stop at the first reached failure, keeping its exact residual heap. -/
inductive SuiteRuns {aliases globals : List String} :
    Program → State → List (Step aliases globals) → Modules.Result Unit → Prop where
  | done (program : Program) (state : State) : SuiteRuns program state [] (.ok () state)
  | next {program state middle head rest out} :
      Executes program state head (.ok () middle) →
      SuiteRuns (head.emit program) middle rest out →
      SuiteRuns program state (head :: rest) out
  | failed {program state stopped head rest error} :
      Executes program state head (.error error stopped) →
      SuiteRuns program state (head :: rest) (.error error stopped)

inductive Runs (commands : List Command) (producer consumer : ResolvedModule)
    (plan : Consumer) (exports : Environment) (caller : Session) :
    Loader.Result Modules.Published → Prop where
  | producerError {error : Loader.Error} {reached : Session} :
      Producer commands producer.source { caller with runtime := Modules.enter consumer.source caller.runtime }
        (.error error reached) →
      Runs commands producer consumer plan exports caller
        (.error error { reached with runtime := Modules.restoreThread caller.runtime reached.runtime })
  | missing {published : Modules.Published} {reached : Session} {error : Modules.Error} :
      Producer commands producer.source { caller with runtime := Modules.enter consumer.source caller.runtime }
        (.ok published reached) →
      BindsAlias plan published reached.runtime (.error error reached.runtime) →
      Runs commands producer consumer plan exports caller
        (observed 1 consumer.source caller.runtime reached.cache (.error error reached.runtime))
  | called {published : Modules.Published} {reached : Session} {bound : State}
      {callee : Callable} {out : Modules.Result Unit} :
      Producer commands producer.source { caller with runtime := Modules.enter consumer.source caller.runtime }
        (.ok published reached) →
      BindsAlias plan published reached.runtime (.ok () bound) →
      exports plan.name = some callee →
      SuiteRuns producer.program bound plan.body out →
      Runs commands producer consumer plan exports caller (observed 1 consumer.source caller.runtime reached.cache out)

abbrev Agrees (commands : List Command) (producer consumer : ResolvedModule)
    (plan : Consumer) (exports : Environment) (caller : Session) : Prop :=
  ∃ out, Runs commands producer consumer plan exports caller out ∧
    Loader.Runs consumer.program (graph producer consumer plan) [] (.initialize 1) caller out ∧
    Loader.load consumer.program (graph producer consumer plan) 1 caller = out

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

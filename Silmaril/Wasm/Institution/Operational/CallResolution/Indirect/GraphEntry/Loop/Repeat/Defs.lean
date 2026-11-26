module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat

open Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

/-- The selected arm writes the results and saved site operands, then
branches to the loop. A subsequent empty arm can fall through to the
ordinary function tail. Stack types in `saved` are top first. -/
structure Guard (entry : Entry) (program : Graph.Program) (tables : Source.Tables) where
  indices : List LocalIdx
  saved : List NumType
  source : entry.insideTail = indices.map Graph.Op.set ++ [.br ⟨1⟩ []]
  binding : (entry.op.bind program tables entry.owner.declaration.module).isSome = true
  typeIndex : entry.owner.declaration.module.types[entry.op.typeIndex.toNat]? = some entry.op.signature
  operands : Prefix.check entry.owner.localTypes [] entry.before =
    some (.int .i32 :: entry.op.signature.params.reverse ++ saved)
  writes : Locals.check entry.owner.localTypes (entry.op.signature.results.reverse ++ saved)
    (indices.map Locals.Op.set) = some []

/-- The numeric prefix is evaluated again on each visit. Each recipe is
independent of the native step relation. -/
inductive Site (entry : Entry) (program : Graph.Program) (tables : Source.Tables) (locals : List Value) where
  | call {states stack active call}
      (trace : OperandTrace locals [] entry.before states (.values stack))
      (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active)
      (invoked : active.invocation program = some call)
  | lookupTrap {states stack active out}
      (trace : OperandTrace locals [] entry.before states (.values stack))
      (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active)
      (resolved : active.resolve program = some out) (trap : LookupTrap out)
  | operandTrap {states stack rest} (trace : OperandTrace locals [] entry.before states (.trap stack rest))

inductive Handoff (A : Type) where
  | call (call : Context.Invocation)
  | trap (phase : Resume.Phase A)

/-- A prefix stores the unconsumed portion of the rendered numeric and
lookup recipe. A subsequent iteration creates a fresh recipe from its locals. -/
inductive Phase (A C : Type) where
  | control (state : Loop.State)
  | pending (current : C) (rest : List C) (next : Handoff A)
  | callee (call : Context.Invocation) (phase : Graph.Phase)
  | write (locals stack : List Value) (indices : List LocalIdx)
  | branch (locals : List Value)
  | trap (phase : Resume.Phase A)

def Phase.resume {A C : Type} : Handoff A → Phase A C
  | .call call => .callee call call.entered
  | .trap phase => .trap phase

def Phase.advance {A C : Type} (next : Handoff A) : List C → Phase A C
  | [] => .resume next
  | head :: rest => .pending head rest next

def Phase.Live {A C : Type} : Phase A C → Prop
  | .control ⟨_, .caller⟩ | .callee _ (.done .trap) | .trap _ => False
  | _ => True

structure Recipe (A C : Type) where
  before : List C
  next : Handoff A

/-- The only back edge is the branch to the live loop. It reinstalls the
source loop with its updated locals. The callee return and selected-site
handoffs share the same native configuration on either side. -/
inductive Edge {A C : Type} (entry : Entry) (program : Graph.Program)
    (indices : List LocalIdx) (recipe : List Value → Recipe A C → Prop) :
    Phase A C → Phase A C → Prop where
  | control {a b} (step : Loop.Edge entry a b) : Edge entry program indices recipe (.control a) (.control b)
  | site {locals head rest next} (path : recipe locals ⟨head :: rest, next⟩) :
      Edge entry program indices recipe (.control ⟨locals, .site⟩) (.advance next rest)
  | pending {head rest next} :
      Edge entry program indices recipe (.pending head rest next) (.advance next rest)
  | callee {call a b} (live : a.LabelOutcome) (step : program.FrameEdge call.address a b) :
      Edge entry program indices recipe (.callee call a) (.callee call b)
  | write {locals stack i more saved value updated} (split : stack = saved ++ [value])
      (step : Locals.Edge ⟨locals, [.value value, .set i]⟩ ⟨updated, []⟩) :
      Edge entry program indices recipe (.write locals stack (i :: more)) (.write updated saved more)
  | armBranch {locals} : Edge entry program indices recipe (.write locals [] []) (.branch locals)
  | return_ {call values b}
      (step : Edge entry program indices recipe (.write call.caller.locals (call.saved ++ values) indices) b) :
      Edge entry program indices recipe (.callee call (.done (.values values))) b
  | restart {locals} : Edge entry program indices recipe (.branch locals) (.control ⟨locals, .enter⟩)

abbrev Runs {A C : Type} (entry : Entry) (program : Graph.Program) (indices : List LocalIdx)
    (recipe : List Value → Recipe A C → Prop) := Relation.ReflTransGen (Edge entry program indices recipe)

def Readback {A C : Type} (entry : Entry) (program : Graph.Program) (indices : List LocalIdx)
    (recipe : List Value → Recipe A C → Prop) (render : Phase A C → C)
    (stop : Phase A C → C → Prop) (initial : Loop.State) (dst : C) : Prop :=
  (∃ phase, Runs entry program indices recipe (.control initial) phase ∧ dst = render phase) ∨
  (∃ phase, Runs entry program indices recipe (.control initial) phase ∧ ¬ phase.Live ∧ stop phase dst)

def coreWrite {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame)
    (locals stack : List Value) (indices : List LocalIdx) : Core.Config H :=
  entry.coreArmWrap outer ⟨s, (entry.frame locals).toCore, coreValues stack ++
    (indices.map (fun i => .plain (.localSet i)) ++ [.plain (.br ⟨1⟩)])⟩

open Wasm.Lime1.Execution in
def limeWrite {H : Type} (entry : Entry) (s : Store H) (outer : Frame)
    (locals stack : List Value) (indices : List LocalIdx) : Config H :=
  entry.limeArmWrap outer ⟨s, entry.frame locals, values stack ++
    (indices.map (fun i => .source (.localSet i)) ++ [.source (.br ⟨1⟩)])⟩

def corePhase {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) :
    Phase Core.Admin (Core.Config H) → Core.Config H
  | .control state => entry.coreConfig s outer state
  | .pending current .. => current
  | .callee call phase => Resume.coreCallee entry s outer call phase
  | .write locals stack indices => coreWrite entry s outer locals stack indices
  | .branch locals => entry.coreLoopWrap outer ⟨s, (entry.frame locals).toCore, [.plain (.br ⟨0⟩)]⟩
  | .trap phase => Resume.corePhase entry s outer phase

open Wasm.Lime1.Execution in
def limePhase {H : Type} (entry : Entry) (s : Store H) (outer : Frame) : Phase Admin (Config H) → Config H
  | .control state => entry.limeConfig s outer state
  | .pending current .. => current
  | .callee call phase => Resume.limeCallee entry s outer call phase
  | .write locals stack indices => limeWrite entry s outer locals stack indices
  | .branch locals => entry.limeLoopWrap outer ⟨s, entry.frame locals, [.source (.br ⟨0⟩)]⟩
  | .trap phase => Resume.limePhase entry s outer phase

def coreRecipe {H : Type} {entry : Entry} {program : Graph.Program} {tables : Source.Tables}
    {locals : List Value} (s : Core.Store H) (outer : Frame) :
    Site entry program tables locals → Recipe Core.Admin (Core.Config H)
  | .call (states := states) (active := active) (call := call) _ _ _ =>
      ⟨states.map (entry.coreOperands s outer locals) ++
        (Outcome.resolved call.address).coreTrace.map (entry.coreLookup s outer active), .call call⟩
  | .lookupTrap (states := states) (active := active) (out := out) _ _ _ _ =>
      ⟨states.map (entry.coreOperands s outer locals) ++
        ((out.coreTrace.map (entry.coreLookup s outer active)).dropLast), .trap (Resume.coreTrap entry active out)⟩
  | .operandTrap (states := states) (stack := stack) (rest := rest) _ =>
      ⟨states.map (entry.coreOperands s outer locals), .trap (.armTrap locals stack (entry.coreSiteCode rest))⟩

open Wasm.Lime1.Execution in
def limeRecipe {H : Type} {entry : Entry} {program : Graph.Program} {tables : Source.Tables}
    {locals : List Value} (s : Store H) (outer : Frame) : Site entry program tables locals → Recipe Admin (Config H)
  | .call (states := states) (active := active) (call := call) _ _ _ =>
      ⟨states.map (entry.limeOperands s outer locals) ++
        [entry.limeLookup s outer active, entry.limeLookupResult s outer active (.resolved call.address)], .call call⟩
  | .lookupTrap (states := states) (active := active) _ _ _ _ =>
      ⟨states.map (entry.limeOperands s outer locals) ++ [entry.limeLookup s outer active],
        .trap (Resume.limeTrap entry active)⟩
  | .operandTrap (states := states) (stack := stack) (rest := rest) _ =>
      ⟨states.map (entry.limeOperands s outer locals), .trap (.armTrap locals stack (entry.limeSiteCode rest))⟩

def coreRecipes {H : Type} (entry : Entry) (program : Graph.Program) (tables : Source.Tables) (s : Core.Store H)
    (outer : Frame) (locals : List Value) (path : Recipe Core.Admin (Core.Config H)) : Prop :=
  ∃ site : Site entry program tables locals, path = coreRecipe s outer site

open Wasm.Lime1.Execution in
def limeRecipes {H : Type} (entry : Entry) (program : Graph.Program) (tables : Source.Tables) (s : Store H)
    (outer : Frame) (locals : List Value) (path : Recipe Admin (Config H)) : Prop :=
  ∃ site : Site entry program tables locals, path = limeRecipe s outer site

def Stop {A C : Type} (entry : Entry) (program : Graph.Program) (render : Resume.Phase A → C)
    (caller : Graph.Phase → C) (pending : List A) : Phase A C → C → Prop
  | .control ⟨locals, .caller⟩, dst =>
      ∃ phase, program.FrameRuns entry.address (entry.callerPhase locals) phase ∧ dst = caller phase
  | .callee call (.done .trap), dst =>
      Resume.Finish entry program render caller (.armTrap call.caller.locals call.saved pending) dst
  | .trap phase, dst => Resume.Finish entry program render caller phase dst
  | _, _ => False

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat

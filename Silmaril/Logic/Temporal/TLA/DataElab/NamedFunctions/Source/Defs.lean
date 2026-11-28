module

public import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Defs
public import Silmaril.Logic.Temporal.TLA.DataElab.Sequences.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs

/-! A source profile for the local predecessor function used by WriteThroughCache.vmem. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source

open Resolution Data.Tagged

universe u

@[expose] public section

abbrev Expr := Term Sequences.signature .collections

def rangeId : BindingId := .declared ⟨Sequences.naturalsId, [.member 3]⟩
def subId : BindingId := .declared ⟨Sequences.naturalsId, [.member 4]⟩
def lenId : BindingId := .declared ⟨Sequences.sequencesId, [.member 1]⟩

/-- Identities and slots of the admitted LET after ordinary collection lowering.
The corresponding term describes every recursive use and its positive-key guard. -/
structure Predecessor where
  site : Site
  self : Nat
  index : Nat
  old : Nat
  queue : BindingId
  base : BindingId
  index_ne_self : index ≠ self
  index_ne_old : index ≠ old
  deriving Repr

def Predecessor.binder (p : Predecessor) : BindingId :=
  .declared ((p.site.child (.bound 0)).child (.binder 0))

def Predecessor.len (p : Predecessor) : Expr :=
  .external lenId 1 (by decide) [.flexible p.queue]

def Predecessor.bound (p : Predecessor) : Expr :=
  .external rangeId 2 (by decide) [.numeral 0, p.len]

def Predecessor.previous (p : Predecessor) : Expr :=
  .index rfl (.witness p.self) (.external subId 2 (by decide) [.witness p.index, .numeral 1])

def Predecessor.field (p : Predecessor) (field : String) : Expr :=
  .index rfl (.index rfl (.index rfl (.flexible p.queue) (.witness p.index)) (.numeral 2))
    (.string rfl field)

def Predecessor.body (p : Predecessor) : Expr :=
  .ite (.eq false (.witness p.index) (.numeral 0)) (.flexible p.base)
    (.ite (.eq false (p.field "op") (.string rfl "Rd")) p.previous
      (.except rfl p.previous [(p.old, [p.field "adr"], p.field "val")]))

def Predecessor.function (p : Predecessor) : Expr :=
  .function rfl p.site p.binder p.index p.bound p.body

def Predecessor.term (p : Predecessor) : Expr :=
  .index rfl (.choose p.self none (.eq false (.witness p.self) p.function)) p.len

/-- The admitted syntax is tied to the actual expanded term by an equality proof.
Every recursive call is at index minus one and is guarded by the zero test. -/
structure CheckedVMem where
  private mk ::
  term : Expr
  wellFormed : term.isWellFormed [] = true
  predecessor : Predecessor
  shape : term = predecessor.term

inductive Diagnostic where
  | resolution (error : Resolution.Diagnostic)
  | levels (error : Levels.Diagnostic)
  | lowering (error : DataElab.Diagnostic)
  | unsupportedPredecessor (site : Site)
  deriving Repr

end

private def certify (term : Expr) : Option { p : Predecessor // term = p.term } :=
  match term with
  | .index _ (.choose self none (.eq false (.witness self') (.function _ site binder index
      (.external range 2 _ [.numeral 0, .external boundLen 1 _ [.flexible boundQueue]])
      (.ite (.eq false (.witness zeroIndex) (.numeral 0)) (.flexible base)
        (.ite (.eq false
            (.index _ (.index _ (.index _ (.flexible opQueue) (.witness opIndex)) (.numeral 2))
              (.string _ "op"))
            (.string _ "Rd"))
          (.index _ (.witness readSelf) (.external readSub 2 _ [.witness readIndex, .numeral 1]))
          (.except _ (.index _ (.witness writeSelf)
              (.external writeSub 2 _ [.witness writeIndex, .numeral 1]))
            [(old,
              [.index _ (.index _ (.index _ (.flexible adrQueue) (.witness adrIndex)) (.numeral 2))
                (.string _ "adr")],
              .index _ (.index _ (.index _ (.flexible valQueue) (.witness valIndex)) (.numeral 2))
                (.string _ "val"))]))))))
      (.external resultLen 1 _ [.flexible queue]) => do
    if slots : index ≠ self ∧ index ≠ old then
      if evidence : self' = self ∧
          binder = .declared ((site.child (.bound 0)).child (.binder 0)) ∧ range = rangeId ∧
          boundLen = lenId ∧ resultLen = lenId ∧ readSub = subId ∧ writeSub = subId ∧
          boundQueue = queue ∧ opQueue = queue ∧ adrQueue = queue ∧ valQueue = queue ∧
          readSelf = self ∧ writeSelf = self ∧ zeroIndex = index ∧ opIndex = index ∧
          readIndex = index ∧ writeIndex = index ∧ adrIndex = index ∧ valIndex = index then
        return ⟨⟨site, self, index, old, queue, base, slots.1, slots.2⟩, by
          rcases evidence with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          rfl⟩
      else none
    else none
  | _ => none

private def lowerLet (registry : CheckedRegistry) (maxDepth : Nat) (site : Site)
    (bounds : List Surface.Bound) (body result : Surface.Expr) : LowerM Expr := do
  let decl := site.child (.letDecl 0)
  let some binding := registry.findBinding (.declared decl) | fail decl .invalidExpansion
  unless binding.kind = .namedFunction do fail decl .invalidExpansion
  let slot ← freshWitness
  let visit : Visit Sequences.signature .collections := fun locals origin expr =>
    lower registry .collections false false maxDepth [] locals origin (.expression expr)
  let rhs ← lowerFunction registry visit [(binding.id, .expression (.witness slot))]
    decl rfl bounds body
  let value := Term.choose slot none (.eq false (.witness slot) rhs)
  visit [(binding.id, .expression value)] (site.child .body) result

/-- Select a nullary source operator whose complete body fits the certified predecessor
form. Resolve against the pinned standard signatures and admit only state expressions. -/
public def check (source : Surface.Module) (root : ModuleId) (imports : ImportMap)
    (maxDepth : Nat) (name : Name) : Except Diagnostic CheckedVMem := do
  let registry ← (resolveWith .namedFunctionSyntax
    ((root, .parsed source imports) :: Sequences.inputs) root).mapError .resolution
  let externalLevels := Sequences.levels.filter fun (id, _) => (registry.findBinding id).isSome
  let levels ← (Levels.check registry externalLevels).mapError .levels
  let some binding := (registry.moduleAt root).bind (·.bindingAt name)
    | throw (.unsupportedPredecessor ⟨root, []⟩)
  let (home, expression) ← (definitionBody registry binding.id).mapError .lowering
  let site := home.child .body
  let some summary := levels.operatorAt binding.id | throw (.unsupportedPredecessor site)
  unless summary.result.floor.atMost .state && summary.result.dependencies.isEmpty &&
      summary.requirements.isEmpty do
    throw (.unsupportedPredecessor site)
  let .letIn [.definition (.function _ _ bounds body)] result := expression
    | throw (.unsupportedPredecessor site)
  let (term, _) ← ((lowerLet registry maxDepth site bounds body result).run 0).mapError .lowering
  let some ⟨p, shape⟩ := certify term | throw (.unsupportedPredecessor site)
  if wellFormed : term.isWellFormed [] = true then
    return ⟨term, wellFormed, p, shape⟩
  else throw (.lowering ⟨site, .invalidExpansion⟩)

/-- Interpret the admitted term using ordinary collection evaluation, including the
anonymous constructor, CHOOSE, and the final application. -/
@[expose] public noncomputable def CheckedVMem.eval (checked : CheckedVMem)
    (policy : Tagged.Policy.{u}) (invalid : Tagged.CollectionPolicy.{u})
    (sequence : SequencePolicy.{u}) (graph : Unspecified.{u})
    (endpoints : Endpoints.EndpointValuation Value.{u}) : Value.{u} :=
  checked.term.eval (policy.collectionOperations invalid graph) policy.booleans
    (Sequences.external policy sequence) ⟨endpoints.rigid, endpoints.source⟩
    (fun _ => .set .empty) endpoints.target

end Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source

module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Provider.Named.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Thms

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)
open Isomorphism.RecursiveCall.Numbered (CaptureCode ExactValueCheck)
open Isomorphism.RecursiveCall.Numbered.Prefix (AllocationHistory AllocatingClient CheckedProviderAssembly)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {actions : Actions m σ}
variable {ids : GlobalRel} {keys : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
variable {assembly : CheckedProviderAssembly actions ids keys captureCode} {name : String} {ty : Ty V S}

theorem selectedDemandL_linked (lookup : assembly.LookupReceipt name ty) :
    selectedDemandL lookup = .linked (.cons lookup.values.left .nil) lookup.entry.provider.chain.checked.storeL := by
  rw [lookup.values_left]
  obtain ⟨entry, selected, rfl⟩ := lookup
  rfl

theorem selectedDemandR_linked (lookup : assembly.LookupReceipt name ty) :
    selectedDemandR lookup = .linked (.cons lookup.values.right .nil) lookup.entry.provider.chain.checked.storeR := by
  rw [lookup.values_right]
  obtain ⟨entry, selected, rfl⟩ := lookup
  rfl

/-- Reindex an existing demand certificate at a named result after checking
both actual closures and their original exit stores. This reads stored values. -/
def matchNamedExport [DecidableEq σ] {summary : MemberSummary V S}
    {left right : Outcome m σ [summary.fn.port]} (lookup : assembly.LookupReceipt name summary.fn.port)
    (sound : Export actions summary left right) (exactValue : ExactValueCheck m) :
    Option (PLift (selectedDemandL lookup = left ∧ selectedDemandR lookup = right)) := do
  let sameL ← exactValue lookup.values.left sound.targetL
  let sameR ← exactValue lookup.values.right sound.targetR
  if stores : lookup.entry.provider.chain.checked.storeL = sound.store ∧
      lookup.entry.provider.chain.checked.storeR = sound.store then
    let relocate := fun (target : m.Val summary.fn.port) (store : σ) =>
      Outcome.linked (.cons target .nil) store
    some ⟨(selectedDemandL_linked lookup).trans
      ((congrArg₂ relocate sameL.down stores.1).trans sound.linkedL.symm),
      (selectedDemandR_linked lookup).trans ((congrArg₂ relocate sameR.down stores.2).trans sound.linkedR.symm)⟩
  else none

/-- Recover the full store traces using the selected provider's original
history at the boundaries recorded by the lookup. -/
theorem NamedDemand.historyL {summary : MemberSummary V S} (source : NamedDemand assembly summary) :
    AllocationHistory actions assembly.unitsL assembly.chain.initialL assembly.chain.checked.storeL :=
  source.lookup.entry.traceL.reassemble source.lookup.entry.provider.chain.historyL

theorem NamedDemand.historyR {summary : MemberSummary V S} (source : NamedDemand assembly summary) :
    AllocationHistory actions assembly.unitsR assembly.chain.initialR assembly.chain.checked.storeR :=
  source.lookup.entry.traceR.reassemble source.lookup.entry.provider.chain.historyR

/-- Use the lookup's exact import check, then transport its equalities into
the exact targets recorded by the existing demand receipt. -/
def NamedDemand.check {summary : MemberSummary V S} (source : NamedDemand assembly summary)
    (exactValue : ExactValueCheck m) (left right : m.Val summary.fn.port) :
    Option (PLift (left = source.sound.targetL ∧ right = source.sound.targetR)) := do
  let same ← source.lookup.checkImports exactValue left right
  let selectedL := (Outcome.linked.inj ((selectedDemandL_linked source.lookup).symm.trans source.sound.linkedL)).1
  let selectedR := (Outcome.linked.inj ((selectedDemandR_linked source.lookup).symm.trans source.sound.linkedR)).1
  pure ⟨same.down.1.trans (congrArg (fun values => values.get .head) selectedL),
    same.down.2.trans (congrArg (fun values => values.get .head) selectedR)⟩

/-- Check the already materialized imports at their typed ports. Each
named pair is checked against its own lookup, even at repeated signatures. -/
def NamedImports.check (exactValue : ExactValueCheck m) {extra : Ports (Ty V S)} :
    {ports : Ports (Ty V S)} → (sources : NamedImports assembly ports) →
    (inputsL inputsR : Tuple m.Val (ports ++ extra)) → Option (sources.Rows inputsL inputsR)
  | _, .nil, _, _ => some ⟨fun _ => none, fun _ => none, trivial⟩
  | _, .cons source rest, .cons left tailL, .cons right tailR =>
    match source.check exactValue left right with
    | none => none
    | some same => do
      let slot : Fin (source.sound.earlier.members.length + 1) := 0
      let knownL := Known.callable (guard := source.sound.dispatch.left) slot
        source.sound.targetL source.sound.capsL source.sound.resolvedL
      let knownR := Known.callable (guard := source.sound.dispatch.right) slot
        source.sound.targetR source.sound.capsR source.sound.resolvedR
      let tail ← rest.check exactValue tailL tailR
      pure ⟨(fun p => match p with
        | .head => some ⟨Known.oldSlot rest.dispatch.left (same.down.1.symm ▸ knownL)⟩
        | .tail p => (tail.left p).map fun member => ⟨Known.newSlot source.sound.dispatch.left member.down⟩),
        (fun p => match p with
        | .head => some ⟨Known.oldSlot rest.dispatch.right (same.down.2.symm ▸ knownR)⟩
        | .tail p => (tail.right p).map fun member => ⟨Known.newSlot source.sound.dispatch.right member.down⟩),
        ⟨same.down.1, same.down.2, tail.matched⟩⟩

def NamedSlot.reindex {summary summary' : MemberSummary V S} {imports : Ports (Ty V S)}
    {left right : SlotGuard m summary} {left' right' : SlotGuard m summary'}
    {inputsL inputsR : Tuple m.Val imports} (slot : NamedSlot left right inputsL inputsR)
    (same : summary' = summary) (guardL : left' = same.symm ▸ left)
    (guardR : right' = same.symm ▸ right) : NamedSlot left' right' inputsL inputsR := by
  cases same
  exact guardL.symm ▸ guardR.symm ▸ slot

/-- Find the export at a particular dispatch slot using the original checked
import order. Internal provider slots have no direct client import. -/
def NamedImports.lookupSlot {extra : Ports (Ty V S)} :
    {ports : Ports (Ty V S)} → (sources : NamedImports assembly ports) →
    (inputsL inputsR : Tuple m.Val (ports ++ extra)) → sources.Matches inputsL inputsR →
    (i : Fin sources.table.members.length) →
    Option (NamedSlot (sources.dispatch.left i) (sources.dispatch.right i) inputsL inputsR)
  | _, .nil, _, _, _, i => i.elim0
  | _, .cons (summary := summary) source rest, .cons targetL tailL, .cons targetR tailR, matched, i =>
    let earlier := prepend summary source.sound.earlier
    let first : Fin (source.sound.earlier.members.length + 1) := 0
    let head : NamedSlot (source.sound.dispatch.left first) (source.sound.dispatch.right first)
        (.cons targetL tailL) (.cons targetR tailR) :=
      ⟨.head, source.sound.capsL, source.sound.capsR,
        matched.1.symm ▸ source.sound.resolvedL, matched.2.1.symm ▸ source.sound.resolvedR⟩
    slotCases earlier rest.table
      (result := fun j => Option (NamedSlot ((source.sound.dispatch.left.combine rest.dispatch.left) j)
        ((source.sound.dispatch.right.combine rest.dispatch.right) j) (.cons targetL tailL) (.cons targetR tailR)))
      (fun j => Fin.cases (motive := fun k => Option (NamedSlot
        ((source.sound.dispatch.left.combine rest.dispatch.left) (leftIndex earlier rest.table k))
        ((source.sound.dispatch.right.combine rest.dispatch.right) (leftIndex earlier rest.table k))
        (.cons targetL tailL) (.cons targetR tailR)))
        (some (NamedSlot.reindex head
          (append_at_old earlier rest.table first)
          (Guard.combine_left source.sound.dispatch.left rest.dispatch.left first)
          (Guard.combine_left source.sound.dispatch.right rest.dispatch.right first)))
        (fun _ => none) j)
      (fun j => (rest.lookupSlot tailL tailR matched.2.2 j).map fun slot =>
        let widened : NamedSlot (rest.dispatch.left j) (rest.dispatch.right j)
            (.cons targetL tailL) (.cons targetR tailR) :=
          ⟨.tail slot.port, slot.capsL, slot.capsR, slot.readyL, slot.readyR⟩
        NamedSlot.reindex widened
          (append_at_new earlier rest.table j)
          (Guard.combine_right source.sound.dispatch.left rest.dispatch.left j)
          (Guard.combine_right source.sound.dispatch.right rest.dispatch.right j))
      i

def NamedSlot.checkCall {summary : MemberSummary V S} {imports : Ports (Ty V S)}
    {past : List (Ports (Ty V S))} {left right : SlotGuard m summary} {inputsL inputsR : Tuple m.Val imports}
    (slot : NamedSlot left right inputsL inputsR) (exact : ExactValueCheck m) (useRight : Bool)
    (locals : Locals m.Val past) (target : Origin imports past summary.fn.port)
    (witnesses : Wires imports past summary.captures) :
    Option (PLift ((if useRight then right else left)
      ((Wires.read (.cons target .nil) (if useRight then inputsR else inputsL) locals).get .head)
      (witnesses.read (if useRight then inputsR else inputsL) locals))) := do
  if address : target.address = (Origin.arg slot.port : Origin imports past summary.fn.port).address then
    let same := NestedTheta.Equality.addresses_injective
      (.cons target .nil) (.cons (.arg slot.port) .nil) (by simp [Wires.addresses, address])
    let equal ← exact.tuple (witnesses.read (if useRight then inputsR else inputsL) locals)
      (if useRight then slot.capsR else slot.capsL)
    let ready : (if useRight then right else left) ((if useRight then inputsR else inputsL).get slot.port)
        (if useRight then slot.capsR else slot.capsL) := by
      cases useRight
      · exact slot.readyL
      · exact slot.readyR
    pure ⟨same.symm ▸ equal.down.symm ▸ ready⟩
  else none

/-- Synthesize resolution for one actual λ capture layout. The existing
provenance checker projects the numbered operands into the linker prefix.
The named slot fixes the exact target import and its typed witness values. -/
def NamedImports.resolveDirect {ports extra : Ports (Ty V S)} {fn : Function V S}
    {past : List (Ports (Ty V S))} (sources : NamedImports assembly ports)
    (inputsL inputsR : Tuple m.Val (ports ++ extra)) (matched : sources.Matches inputsL inputsR)
    (exact : ExactValueCheck m) (useRight : Bool)
    (binding : Binding Op sources.table (ports ++ extra) past fn) (locals : Locals m.Val past) :
    Option (PLift (binding.resolved (if useRight then sources.dispatch.right else sources.dispatch.left)
      (if useRight then inputsR else inputsL) locals)) :=
  let inputs := if useRight then inputsR else inputsL
  let guard := if useRight then sources.dispatch.right else sources.dispatch.left
  let scope : Scope m := ⟨past, sources.table, locals, locals, guard, guard⟩
  let resolve : Direct.SourceResolver inputs inputs scope := fun i wires =>
    match sources.lookupSlot inputsL inputsR matched i with
    | none => none
    | some slot =>
      let .cons target witnesses := wires
      (NamedSlot.checkCall slot exact useRight locals target witnesses).map fun ready => by
        cases useRight <;> exact ⟨ready.down, ready.down⟩
  (Direct.synthesizeWith (fn := fn) resolve binding.captures binding.body).map fun proof => ⟨proof.down.1⟩

def NamedImports.analyzeLayoutsWith {ports extra : Ports (Ty V S)} {fn : Function V S}
    {value : ValueSort V S} {shifted shiftedR : Bool}
    (sources : NamedImports assembly ports)
    (layout : AllocationPlan Op sources.table (ports ++ extra) fn value shifted)
    (right : layout.Layout shiftedR)
    (exactValue : ExactValueCheck m) (unitL unitR : Nat) (inputsL inputsR : Tuple m.Val (ports ++ extra))
    (initial : σ) (storeL : assembly.chain.checked.storeL = initial) (storeR : assembly.chain.checked.storeR = initial)
    (receipt : LinkedRows (layout.linkDelta actions unitL inputsL initial)
      ((layout.withLayout right).linkDelta actions unitR inputsR initial))
    (resolve : sources.Matches inputsL inputsR → Option (PLift (
      layout.binding.resolved sources.dispatch.left inputsL ((AllocatingClient.initialLocals m shifted).snoc receipt.left) ∧
      (layout.withLayout right).binding.resolved sources.dispatch.right inputsR
        ((AllocatingClient.initialLocals m shiftedR).snoc receipt.right)))) :
    Option (ExportAnalysis actions layout.binding.summary
      (Executable.link actions unitL layout.numbered.toGraph inputsL assembly.chain.checked.storeL)
      (Executable.link actions unitR (layout.withLayout right).numbered.toGraph inputsR assembly.chain.checked.storeR)) := do
  let admitted ← sources.check exactValue inputsL inputsR
  let some ready := resolve admitted.matched | none
  let checked ← layout.analyzeLayouts right sources.dispatch unitL unitR inputsL inputsR initial receipt
    admitted.left admitted.right ready.down.1 ready.down.2
  pure ⟨checked.linked.relink
    (congrArg (Executable.link actions unitL layout.numbered.toGraph inputsL) storeL)
    (congrArg (Executable.link actions unitR (layout.withLayout right).numbered.toGraph inputsR) storeR),
    checked.problem, checked.mem_problem⟩

/-- Check the actual named imports once and analyze a shared λ body over
the two independently numbered capture boundaries. The initializer
receipt fixes the actual local rows and the common invocation store. -/
def NamedImports.analyzeLayouts {ports extra : Ports (Ty V S)} {fn : Function V S}
    {value : ValueSort V S} {shifted shiftedR : Bool}
    (sources : NamedImports assembly ports)
    (layout : AllocationPlan Op sources.table (ports ++ extra) fn value shifted)
    (right : layout.Layout shiftedR)
    (exactValue : ExactValueCheck m) (unitL unitR : Nat) (inputsL inputsR : Tuple m.Val (ports ++ extra))
    (initial : σ) (storeL : assembly.chain.checked.storeL = initial) (storeR : assembly.chain.checked.storeR = initial)
    (receipt : LinkedRows (layout.linkDelta actions unitL inputsL initial)
      ((layout.withLayout right).linkDelta actions unitR inputsR initial))
    (readyL : sources.Matches inputsL inputsR → layout.binding.resolved sources.dispatch.left inputsL
      ((AllocatingClient.initialLocals m shifted).snoc receipt.left))
    (readyR : sources.Matches inputsL inputsR → (layout.withLayout right).binding.resolved sources.dispatch.right inputsR
      ((AllocatingClient.initialLocals m shiftedR).snoc receipt.right)) :
    Option (ExportAnalysis actions layout.binding.summary
      (Executable.link actions unitL layout.numbered.toGraph inputsL assembly.chain.checked.storeL)
      (Executable.link actions unitR (layout.withLayout right).numbered.toGraph inputsR assembly.chain.checked.storeR)) :=
  sources.analyzeLayoutsWith layout right exactValue unitL unitR inputsL inputsR initial storeL storeR receipt
    (fun matched => some ⟨readyL matched, readyR matched⟩)

/-- Analyze an allocating layout pair by synthesizing static resolution
from the checked named imports and the actual target and witness origins. -/
def NamedImports.analyzeLayoutsDirect {ports extra : Ports (Ty V S)} {fn : Function V S}
    {value : ValueSort V S} {shifted shiftedR : Bool}
    (sources : NamedImports assembly ports)
    (layout : AllocationPlan Op sources.table (ports ++ extra) fn value shifted)
    (right : layout.Layout shiftedR)
    (exactValue : ExactValueCheck m) (unitL unitR : Nat) (inputsL inputsR : Tuple m.Val (ports ++ extra))
    (initial : σ) (storeL : assembly.chain.checked.storeL = initial) (storeR : assembly.chain.checked.storeR = initial)
    (receipt : LinkedRows (layout.linkDelta actions unitL inputsL initial)
      ((layout.withLayout right).linkDelta actions unitR inputsR initial)) :
    Option (ExportAnalysis actions layout.binding.summary
      (Executable.link actions unitL layout.numbered.toGraph inputsL assembly.chain.checked.storeL)
      (Executable.link actions unitR (layout.withLayout right).numbered.toGraph inputsR assembly.chain.checked.storeR)) :=
  sources.analyzeLayoutsWith layout right exactValue unitL unitR inputsL inputsR initial storeL storeR receipt
    (fun matched => do
      let left ← sources.resolveDirect inputsL inputsR matched exactValue false layout.binding
        ((AllocatingClient.initialLocals m shifted).snoc receipt.left)
      let right ← sources.resolveDirect inputsL inputsR matched exactValue true (layout.withLayout right).binding
        ((AllocatingClient.initialLocals m shiftedR).snoc receipt.right)
      pure ⟨left.down, right.down⟩)

/-- Analyze a client from its resolved imports and successful initializer
receipt at the assembly's store. This consumes link results and uses the
existing allocating demand analysis for the final λ. -/
def NamedImports.analyzeAllocating {ports extra : Ports (Ty V S)} {fn : Function V S}
    {value : ValueSort V S} {shifted : Bool}
    (sources : NamedImports assembly ports)
    (layout : AllocationPlan Op sources.table (ports ++ extra) fn value shifted)
    (exactValue : ExactValueCheck m) (unit : Nat) (inputsL inputsR : Tuple m.Val (ports ++ extra))
    (initial : σ) (storeL : assembly.chain.checked.storeL = initial) (storeR : assembly.chain.checked.storeR = initial)
    (receipt : layout.Initialized actions unit inputsL inputsR initial)
    (readyL : sources.Matches inputsL inputsR → layout.binding.resolved sources.dispatch.left inputsL
      ((AllocatingClient.initialLocals m shifted).snoc receipt.left))
    (readyR : sources.Matches inputsL inputsR → layout.binding.resolved sources.dispatch.right inputsR
      ((AllocatingClient.initialLocals m shifted).snoc receipt.right)) :
    Option (ExportAnalysis actions layout.binding.summary
      (Executable.link actions unit layout.numbered.toGraph inputsL assembly.chain.checked.storeL)
      (Executable.link actions unit layout.numbered.toGraph inputsR assembly.chain.checked.storeR)) :=
  sources.analyzeLayouts layout ⟨layout.init, layout.binding.captures⟩ exactValue unit unit inputsL inputsR
    initial storeL storeR receipt readyL readyR

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

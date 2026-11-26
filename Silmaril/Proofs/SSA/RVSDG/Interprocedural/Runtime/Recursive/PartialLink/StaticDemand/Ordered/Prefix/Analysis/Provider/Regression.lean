module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Provider.Named.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Check.Defs
meta import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Check.Defs
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Provider.Named.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.ProviderRegression

open NestedTheta.Liveness (Demand)
open Isomorphism (OutcomesRelated)
open Isomorphism.RecursiveCall.Numbered.Prefix (AdmittedExport)
open Continuation.Partial.Executable (Actions Observation observe runFor)
open Isomorphism.RecursiveCall.Numbered (ExactValueCheck OrdinaryOutputs decidePort instructionCode)
open Isomorphism.RecursiveCall.Numbered.Prefix (AllocatingClient GraphPlan checkGraphProvider admitAllocatingClient)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev global : T := .value (.global (.data ()))
private abbrev single := [num]
private abbrev pair := [num, num]
private abbrev providerFn : Function Unit Unit := ⟨single, single⟩
private abbrev clientFn : Function Unit Unit := ⟨pair, single⟩

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | allocate : Op single single
  | probe : Op [global] []

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .allocate, .cons (.data n) .nil => .cons (.data (2 * n)) .nil
    | .probe, _ => .nil

private def one (n : Nat) : Tuple machine.Val single := .cons (.data n) .nil

private def actions : Actions machine Nat where
  step
    | .allocate, .cons (.data n) .nil => fun store =>
      let n : Nat := n
      some (one (2 * n), store + n + 4)
    | .probe, .cons (.global _ _ (.data n)) .nil => fun store =>
      let n : Nat := n
      if n = 0 then none else some (.nil, store + n)

private def initializer : RVSDG.Term Op single [] [single] single :=
  .bind ⟨single, .simple .allocate, .cons (.arg .head) .nil, fun i => i.elim0⟩
    (fun i => i.elim0) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def providerDelta : DeltaTerm Op single [] (.data ()) :=
  ⟨single, .cons (.arg .head) .nil, [single], initializer⟩

private def providerPrefix (cap : Nat) : DeltaPrefix actions 83 providerDelta (one cap) (one cap) 20 :=
  ⟨.cons (.global 83 0 (.data (2 * cap))) .nil, .cons (.global 83 0 (.data (2 * cap))) .nil,
    20 + cap + 4, rfl, rfl⟩

private def providerBinding : Binding Op (Scope.ordinary machine).table single [[global]] providerFn where
  context := [global]
  captures := .cons (.output (0 : Fin 1) .head) .nil
  sigs := [[]]
  body := .primitive .probe (.cons (.arg .head) .nil) (.ret (.cons (.arg (.tail .head)) .nil))

private def providerTerm : OmegaTerm Op single [providerFn.port] [[global], [providerFn.port]] :=
  ⟨.bind (.delta providerDelta)
    (.bind (.lambda providerBinding.term) (.ret (lastExport [[global]] providerFn)))⟩

private def providerGraph := providerTerm.toGraph

private def providerAnalysis (cap : Nat) :=
  (Plan.analyzeNumberedAfterDelta providerGraph (providerPrefix cap)
    (.finish (scope := (providerPrefix cap).scope) providerBinding (fun _ _ _ => trivial) (fun _ _ _ => trivial))
    (OmegaTerm.toTerm_toGraph providerTerm)).get (by rfl)

private abbrev sound (cap : Nat) := (providerAnalysis cap).linked

local instance : DecidableEq T := decidePort

private def primitiveKeys : NestedTheta.Equality.OpcodeCode Op where
  Key := Nat
  encode
    | .allocate => 0
    | .probe => 1
  injective := by
    intro _ _ x y _
    cases x <;> cases y <;> rfl

private abbrev keys := instructionCode primitiveKeys

private instance : DecidableEq keys.Key :=
  show DecidableEq (Sum Nat (Ports T × Ports T)) from inferInstance

private theorem ordinary : OrdinaryOutputs Op := by
  intro _ _ opcode
  cases opcode <;> rfl

private def exactOrdinary : ExactValueCheck machine :=
  ExactValueCheck.firstOrder (fun _ => inferInstanceAs (DecidableEq Nat))
    (fun _ => inferInstanceAs (DecidableEq Unit))

private def exact : ExactValueCheck machine := fun left right =>
  (ExactValueCheck.lambda keys exactOrdinary left right).orElse (fun _ => exactOrdinary left right)

private def alignment : GraphPlan providerGraph providerGraph :=
  .skipL (.skipR (.start (.lambda .done)))

private def providerCheck (cap : Nat) :=
  checkGraphProvider keys actions Eq ordinary 83 83 (one cap) (one cap)
    providerGraph providerGraph alignment (providerFn := providerFn) .head 20 20

private theorem providerAccepted (cap : Nat) : (providerCheck cap).isSome = true := by cbv

private def checkedProvider (cap : Nat) := (providerCheck cap).get (providerAccepted cap)

private abbrev imports := [providerFn.port, global, num]
private abbrev context := [providerFn.port, global, global]
private abbrev entry := context ++ clientFn.args
private abbrev slots := Ordered.prepend providerBinding.summary (sound 0).earlier
private abbrev importedSlot := (0 : Fin ((sound 0).earlier.members.length + 1))

private def clientDelta : DeltaTerm Op imports [] (.data ()) :=
  ⟨single, .cons (.arg (.tail (.tail .head))) .nil, [single], initializer⟩

private def suffix : Code Op entry [single] [[]] single true (some slots) :=
  .primitive .probe (.cons (.arg (.tail (.tail .head))) .nil)
    (.ret (.cons (.output (0 : Fin 2) .head) .nil))

private def clientBinding : Binding Op slots imports [[global]] clientFn where
  context := context
  captures := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.output (0 : Fin 1) .head) .nil))
  sigs := [single, []]
  body := .familyCall (table := slots) importedSlot .head
    (.cons (.arg (.tail .head)) .nil) (.cons (.arg (.tail (.tail (.tail .head)))) .nil) suffix

private def entryValues (cap : Nat) (target : machine.Val providerFn.port) : Tuple machine.Val imports :=
  .cons target (.cons ((sound cap).capsL.get .head) (one 2))

private theorem resolves (cap : Nat) (target : machine.Val providerFn.port)
    (same : target = (sound cap).targetL) (row : Tuple machine.Val [global]) :
    clientBinding.resolved (sound cap).dispatch.left (entryValues cap target) (row, PUnit.unit) :=
  fun _ _ => ⟨⟨same, rfl⟩, fun _ _ => trivial⟩

private def admit (cap : Nat) (unitId : Nat) (target : machine.Val providerFn.port) :=
  analyzeAllocatingClient (checkedProvider cap) (sound cap) exact unitId
    (entryValues cap (sound cap).targetL) (entryValues cap target) clientDelta clientBinding
    (fun same run => resolves cap _ same run.left) (fun same run => resolves cap _ same run.right)

private def clientGraph := (sound 0).clientGraph clientDelta clientBinding
private def client : AllocatingClient Op imports clientFn (.data ()) false :=
  ⟨clientDelta.toGraph, clientBinding.term.toGraph⟩

#guard (admit 3 84 (sound 3).targetL).isSome
#guard (admit 3 83 (sound 3).targetL).isNone
-- The code and signature match. The stale closure captures a different global payload.
#guard (admit 3 84 (sound 4).targetL).isNone

#guard (admitAllocatingClient actions ordinary exact (checkedProvider 3) 84 84
  (entryValues 3 (sound 3).targetL) (entryValues 3 (sound 3).targetL) client client).isSome

private def result (cap : Nat) := admit cap 84 (sound cap).targetL
private def requested : Demand := (· == 0)
private def emptyDemand : Demand := fun _ => false

#guard (sound 3).store == 27
#guard (result 3).map (·.linked.store) == some 33
#guard (result 3).any fun checked =>
  checked.liveCapture emptyDemand (.tail .head) &&
  checked.liveCapture emptyDemand (.tail (.tail .head)) &&
  checked.liveFormal requested .head &&
  !checked.liveFormal requested (.tail .head)

private def args (spare : Nat) : Tuple machine.Val pair := .cons (.data (41 : Nat)) (one spare)

private def run (cap : Nat) (values : Tuple machine.Val pair) :=
  Executable.run actions 60 84 clientGraph (entryValues cap (sound cap).targetL) .head values (sound cap).store

private def returned : Observation machine Nat single → Option (Nat × Nat)
  | .returned (.cons (.data payload) .nil) store => some (payload, store)
  | _ => none

private def blocked (values : Tuple machine.Val pair) : Option (Nat × Nat × Nat × Nat) :=
  match run 0 values with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, .cons (.global unitId vertex (.data n)) .nil⟩, _⟩ store) =>
    some (unitId, vertex, n, store)
  | _ => none

private def resumed (values : Tuple machine.Val pair) : Option (Nat × Nat) :=
  match run 0 values with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, _⟩, stack⟩ _) =>
    returned (observe actions (runFor actions 60 ⟨.returned .nil stack, 50⟩))
  | _ => none

private def replaced (cap : Nat) :=
  (result cap).map fun checked => checked.substituteDeadFormals requested (args 4) (args 40)

#guard (replaced 3).map (fun values => match values.get (.tail .head) with
  | .data n => n) == some (40 : Nat)
#guard (run 3 (args 4)).toOption.bind returned == some (41, 43)
#guard (replaced 3).bind (fun values => (run 3 values).toOption.bind returned) == some (41, 43)
#guard blocked (args 4) == some (83, 0, 0, 30)
#guard (replaced 0).bind blocked == some (83, 0, 0, 30)
#guard resumed (args 4) == some (41, 54)
#guard (replaced 0).bind resumed == some (41, 54)

-- The second layout inserts an empty φ before each allocated global.
private def providerLayout (shifted : Bool) :
    AllocationPlan Op (Scope.ordinary machine).table single providerFn (.data ()) shifted where
  init := ⟨single, .cons (.arg .head) .nil, [single], initializer⟩
  binding :=
    { context := [global]
      captures := .cons (by
        cases shifted
        · exact .output (0 : Fin 1) .head
        · exact .output (1 : Fin 2) .head) .nil
      sigs := [[]]
      body := providerBinding.body }

private def allocated (shifted : Bool) (cap : Nat) : Tuple machine.Val [global] :=
  .cons (.global 83 (if shifted then 1 else 0) (.data (2 * cap))) .nil

private def providerInitialized (shifted : Bool) (cap : Nat) :
    (providerLayout shifted).Initialized actions 83 (one cap) (one cap) 20 :=
  ⟨allocated shifted cap, allocated shifted cap, 20 + cap + 4,
    by cases shifted <;> rfl, by cases shifted <;> rfl⟩

private def analyzeProvider (shifted : Bool) (cap : Nat) :=
  (providerLayout shifted).analyze (Scope.Checked.ordinary actions).state.dispatch 83 (one cap) (one cap) 20
    (providerInitialized shifted cap) (fun _ => none) (fun _ => none)
    (by cases shifted <;> exact fun _ _ _ => trivial)
    (by cases shifted <;> exact fun _ _ _ => trivial)

private def providerSound (shifted : Bool) (cap : Nat) :=
  ((analyzeProvider shifted cap).get (by cases shifted <;> rfl)).linked

private def clientLayout (shifted : Bool) :
    AllocationPlan Op (prepend providerBinding.summary (Scope.ordinary machine).table)
      imports clientFn (.data ()) shifted where
  init := ⟨single, .cons (.arg (.tail (.tail .head))) .nil, [single], initializer⟩
  binding :=
    { context := context
      captures := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (by
        cases shifted
        · exact .output (0 : Fin 1) .head
        · exact .output (1 : Fin 2) .head) .nil))
      sigs := [single, []]
      body := clientBinding.body }

private def relocatedEntry (shifted : Bool) (cap : Nat) (target : machine.Val providerFn.port) :
    Tuple machine.Val imports :=
  .cons target (.cons ((allocated shifted cap).get .head) (one 2))

private def analyzeRelocated (shifted : Bool) (cap : Nat) (target : machine.Val providerFn.port) :
    Option (ExportAnalysis actions (clientLayout shifted).binding.summary
      (Executable.link actions 84 (clientLayout shifted).numbered.toGraph (relocatedEntry shifted cap target)
        (providerSound shifted cap).store)
      (Executable.link actions 84 (clientLayout shifted).numbered.toGraph (relocatedEntry shifted cap target)
        (providerSound shifted cap).store)) := by
  cases shifted
  · exact (clientLayout false).analyzeImported (providerSound false cap) exact 84
      (relocatedEntry false cap target) (relocatedEntry false cap target)
      (fun same _ _ _ => ⟨⟨same, rfl⟩, fun _ _ => trivial⟩)
      (fun same _ _ _ => ⟨⟨same, rfl⟩, fun _ _ => trivial⟩)
  · exact (clientLayout true).analyzeImported (providerSound true cap) exact 84
      (relocatedEntry true cap target) (relocatedEntry true cap target)
      (fun same _ _ _ => ⟨⟨same, rfl⟩, fun _ _ => trivial⟩)
      (fun same _ _ _ => ⟨⟨same, rfl⟩, fun _ _ => trivial⟩)

private def relocateIds : GlobalRel := fun left right => right = (left.1, left.2 + 1)

private def relocatedProviderPlan :
    GraphPlan (providerLayout false).numbered.toGraph (providerLayout true).numbered.toGraph :=
  .skipL (.skipR (.skipR (.start (.lambda .done))))

private def relocatedProviderCheck (cap : Nat) :=
  checkGraphProvider keys actions relocateIds ordinary 83 83 (one cap) (one cap)
    (providerLayout false).numbered.toGraph (providerLayout true).numbered.toGraph
    relocatedProviderPlan (providerFn := providerFn) .head 20 20

private def pairedAdmission (cap : Nat) (targetR : machine.Val providerFn.port) :=
  match relocatedProviderCheck cap with
  | none => false
  | some provider =>
    (admitAllocatingClient actions ordinary exact provider 84 84
      (relocatedEntry false cap (providerSound false cap).targetL) (relocatedEntry true cap targetR)
      (clientLayout false).numbered (clientLayout true).numbered).isSome

#guard pairedAdmission 3 (providerSound true 3).targetL
#guard pairedAdmission 0 (providerSound true 0).targetL
-- Same signature, code, unit and payload, but the old allocation vertex.
#guard !(pairedAdmission 3 (providerSound false 3).targetL)
#guard (analyzeRelocated true 3 (providerSound false 3).targetL).isNone

private def relocatedResult (shifted : Bool) (cap : Nat) :=
  analyzeRelocated shifted cap (providerSound shifted cap).targetL

#guard [false, true].all fun shifted => (relocatedResult shifted 3).any fun checked =>
  checked.linked.store == 33 &&
  checked.liveCapture emptyDemand (.tail .head) &&
  checked.liveCapture emptyDemand (.tail (.tail .head)) &&
  checked.liveFormal requested .head &&
  !checked.liveFormal requested (.tail .head) &&
  (match checked.linked.capsL.get (.tail (.tail .head)) with
    | .global unitId vertex (.data n) =>
      let n : Nat := n
      unitId == 84 && vertex == (if shifted then 1 else 0) && n == 4)

private def relocatedRun (shifted : Bool) (cap : Nat) (values : Tuple machine.Val pair) :=
  let source := providerSound shifted cap
  Executable.run actions 60 84 (clientLayout shifted).numbered.toGraph
    (relocatedEntry shifted cap source.targetL) .head values source.store

private def relocatedLink (shifted : Bool) (cap : Nat) :=
  let source := providerSound shifted cap
  Executable.link actions 84 (clientLayout shifted).numbered.toGraph
    (relocatedEntry shifted cap source.targetL) source.store

private theorem providerRelated (cap : Nat) :
    ValueRelated machine relocateIds (providerSound false cap).targetL (providerSound true cap).targetL :=
  .closure (.cons (.global rfl (.data _)) .nil) (NestedTheta.Graph.Isomorphic.refl _)

private theorem relocatedLinksRelated (cap : Nat) :
    OutcomesRelated machine relocateIds Nat (· + 1) [clientFn.port]
      (relocatedLink false cap) (relocatedLink true cap) :=
  .linked (.cons (.closure (.cons (providerRelated cap)
    (.cons (.global rfl (.data _)) (.cons (.global rfl (.data _)) .nil)))
      (NestedTheta.Graph.Isomorphic.refl _)) .nil) (20 + cap + 4 + 2 + 4)

private theorem argumentsRelated (spare : Nat) : TupleRelated machine relocateIds (args spare) (args spare) :=
  .cons (ValueRelated.data (m := machine) (ids := relocateIds) (t := ()) (41 : Nat))
    (.cons (ValueRelated.data (m := machine) (ids := relocateIds) (t := ()) spare) .nil)

example (cap : Nat)
    (left : ExportAnalysis actions clientBinding.summary (relocatedLink false cap) (relocatedLink false cap))
    (right : ExportAnalysis actions clientBinding.summary (relocatedLink true cap) (relocatedLink true cap))
    (admitted : AdmittedExport actions.toPrimitives relocateIds (fn := clientFn) .head
      (relocatedLink false cap) (relocatedLink true cap)) :=
  left.relocated_substituted_starts right (relocatedLinksRelated cap) admitted requested
    (argumentsRelated 4) (argumentsRelated 40) rfl

private def relocatedBlock (shifted : Bool) (values : Tuple machine.Val pair) :
    Option (Nat × Nat × Nat × Nat) :=
  match relocatedRun shifted 0 values with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, .cons (.global unitId vertex (.data n)) .nil⟩, _⟩ store) =>
    some (unitId, vertex, n, store)
  | _ => none

private def relocatedResume (shifted : Bool) (values : Tuple machine.Val pair) :=
  match relocatedRun shifted 0 values with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, _⟩, stack⟩ _) =>
    returned (observe actions (runFor actions 60 ⟨.returned .nil stack, 50⟩))
  | _ => none

private def relocatedReplacement (shifted : Bool) (cap : Nat) :=
  (relocatedResult shifted cap).map fun checked => checked.substituteDeadFormals requested (args 4) (args 40)

#guard [false, true].all fun shifted =>
  let attempt := some (83, if shifted then 1 else 0, 0, 30)
  let success := some (41, 43)
  let resumed := some (41, 54)
  (relocatedReplacement shifted 3).map (fun values => match values.get (.tail .head) with
    | .data n => n) == some (40 : Nat) &&
  (relocatedRun shifted 3 (args 4)).toOption.bind returned == success &&
  (relocatedReplacement shifted 3).bind (fun values => (relocatedRun shifted 3 values).toOption.bind returned) == success &&
  relocatedBlock shifted (args 4) == attempt &&
  (relocatedReplacement shifted 0).bind (relocatedBlock shifted) == attempt &&
  relocatedResume shifted (args 4) == resumed &&
  (relocatedReplacement shifted 0).bind (relocatedResume shifted) == resumed

section NamedProviders

open Isomorphism.RecursiveCall.Numbered.Prefix (CheckedProviderAssembly)

private def secondBinding : Binding Op (Scope.ordinary machine).table single [[global]] providerFn where
  context := [global]
  captures := .cons (.output (0 : Fin 1) .head) .nil
  sigs := [[], single]
  body := .primitive .probe (.cons (.arg .head) .nil)
    (.primitive .allocate (.cons (.arg (.tail .head)) .nil)
      (.ret (.cons (.output (1 : Fin 2) .head) .nil)))

private def secondLayout : AllocationPlan Op (Scope.ordinary machine).table single providerFn (.data ()) false :=
  ⟨providerDelta, secondBinding⟩

private def secondRight (shifted : Bool) : secondLayout.Layout shifted where
  init := ⟨single, .cons (.arg .head) .nil, [single], initializer⟩
  captures := .cons (by
    cases shifted
    · exact .output (0 : Fin 1) .head
    · exact .output (1 : Fin 2) .head) .nil

private def namedIds (shifted : Bool) : GlobalRel :=
  fun left right => right = (left.1, if shifted && left.1 != 83 then left.2 + 1 else left.2)

private def secondPlan (shifted : Bool) :
    GraphPlan secondLayout.numbered.toGraph (secondLayout.withLayout (secondRight shifted)).numbered.toGraph :=
  match shifted with
  | false => .skipL (.skipR (.start (.lambda .done)))
  | true => .skipL (.skipR (.skipR (.start (.lambda .done))))

private def secondChecked (cap : Nat) (shifted : Bool) :=
  checkGraphProvider keys actions (namedIds shifted) ordinary 84 84 (one cap) (one cap)
    secondLayout.numbered.toGraph (secondLayout.withLayout (secondRight shifted)).numbered.toGraph
    (secondPlan shifted) (providerFn := providerFn) .head 27 27

private def secondInitialized (cap : Nat) (shifted : Bool) :
    LinkedRows (secondLayout.linkDelta actions 84 (one cap) 27)
      ((secondLayout.withLayout (secondRight shifted)).linkDelta actions 84 (one cap) 27) :=
  ⟨.cons (.global 84 0 (.data (2 * cap))) .nil,
    .cons (.global 84 (if shifted then 1 else 0) (.data (2 * cap))) .nil,
    27 + cap + 4, rfl, by cases shifted <;> rfl⟩

private def secondSound (cap : Nat) (shifted : Bool) :=
  ((secondLayout.analyzeLayouts (secondRight shifted) (Scope.Checked.ordinary actions).state.dispatch
    84 84 (one cap) (one cap) 27 (secondInitialized cap shifted) (fun _ => none) (fun _ => none)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)).get (by cases shifted <;> rfl)).linked

private def namedAssembly (cap : Nat) (shifted : Bool) := do
  let first ← checkGraphProvider keys actions (namedIds shifted) ordinary 83 83 (one 3) (one 3)
    providerGraph providerGraph alignment (providerFn := providerFn) .head 20 20
  let second ← secondChecked cap shifted
  (CheckedProviderAssembly.start "add-first" first.allocationChain).append
    "scale-second" second.allocationChain ordinary

private abbrev namedPorts : Ports T := [providerFn.port, providerFn.port]
private abbrev namedExtra : Ports T := [global, global, num]
private abbrev namedCaptures : Ports T := namedPorts ++ [global, global, global]
private abbrev namedEntry := namedCaptures ++ clientFn.args
private abbrev namedFirstSlots := prepend providerBinding.summary (Scope.ordinary machine).table
private abbrev secondSlots := prepend secondBinding.summary (Scope.ordinary machine).table
private abbrev namedSlots := append namedFirstSlots (append secondSlots (Scope.ordinary machine).table)

private def namedLayout : AllocationPlan Op namedSlots (namedPorts ++ namedExtra) clientFn (.data ()) false where
  init := ⟨single, .cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil, [single], initializer⟩
  binding :=
    { context := namedCaptures
      captures := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head)))
        (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.output (0 : Fin 1) .head) .nil))))
      sigs := [single, single, []]
      body := .familyCall (table := namedSlots) (0 : Fin 2) .head
        (.cons (.arg (.tail (.tail .head))) .nil)
        (.cons (.arg (.tail (.tail (.tail (.tail (.tail .head)))))) .nil)
        (.familyCall (table := namedSlots) (1 : Fin 2) (.tail .head)
          (.cons (.arg (.tail (.tail (.tail .head)))) .nil)
          (.cons (.output (0 : Fin 1) .head) .nil)
          (.primitive .probe (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil)
            (.ret (.cons (.output (1 : Fin 3) .head) .nil)))) }

private def namedRight (shifted : Bool) (wrongTarget : Bool := false) : namedLayout.Layout shifted where
  init := ⟨single, .cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil, [single], initializer⟩
  captures := .cons (.arg (if wrongTarget then .tail .head else .head))
    (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head)))
    (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (by
      cases shifted
      · exact .output (0 : Fin 1) .head
      · exact .output (1 : Fin 2) .head) .nil))))

private def clientImports (targetA targetB : machine.Val providerFn.port)
    (witnessA witnessB : machine.Val global) : Tuple machine.Val (namedPorts ++ namedExtra) :=
  .cons targetA (.cons targetB (.cons witnessA (.cons witnessB (one 2))))

private def namedArgs (spare : Nat) : Tuple machine.Val pair := .cons (.data (7 : Nat)) (one spare)

private def namedRun (cap vertexR : Nat) (store : Nat) (target : machine.Val clientFn.port)
    (formals : Tuple machine.Val pair) : Bool :=
  let observation := Continuation.Partial.Executable.run actions 60 (.call target formals) store
  if cap == 0 then
    match observation with
    | .blocked ⟨⟨_, _, .probe, _, _, .cons (.global unitId vertex (.data payload)) .nil⟩, stack⟩ attempted =>
      let payload : Nat := payload
      unitId == 84 && vertex == vertexR && payload == 0 && attempted == 43 &&
        returned (observe actions (runFor actions 60 ⟨.returned .nil stack, 50⟩)) == some (14, 65)
    | _ => false
  else
    returned observation == some (14, 73)

private def checkNamed (cap : Nat) (swapRight shifted staleRight wrongTarget : Bool := false) : Option Bool := do
  let rightLayout := namedRight shifted wrongTarget
  let right := namedLayout.withLayout rightLayout
  -- The outer capture wires move while the numbered λ body keeps its row map.
  let _ ← NestedTheta.Isomorphism.check keys (fun _ => ⟨id, id⟩)
    namedLayout.numbered.body.body right.numbered.body.body
  let assembly ← namedAssembly cap shifted
  let first ← assembly.lookup "add-first" providerFn.port
  let second ← assembly.lookup "scale-second" providerFn.port
  let firstProof ← matchNamedExport first (providerSound false 3) exact
  let secondProof ← matchNamedExport second (secondSound cap shifted) exact
  let sourceA : NamedDemand assembly providerBinding.summary :=
    ⟨"add-first", first, (providerSound false 3).relink firstProof.down.1 firstProof.down.2⟩
  let sourceB : NamedDemand assembly secondBinding.summary :=
    ⟨"scale-second", second, (secondSound cap shifted).relink secondProof.down.1 secondProof.down.2⟩
  let sources : NamedImports assembly namedPorts := .cons sourceA (.cons sourceB .nil)
  let importsL := clientImports first.values.left second.values.left
    (sourceA.sound.capsL.get .head) (sourceB.sound.capsL.get .head)
  let targetAR := if swapRight then second.values.right else first.values.right
  let targetBR := if swapRight then first.values.right
    else if staleRight then (secondSound cap false).targetR else second.values.right
  let importsR := clientImports targetAR targetBR
    (sourceA.sound.capsR.get .head) (sourceB.sound.capsR.get .head)
  let initial := assembly.chain.checked.storeL
  let receipt ← LinkedRows.check
    (namedLayout.linkDelta actions 85 importsL initial)
    (right.linkDelta actions 85 importsR initial)
  if common : assembly.chain.checked.storeR = initial then
    let checked ← sources.analyzeLayoutsDirect namedLayout rightLayout exact 85 85
      importsL importsR initial rfl common receipt
    let original := namedArgs 4
    let vertexR := if shifted then 1 else 0
    let substituted := checked.substituteDeadFormals requested original (namedArgs 40)
    let spare : Nat := match substituted.get (.tail .head) with | .data n => n
    have _traceL := Isomorphism.RecursiveCall.Numbered.Prefix.AllocationHistory.link sourceA.historyL checked.linked.linkedL
    have _traceR := Isomorphism.RecursiveCall.Numbered.Prefix.AllocationHistory.link sourceB.historyR checked.linked.linkedR
    pure (sourceA.sound.store == 27 && sourceB.sound.store == (27 + cap + 4) &&
      checked.liveCapture emptyDemand (.tail (.tail .head)) &&
      checked.liveCapture emptyDemand (.tail (.tail (.tail .head))) &&
      checked.liveFormal requested .head && !checked.liveFormal requested (.tail .head) && spare == 40 &&
      namedRun cap 0 checked.linked.store checked.linked.targetL original &&
      namedRun cap 0 checked.linked.store checked.linked.targetL substituted &&
      namedRun cap vertexR checked.linked.store checked.linked.targetR original &&
      namedRun cap vertexR checked.linked.store checked.linked.targetR substituted &&
      (match checked.linked.capsR.get (.tail (.tail (.tail (.tail .head)))) with
        | .global unitId vertex (.data n) =>
          let n : Nat := n
          unitId == 85 && vertex == vertexR && n == 4))
  else none

#guard checkNamed 5 == some true
#guard checkNamed 0 == some true
#guard (checkNamed 5 true).isNone
#guard checkNamed 5 (shifted := true) == some true
#guard checkNamed 0 (shifted := true) == some true
-- Both names resolve correctly, but the first call wire reads the second provider.
#guard (checkNamed 5 (shifted := true) (wrongTarget := true)).isNone
-- Same provider body and payload, with the capture still at vertex 0.
#guard (checkNamed 5 (shifted := true) (staleRight := true)).isNone

private def namedLinked (cap : Nat) (shifted : Bool) :=
  let first := providerSound false 3
  let second := secondSound cap true
  let inputs := if shifted then
    clientImports first.targetR second.targetR (first.capsR.get .head) (second.capsR.get .head)
    else clientImports first.targetL second.targetL (first.capsL.get .head) (second.capsL.get .head)
  Executable.link actions 85 (namedLayout.withLayout (namedRight shifted)).numbered.toGraph inputs second.store

private theorem namedLinkedRelated (cap : Nat) :
    OutcomesRelated machine (namedIds true) Nat (· + 1) [clientFn.port]
      (namedLinked cap false) (namedLinked cap true) := by
  let first := providerSound false 3
  let second := secondSound cap true
  have firstRelated : ValueRelated machine (namedIds true) first.targetL first.targetR :=
    .closure (.cons (.global rfl (.data _)) .nil) (NestedTheta.Graph.Isomorphic.refl _)
  have secondRelated : ValueRelated machine (namedIds true) second.targetL second.targetR :=
    .closure (.cons (.global rfl (.data _)) .nil) (NestedTheta.Graph.Isomorphic.refl _)
  exact .linked (.cons (.closure (.cons firstRelated (.cons secondRelated
    (.cons (.global rfl (.data _)) (.cons (.global rfl (.data _)) (.cons (.global rfl (.data _)) .nil)))))
    (NestedTheta.Graph.Isomorphic.refl _)) .nil) (27 + cap + 4 + 2 + 4)

private theorem namedArgsRelated (spare : Nat) :
    TupleRelated machine (namedIds true) (namedArgs spare) (namedArgs spare) :=
  .cons (ValueRelated.data (m := machine) (ids := namedIds true) (t := ()) (7 : Nat))
    (.cons (ValueRelated.data (m := machine) (ids := namedIds true) (t := ()) spare) .nil)

example (cap : Nat)
    (analysis : ExportAnalysis actions namedLayout.binding.summary (namedLinked cap false) (namedLinked cap true))
    (admitted : AdmittedExport actions.toPrimitives (namedIds true) (fn := clientFn) .head
      (namedLinked cap false) (namedLinked cap true)) :=
  analysis.relocated_substituted_starts analysis (namedLinkedRelated cap) admitted requested
    (namedArgsRelated 4) (namedArgsRelated 40) rfl

end NamedProviders

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.ProviderRegression

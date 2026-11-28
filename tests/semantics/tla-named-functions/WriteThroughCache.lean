module

import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source.Defs
import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source.Thms
meta import Lean

open Silmaril.Logic.Temporal.TLA Resolution DataElab NamedFunctions.Source

private def fromResult {α ε : Type} [Repr ε] : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def standardImports : ImportMap :=
  [("Naturals", Sequences.naturalsId), ("Sequences", Sequences.sequencesId)]

private def sourceId (name : String) : ModuleId := "tlaplus/" ++ Sequences.revision ++ "/" ++ name
private def root : ModuleId := sourceId "WriteThroughCache"
private def memoryImports : ImportMap := [("MemoryInterface", sourceId "MemoryInterface")]
private def instanceImports : ImportMap :=
  [("InternalMemory", sourceId "InternalMemory"), ("Memory", sourceId "Memory")]

private def checkProjection (unit : Surface.ModuleUnit) : IO Unit := do
  let root := "WriteThroughCache.vmem projection"
  let projected : Surface.Module := ⟨"WriteThroughCache", ["Naturals", "Sequences"],
    [.variables ["wmem", "memQ"], unit]⟩
  let checked ← fromResult (check projected root standardImports 32 (.ident "vmem"))
  let p := checked.predecessor
  let home : Site := ⟨root, [.unit 1, .body, .letDecl 0]⟩
  unless p.site == home && p.binder == .declared (home.child (.bound 0) |>.child (.binder 0)) &&
      p.base == .declared ⟨root, [.unit 0, .member 0]⟩ &&
      p.queue == .declared ⟨root, [.unit 0, .member 1]⟩ do
    throw (IO.userError s!"unexpected predecessor certificate: {reprStr p}")
  IO.println "WriteThroughCache.vmem projection: certified CHOOSE regression passed"

private def parse (dir : System.FilePath) (name : String) : IO Surface.Module := do
  let source ← fromResult (Surface.Parser.parseModule (← IO.FS.readFile (dir / (name ++ ".tla"))))
  unless source.name == name do throw (IO.userError s!"unexpected module header for {name}")
  return source

private def moduleAt (registry : CheckedRegistry) (id : ModuleId) : IO CheckedModule :=
  (registry.moduleAt id).getDM (throw (IO.userError s!"missing checked module {id}"))

private def requireReference (checked : CheckedModule) (path : Path) (id : BindingId) : IO Unit := do
  unless (checked.referenceAt path).map (·.target) == some id do
    throw (IO.userError s!"{checked.name} reference {reprStr path}: expected {reprStr id}")

private def expectResolutionError (result : Except Resolution.Diagnostic CheckedRegistry)
    (site : Site) (kind : Resolution.DiagnosticKind) : IO Unit := do
  let .error actual := result | throw (IO.userError s!"expected rejection at {reprStr site}")
  unless actual.site == site && actual.kind == kind do
    throw (IO.userError s!"expected {reprStr kind} at {reprStr site}, got {reprStr actual}")

private def checkIntact (dir : System.FilePath) (source : Surface.Module) (index : Nat) :
    IO Unit := do
  let naturals ← parse dir "Naturals"
  let sequences ← parse dir "Sequences"
  let interface ← parse dir "MemoryInterface"
  let internal ← parse dir "InternalMemory"
  let memory ← parse dir "Memory"
  let memoryInput := (sourceId "MemoryInterface", ModuleInput.parsed interface [])
  let imports := standardImports ++ memoryImports ++ instanceImports
  let rootInput := (root, ModuleInput.parsed source imports)
  let graph : Registry := [rootInput, memoryInput,
    (Sequences.naturalsId, .parsed naturals []),
    (Sequences.sequencesId, .parsed sequences [("Naturals", Sequences.naturalsId)]),
    (sourceId "InternalMemory", .parsed internal memoryImports),
    (sourceId "Memory", .parsed memory (memoryImports ++ instanceImports))]
  let profile := Profile.namedFunctionInstanceSyntax
  let registry ← fromResult (resolveOperatorWith profile graph root index)
  let checked ← moduleAt registry root
  let nat ← moduleAt registry Sequences.naturalsId
  let seq ← moduleAt registry Sequences.sequencesId
  let mem ← moduleAt registry (sourceId "MemoryInterface")
  unless checked.selectedUnit == some index &&
      checked.imports == [Sequences.naturalsId, Sequences.sequencesId, sourceId "MemoryInterface"] &&
      registry.modules.map Prod.fst == checked.imports ++ [root] &&
      (checked.bindingAt (.ident "vmem")).map (·.id) == some (.declared ⟨root, [.unit index]⟩) do
    throw (IO.userError "unexpected selected source scope or EXTENDS identities")
  for (id, _, operators) in Sequences.modules do
    let standard ← moduleAt registry id
    for (name, op) in operators do
      let some binding := standard.bindingAt name
        | throw (IO.userError s!"missing operator {reprStr name} in {standard.name}")
      unless binding.kind == .operator && binding.slots == List.replicate op.arity .expression &&
          !binding.isLocal && (checked.bindingAt name).map (·.id) == some binding.id do
        throw (IO.userError s!"wrong import origin or signature for {reprStr name}")
  let natural (unit : Nat) : BindingId := .declared ⟨Sequences.naturalsId, [.unit unit]⟩
  let seqLen : BindingId := .declared ⟨Sequences.sequencesId, [.unit 2]⟩
  let letPath : Path := [.unit index, .body, .letDecl 0]
  let domain := letPath ++ [.bound 0, .domain]
  requireReference checked domain (natural 11)
  requireReference checked (domain ++ [.operand 1]) seqLen
  requireReference checked (letPath ++ [.body, .operand 2, .operand 1, .operand 1]) (natural 2)
  requireReference checked (letPath ++ [.body, .operand 2, .operand 2, .operand 0, .operand 1])
    (natural 2)
  requireReference checked [.unit index, .body, .body, .operand 1] seqLen
  let some plan := seq.instanceAt [.unit 0]
    | throw (IO.userError "missing Sequences LOCAL INSTANCE Naturals")
  let range := Name.symbol .infix ".."
  unless plan.site == ⟨Sequences.sequencesId, [.unit 0]⟩ &&
      plan.target == Sequences.naturalsId && plan.parameters.isEmpty &&
      plan.substitutions.isEmpty && plan.members.isEmpty &&
      (seq.bindingAt range).any (fun b => b.id == natural 11 && b.isLocal) &&
      (nat.bindingAt range).any (fun b => b.id == natural 11 && !b.isLocal) do
    throw (IO.userError "Sequences must reuse the local Naturals identities")
  requireReference seq [.unit 2, .body, .domain] (natural 0)
  requireReference seq [.unit 2, .body, .body, .operand 1] (natural 11)
  for (name, path, kind, arity) in
      [("memInt", [.unit 0, .member 0], BindingKind.variable, 0),
       ("Send", [.unit 1, .member 0], .constant, 4), ("Reply", [.unit 1, .member 1], .constant, 4),
       ("InitMemInt", [.unit 1, .member 2], .constant, 0),
       ("Proc", [.unit 1, .member 3], .constant, 0), ("Adr", [.unit 1, .member 4], .constant, 0),
       ("Val", [.unit 1, .member 5], .constant, 0), ("MReq", [.unit 2], .operator, 0),
       ("NoVal", [.unit 3], .operator, 0)] do
    let id := BindingId.declared ⟨sourceId "MemoryInterface", path⟩
    unless (mem.bindingAt (.ident name)).any (fun b =>
        b.id == id && b.kind == kind && b.slots == List.replicate arity .expression) &&
        (checked.bindingAt (.ident name)).map (·.id) == some id do
      throw (IO.userError s!"wrong MemoryInterface origin for {name}")
  expectResolutionError (resolveWith profile graph root)
    ⟨root, [.unit 2]⟩ (.unsupported .assumption)
  let internalRegistry ← fromResult (resolveWith profile graph (sourceId "InternalMemory"))
  let checkedInternal ← moduleAt internalRegistry (sourceId "InternalMemory")
  unless checkedInternal.imports == [sourceId "MemoryInterface"] &&
      (checkedInternal.bindingAt (.ident "ISpec")).map (·.id) ==
        some (.declared ⟨sourceId "InternalMemory", [.unit 7]⟩) do
    throw (IO.userError "unexpected InternalMemory declarations")
  expectResolutionError (resolveWith profile graph (sourceId "Memory"))
    ⟨sourceId "Memory", [.unit 0]⟩ (.unsupported .instanceTheorem)
  let some (.definition (.namedInstance .ordinary "M" [] ⟨"InternalMemory",
      [⟨.ident "mem", .expr (.ref (.operator (.ident "wmem")) [] [])⟩]⟩)) := source.units[3]?
    | throw (IO.userError "unexpected M INSTANCE edge")
  let some (.definition (.namedInstance .ordinary "LM" [] ⟨"Memory", []⟩)) := source.units[19]?
    | throw (IO.userError "unexpected LM INSTANCE edge")
  let .error ⟨site, .unknownName (.qualified ["M"] (.ident "IInit"))⟩ :=
      resolveOperatorWith profile graph root 4
    | throw (IO.userError "expected Init selection to reject the unchecked M!IInit reference")
  unless site.moduleId == root && site.path.take 2 == [.unit 4, .body] do
    throw (IO.userError s!"wrong Init reference location: {reprStr site}")
  IO.println "WriteThroughCache: intact imports and vmem reference origins checked"
  IO.println "Full resolution stops at QLen ASSUME. M targets theorem-bearing InternalMemory; LM targets Memory, whose Inner edge is rejected there."

  -- Use the interpreted signatures for lowering. The parsed standard modules above
  -- establish declaration origin and arity. Their bodies provide no interpretation.
  let selected ← fromResult (checkSelected [rootInput, memoryInput] root index 32)
  let p := selected.predecessor
  let home : Site := ⟨root, letPath⟩
  unless p.site == home && p.binder == .declared (home.child (.bound 0) |>.child (.binder 0)) &&
      p.base == .declared ⟨root, [.unit 0, .member 0]⟩ &&
      p.queue == .declared ⟨root, [.unit 0, .member 4]⟩ do
    throw (IO.userError s!"unexpected intact predecessor certificate: {reprStr p}")
  IO.println "WriteThroughCache.vmem: original unit selected, state levels checked and certified as CHOOSE"

private def term (range index : String) : String :=
  s!"LET fold[k \\in {range}] ==
      IF k = 0 THEN wmem
      ELSE IF memQ[k][2].op = \"Rd\" THEN fold[{index}]
      ELSE [fold[{index}] EXCEPT ![memQ[k][2].adr] = memQ[k][2].val]
    IN fold[Len(memQ)]"

private def fixture (expression : String) (standard : String := "Naturals, Sequences")
    (extra : String := "") : IO Surface.Module := do
  let extendsLine := if standard.isEmpty then "" else s!"EXTENDS {standard}\n"
  fromResult (Surface.Parser.parseModule
    s!"---- MODULE Fixture ----\n{extendsLine}VARIABLES wmem, memQ\n{extra}\nvmem == {expression}\n====")

private def controls : IO Unit := do
  let range := "0 .. Len(memQ)"
  let checkText := fun source => check source "fixture" standardImports 32 (.ident "vmem")
  discard <| fromResult (checkText (← fixture (term range "k-1")))
  for wrongIndex in ["k-0", "k < 1"] do
    match checkText (← fixture (term range wrongIndex)) with
    | .error (.unsupportedPredecessor _) => pure ()
    | other => throw (IO.userError s!"expected to reject predecessor index {wrongIndex}: {other.isOk}")
  let rogue ← fixture (term range "k-1") "Sequences" "a-b == a\na..b == {a,b}"
  match check rogue "fixture" [("Sequences", Sequences.sequencesId)] 32 (.ident "vmem") with
  | .error (.unsupportedPredecessor _) => pure ()
  | .error other => throw (IO.userError s!"expected predecessor diagnostic, got {reprStr other}")
  | .ok _ => throw (IO.userError "expected to reject same-spelled local operators")
  for (expression, name) in [(term "fold" "k-1", "fold"), ("LET fold[k \\in {0}] == k IN k", "k")] do
    match checkText (← fixture expression) with
    | .error (.resolution ⟨_, .unknownName (.ident missing)⟩) =>
      unless missing == name do throw (IO.userError s!"expected an unresolved {name}, got {missing}")
    | _ => throw (IO.userError s!"expected {name} to be out of scope")
  IO.println "WriteThroughCache.vmem controls: alpha-renaming, resolved subtraction, strict predecessor and lexical scope"

private def selectionControls : IO Unit := do
  let fixtureRoot := "fixture"
  let inputs (source : Surface.Module) : Registry := [(fixtureRoot, .parsed source [])]
  let source ← fixture "Earlier" "" "Earlier == 0"
  let selected ← fromResult (resolveOperatorWith .namedFunctionSyntax (inputs source) fixtureRoot 2)
  let .error ⟨site, .missingSummary target⟩ := Levels.checkSelectedOperator selected
    | throw (IO.userError "selected levels should reject a skipped operator body")
  unless site == ⟨fixtureRoot, [.unit 2, .body]⟩ &&
      target == .declared ⟨fixtureRoot, [.unit 1]⟩ && !(Levels.check selected).isOk do
    throw (IO.userError "selection must preserve the skipped declaration but withhold its summary")
  let duplicate ← fixture "0" "" "vmem == 0"
  expectResolutionError (resolveOperatorWith .namedFunctionSyntax (inputs duplicate) fixtureRoot 2)
    ⟨fixtureRoot, [.unit 2]⟩ (.conflictingName (.ident "vmem") (.declared ⟨fixtureRoot, [.unit 1]⟩))
  let anonymous ← fixture "0" "" "INSTANCE Other"
  expectResolutionError (resolveOperatorWith .namedFunctionInstanceSyntax (inputs anonymous) fixtureRoot 2)
    ⟨fixtureRoot, [.unit 1]⟩ (.unsupported .selectionScope)
  IO.println "Operator selection controls: skipped body, duplicate name and unknown import scope rejected"

open Lean in
run_cmd do
  let declarations := [``predecessor_key, ``CheckedVMem.eval_eq_choose_apply_len,
    ``CheckedVMem.eval_eq_vmem, ``NamedFunctions.Definition.existsUnique_fixedPoint,
    ``NamedFunctions.vmem_eq_choose_apply_len]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in declarations do
    let axioms ← collectAxioms name
    unless axioms.all (· ∈ allowed) do
      throwError "unexpected axioms for {name}: {axioms}"
  logInfo m!"Axiom audit passed for {declarations.length} predecessor and CHOOSE theorems"

public def main (args : List String) : IO Unit := do
  let [dir, revision] := args | throw (IO.userError "expected the pinned TLA+ source directory and revision")
  unless revision == Sequences.revision do
    throw (IO.userError "pinned source revision differs from the standard interpretation")
  let source ← parse dir "WriteThroughCache"
  let [(unit, index)] := source.units.zipIdx.filter (fun
    | (.definition (.operator .ordinary (.ident "vmem" []) _), _) => true
    | _ => false)
    | throw (IO.userError "expected exactly one vmem definition")
  unless index == 12 do throw (IO.userError "unexpected vmem unit index")
  checkIntact dir source index
  checkProjection unit
  controls
  selectionControls

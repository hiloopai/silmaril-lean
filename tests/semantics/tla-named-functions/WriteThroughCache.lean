module

import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.NamedFunctions.Source.Defs

open Silmaril.Logic.Temporal.TLA Resolution DataElab NamedFunctions.Source

private def fromResult {α ε : Type} [Repr ε] : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def imports : ImportMap :=
  [("Naturals", Sequences.naturalsId), ("Sequences", Sequences.sequencesId)]

private def root : ModuleId := "WriteThroughCache.vmem projection"

private def checkProjection (unit : Surface.ModuleUnit) : IO Unit := do
  let projected : Surface.Module := ⟨"WriteThroughCache", ["Naturals", "Sequences"],
    [.variables ["wmem", "memQ"], unit]⟩
  let checked ← fromResult (check projected root imports 32 (.ident "vmem"))
  let p := checked.predecessor
  let home : Site := ⟨root, [.unit 1, .body, .letDecl 0]⟩
  unless p.site == home && p.binder == .declared (home.child (.bound 0) |>.child (.binder 0)) &&
      p.base == .declared ⟨root, [.unit 0, .member 0]⟩ &&
      p.queue == .declared ⟨root, [.unit 0, .member 1]⟩ do
    throw (IO.userError s!"unexpected predecessor certificate: {reprStr p}")
  IO.println "WriteThroughCache.vmem: original LET resolved, level checked and lowered to certified CHOOSE"

private def term (range index : String) : String :=
  s!"LET fold[k \\in {range}] ==
      IF k = 0 THEN wmem
      ELSE IF memQ[k][2].op = \"Rd\" THEN fold[{index}]
      ELSE [fold[{index}] EXCEPT ![memQ[k][2].adr] = memQ[k][2].val]
    IN fold[Len(memQ)]"

private def fixture (expression : String) (standard : String := "Naturals, Sequences")
    (extra : String := "") : IO Surface.Module :=
  fromResult (Surface.Parser.parseModule
    s!"---- MODULE Fixture ----\nEXTENDS {standard}\nVARIABLES wmem, memQ\n{extra}\nvmem == {expression}\n====")

private def controls : IO Unit := do
  let range := "0 .. Len(memQ)"
  let checkText := fun source => check source "fixture" imports 32 (.ident "vmem")
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

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the pinned WriteThroughCache.tla path")
  let source ← fromResult (Surface.Parser.parseModule (← IO.FS.readFile path))
  unless source.name == "WriteThroughCache" &&
      source.extendsModules == ["Naturals", "Sequences", "MemoryInterface"] do
    throw (IO.userError "unexpected module or imports")
  let [unit] := source.units.filter (fun
    | .definition (.operator .ordinary (.ident "vmem" []) _) => true
    | _ => false)
    | throw (IO.userError "expected exactly one vmem definition")
  checkProjection unit
  controls

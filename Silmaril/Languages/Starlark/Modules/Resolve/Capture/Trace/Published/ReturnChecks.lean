module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Thms
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
meta import Silmaril.Languages.Starlark.Modules.Loader.Defs
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open scoped Functions.Lowering.Quote
open Defaults
open Defaults.Nested.Sequence.Recursive (Site)
open Defaults.Nested.Sequence.Recursive.Call.Named (Mapping)
open Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance (Entry)
open Functions (Program)

private def globals : List String := ["data", "factory", "escaped", "late", "alias", "result", "after"]
private def int (n : Int) : Functions.Lowering.Expr := .atom (.scalar (.int n))
private def boxed (n : Int) : Functions.Lowering.Expr := .list [int n]
private def localRead (name : String) : Functions.Lowering.Expr := Leaf.readOperand (fileSlot name)
private def globalRead (name : String) : Functions.Lowering.Expr := Leaf.readOperand (globalSlot name)

private def factoryBlock : Assignment.LexicalBlock := ⟨["value", "child", "copy"], [], globals⟩
private def childKeywords : List PlainKeywordParameter :=
  [.defaulted ⟨"key", starlark%[value], localRead "value", [fileSlot "value"]⟩]

private def childBody : Body.Suite :=
  .assign "marked" starlark%[[44]] (.assign "probe" starlark%[key[0]]
    (.assign "seen" starlark%[value[0]] (.ret starlark%[late])))

private def child : Site factoryBlock childKeywords (some "rest") (some "extras") where
  name := "child"
  target := by decide
  parameters := ⟨["first"], []⟩
  source := childBody.source
  binders := ["marked", "probe", "seen"]
  locals := ["marked", "probe", "seen"]
  collects := .seq (.assign _ _) (.seq (.assign _ _) (.seq (.assign _ _) (.ret _)))
  localOrder := .keep (by decide) (.keep (by decide) (.keep (by decide) .nil))
  body := ⟨.seq (.assignExpr (fileSlot "marked") (boxed 44))
    (.seq (.assignExpr (fileSlot "probe") (.index (localRead "key") (int 0)))
      (.seq (.assignExpr (fileSlot "seen") (.index (localRead "value") (int 0)))
        (.returnExpr (globalRead "late")))), [fileSlot "key", fileSlot "value", globalSlot "late"]⟩
  free := [⟨fileSlot "value", fileSlot "value"⟩, ⟨globalSlot "late", globalSlot "late"⟩]
  selects := .owned (.owned (by decide))
    (.enclosing (.enclosing (by decide) (by decide)) (.module (.module (by decide) (by decide) (by decide)) .nil))
  defaults := []
  lexical := .nil

private def returned : Entry factoryBlock := ⟨0, childKeywords, some "rest", some "extras", child⟩

private def factoryTail : Statement :=
  .seq (.assign "copy" starlark%[child])
    (.seq (.assign "value" starlark%[[52]]) (.ret (some starlark%[copy])))

private def factoryTailCode : ResolvedBody :=
  ⟨.seq (.assignExpr (fileSlot "copy") (localRead "child"))
    (.seq (.assignExpr (fileSlot "value") (boxed 52)) (.returnExpr (localRead "copy"))),
    [fileSlot "child", fileSlot "copy"]⟩

private def factory : Site (moduleLex globals) [] none none .global where
  name := "factory"
  target := by decide
  parameters := ⟨["value"], []⟩
  source := .seq child.statement factoryTail
  binders := ["child", "copy", "value"]
  locals := ["child", "copy"]
  collects := .seq (.define _ _ _) (.seq (.assign _ _) (.seq (.assign _ _) (.ret _)))
  localOrder := .keep (by decide) (.keep (by decide) (.skip (by decide) .nil))
  body := ⟨.seq (.define (fileSlot "child") 0) factoryTailCode.code, child.reads ++ factoryTailCode.reads⟩
  free := [⟨globalSlot "late", globalSlot "late"⟩]
  selects := .owned (.owned (by decide)) (.module (.module (by decide) (by decide) (by decide))
    (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil)))
  defaults := []
  lexical := .nil

private def root : Root globals where
  keywords := []
  varargs := none
  kwargs := none
  site := factory
  lexical := .nil
  seed := #[]
  bodyTable := #[child.declaration]
  children := [(0, child.declaration)]
  returned := some returned
  suite := by
    refine .define (rest := factoryTail) (tail := factoryTailCode)
      (childTable := #[]) (descendants := []) (later := []) child (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil) ?_ ?_
    · refine .plain (.straight (source := childBody) ?_)
      refine .assign (by decide) (.list (.int 44)) ?_
      refine .assign (by decide) (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0)) ?_
      refine .assign (by decide) (.index (.read (by decide) (.enclosing (by decide) (by decide))
        (.enclosing (by decide) (by decide))) (.int 0)) ?_
      exact .ret (.read (by decide) (.global (by decide) (by decide) (by decide))
        (.module (by decide) (by decide) (by decide)))
    · exact .assign (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide)))
        (.copy (name := "child") (by decide) rfl)
        (.assign (by decide) (.list (.int 52)) .forget (.returnLocal (by decide) (by decide) rfl))

private theorem fromGlobal {name : String} (member : name ∈ globals)
    (legal : name.toList.head? ≠ some '$') :
    Body.Operand (moduleLex globals) (.scalar (.read name)) (globalRead name) [globalSlot name] :=
  .read legal (.global (by simp [moduleLex]) (by simp [moduleLex]) member)
    (.module (by simp [moduleLex]) (by simp [moduleLex]) member)

private def make : Invocation globals where
  callee := "factory"
  calleeGlobal := by decide
  legal := by decide
  destination := "escaped"
  destinationGlobal := by decide
  arguments := [starlark%[data]]
  codes := [globalRead "data"]
  reads := [globalSlot "data"]
  operands := .cons (fromGlobal (by decide) (by decide)) .nil
  keywords := .empty

private def mapping (bad : Bool) : Mapping (moduleLex globals) :=
  if bad then ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
    .entry (.string "key") (.plain (.int 8)) .empty⟩
  else ⟨[(.string "extra", starlark%[late])], [(.atom (.string "extra"), globalRead "late")], [globalSlot "late"],
    .entry (.string "extra") (.plain (fromGlobal (by decide) (by decide))) .empty⟩

private def invoke (bad : Bool) : Invocation globals where
  callee := "alias"
  calleeGlobal := by decide
  legal := by decide
  destination := "result"
  destinationGlobal := by decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := ⟨[("another", starlark%[[61]])], [("another", boxed 61)], [], .cons (.list (.int 61)) .nil, by decide⟩
  star := some (.list (.cons (fromGlobal (name := "data") (by decide) (by decide))
    (.cons (fromGlobal (name := "data") (by decide) (by decide)) .nil)))
  mapping := some (mapping bad)

private def commands (bad : Bool) : List Resolve.Command :=
  [.assign "data" starlark%[[31]], root.command, make.source, .assign "late" starlark%[[83]],
   .assign "alias" starlark%[escaped], (invoke bad).source, .assign "after" starlark%[[99]]]

private def code (bad : Bool) : List Modules.Command :=
  [.exec (.assignExpr "data" (boxed 31)), .exec (.define "factory" 1), .exec (.assignExpr "escaped" make.code),
   .exec (.assignExpr "late" (boxed 83)), .exec (.assignExpr "alias" (globalRead "escaped")),
   .exec (.assignExpr "result" (invoke bad).code), .exec (.assignExpr "after" (boxed 99))]

private def exports : Environment :=
  update (update (update (update (update (update (update (fun _ => none) "data" none)
    "factory" (some root.callable)) "escaped" (some (.nested returned))) "late" none)
    "alias" (some (.nested returned))) "result" none) "after" none

private theorem plan (bad : Bool) : Plan globals (fun _ => none) (commands bad) #[] (code bad) root.table exports := by
  refine .assign (by decide) (.list (.int 31)) .forget (.define root ?_)
  refine .invoke make root.callable rfl (.assign (by decide) (.list (.int 83)) .forget ?_)
  refine .assign (by decide) (fromGlobal (by decide) (by decide)) (.copy (name := "escaped") rfl) ?_
  exact .invoke (invoke bad) (.nested returned) rfl (.assign (by decide) (.list (.int 99)) .forget .done)

example (bad : Bool) {resolved : ResolvedModule} (checked : resolve (commands bad) = .ok resolved)
    (caller : Lists.State) :
    ∃ reached, ExecutesAll globals (enter resolved.source caller) (commands bad) reached ∧
      runModule (commands bad) (fun _ => none) caller = .ok (finish resolved.source caller reached) ∧
      ∀ published final, finish resolved.source caller reached = .ok published final →
        PublishedLive exports resolved.program published final := by
  have checkedPlan : Plan (Trace.names (commands bad)) (fun _ => none) (commands bad) #[] (code bad) root.table exports := plan bad
  obtain ⟨out, source, _, _, exactResult, published⟩ := module_agrees checkedPlan checked (fun _ => none) caller
  exact ⟨out, source, exactResult, published⟩

#guard
  match runModule (commands false) (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "escaped", published.exports.lookup "alias", published.exports.lookup "data",
      published.exports.lookup "late", published.exports.lookup "result" with
    | some (.function escaped), some (.function alias), some (.list data), some (.list late), some (.list result) =>
      match final.heap[escaped]? with
      | some ⟨.function closure, true⟩ =>
        escaped == alias && late == result && closure.declaration == 0 &&
        closure.defaults == [(fileSlot "key", .list data)] &&
        final.heap[data]? == some ⟨.list [.scalar (.int 31)], true⟩ &&
        final.heap[late]? == some ⟨.list [.scalar (.int 83)], true⟩ &&
        (match closure.captures with
        | [value, global] =>
          (match final.heap[value.address]? with
          | some ⟨.binding (some (.list rebound)), true⟩ =>
            final.heap[rebound]? == some ⟨.list [.scalar (.int 52)], true⟩
          | _ => false) && final.heap[global.address]? == some ⟨.binding (some (.list late)), false⟩
        | _ => false)
      | _ => false
    | _, _, _, _, _ => false
  | _ => false

#guard
  let caller : Lists.State := { iterators := [123] }
  match runModule (commands true) (fun _ => none) caller, resolve (commands true) with
  | .ok (.error (.runtime .indexTarget) final), .ok resolved =>
    let entered := enter resolved.source caller
    let cell name := (entered.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    let lists := final.heap.toList.filterMap fun cell => match cell.contents with
      | .list [.scalar (.int value)] => some (value, cell.frozen)
      | _ => none
    let tuples := final.heap.toList.countP fun cell => match cell.contents with | .tuple .. => true | _ => false
    let dicts := final.heap.toList.countP fun cell => match cell.contents with | .dict .. => true | _ => false
    lists == [(31, false), (52, false), (83, false), (61, false), (44, false)] && tuples == 1 && dicts == 2 &&
    cell "escaped" == cell "alias" && cell "result" == some ⟨.binding none, false⟩ &&
    cell "after" == some ⟨.binding none, false⟩ && (final.slots (globalSlot "alias")).isNone &&
    final.iterators == [123]
  | _, _ => false

open Imports

private inductive ImportCase where
  | ok | bodyError | missing

private def importName : ImportCase → String
  | .ok | .bodyError => "factory"
  | .missing => "absent"

private def importerGlobals : List String := ["starter", "made", "held", "marker", "result", "late"]

private def importsMapping (test : ImportCase) : Mapping (block ["loaded"] importerGlobals) :=
  match test with
  | .bodyError =>
    ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
      .entry (.string "key") (.plain (.int 8)) .empty⟩
  | .ok | .missing =>
    ⟨[(.string "extra", starlark%[9])], [(.atom (.string "extra"), int 9)], [],
      .entry (.string "extra") (.plain (.int 9)) .empty⟩

private def factoryCall : Imports.Invocation ["loaded"] importerGlobals where
  callee := "starter"
  declared := .inr (by decide)
  legal := by decide
  destination := "made"
  destinationGlobal := by decide
  arguments := [starlark%[[41]]]
  codes := [boxed 41]
  reads := []
  operands := .cons (.list (.int 41)) .nil
  keywords := .empty

private def childCall (test : ImportCase) : Imports.Invocation ["loaded"] importerGlobals where
  callee := "held"
  declared := .inr (by decide)
  legal := by decide
  destination := "result"
  destinationGlobal := by decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := ⟨[("another", starlark%[[71]])], [("another", boxed 71)], [],
    .cons (.list (.int 71)) .nil, by decide⟩
  star := some (.list (.cons (.int 17) (.cons (.int 18) .nil)))
  mapping := some (importsMapping test)

private def consumer (test : ImportCase) : Consumer where
  label := "prodé.star"
  name := importName test
  alias := "loaded"
  publicName := by cases test <;> simp [importName, Modules.isPublic, String.startsWith_string_eq_false_iff]
  globals := importerGlobals
  body :=
    [.assign "starter" (by decide)
        (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.name "loaded"),
      .invoke factoryCall,
      .assign "held" (by decide)
        (.read (by decide) (.global (by decide) (by decide) (by decide))
          (.module (by decide) (by decide) (by decide))) (.name "made"),
      .assign "marker" (by decide) (.list (.int 88)) .forget,
      .invoke (childCall test),
      .assign "late" (by decide) (.list (.int 199)) .forget]
  declared := rfl
  separate := by decide

private theorem covered (test : ImportCase) (program : Program) : Covered exports (commands false) (consumer test) program := by
  have ready : ReadyFor program (initial "loaded" (.regular root.callable)) (consumer test).body := by
    exact ⟨.regular root.callable, rfl, ⟨.regular (.nested returned), rfl, trivial⟩⟩
  cases test
  · exact .inl ⟨root.callable, rfl, ready⟩
  · exact .inl ⟨root.callable, rfl, ready⟩
  · exact .inr (by decide)

example (test : ImportCase) {producer importer : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve (consumer test).commands producer.program = .ok importer)
    (caller : Lists.State) :
    Agrees (commands false) producer importer (consumer test) exports ⟨caller, []⟩ :=
  cold_agrees (commands := commands false) (plan false) prod (consumer test) imp (covered test producer.program) caller

example (test : ImportCase) {producer importer : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve (consumer test).commands producer.program = .ok importer)
    (caller : Lists.State) :
    ∃ preload, Producer (commands false) producer.source ⟨caller, []⟩ preload ∧
      Loader.load importer.program (graph producer importer (consumer test)) 0 ⟨caller, []⟩ = preload ∧
      ∀ published reached, preload = .ok published reached →
        reached.cache = [(0, published)] ∧ Agrees (commands false) producer importer (consumer test) exports reached :=
  preloaded_agrees (commands := commands false) (plan false) prod (consumer test) imp (covered test producer.program) caller

private def runImport (test : ImportCase) (warm : Bool) : Option (Loader.Result Modules.Published) := do
  let producer ← (resolve (commands false)).toOption
  let importer ← (resolve (consumer test).commands producer.program).toOption
  let manifest := graph producer importer (consumer test)
  let caller : Loader.Session := { runtime := {iterators := [123]} }
  if warm then
    match Loader.load importer.program manifest 0 caller with
    | .ok _ state => some (Loader.load importer.program manifest 1 state)
    | .error .. => none
  else
    some (Loader.load importer.program manifest 1 caller)

private def imported (warm : Bool) : Bool :=
  match runImport .ok warm with
  | some (.ok published final) =>
    match final.cache.lookup 0, published.exports.lookup "result", published.exports.lookup "late",
      published.exports.lookup "made", published.exports.lookup "held" with
    | some producer, some (.list result), some (.list consumerLate), some (.function made), some (.function held) =>
      match producer.exports.lookup "factory", producer.exports.lookup "escaped", producer.exports.lookup "late" with
      | some (.function factory), some (.function escaped), some (.list producerLate) =>
        match final.runtime.heap[made]?, final.runtime.heap[escaped]? with
        | some ⟨.function closure, true⟩, some ⟨.function prior, true⟩ =>
          let lists := final.runtime.heap.toList.filterMap (fun cell => match cell.contents with
            | .list [.scalar (.int n)] => some n
            | _ => none)
          final.cache.map Prod.fst == [1, 0] && made == held && made != escaped &&
          published.exports.lookup "starter" == some (.function factory) &&
          published.exports.lookup "loaded" == none && result == producerLate && result != consumerLate &&
          final.runtime.heap[result]? == some ⟨.list [.scalar (.int 83)], true⟩ &&
          final.runtime.heap[consumerLate]? == some ⟨.list [.scalar (.int 199)], true⟩ &&
          (match closure.defaults with
           | [(name, .list saved)] =>
             name == fileSlot "key" && final.runtime.heap[saved]? == some ⟨.list [.scalar (.int 41)], true⟩
           | _ => false) &&
          (match closure.captures, prior.captures with
           | [localCapture, globalCapture], [oldLocal, oldGlobal] =>
             localCapture.address != oldLocal.address && globalCapture.address == oldGlobal.address &&
             (match final.runtime.heap[localCapture.address]? with
             | some ⟨.binding (some (.list rebound)), true⟩ =>
               final.runtime.heap[rebound]? == some ⟨.list [.scalar (.int 52)], true⟩
             | _ => false) &&
             final.runtime.heap[globalCapture.address]? == some ⟨.binding (some (.list producerLate)), false⟩
           | _, _ => false) &&
          lists.count 31 == 1 && lists.count 44 == 2 && final.runtime.iterators == [123] &&
          (final.runtime.slots (fileSlot "loaded")).isNone
        | _, _ => false
      | _, _, _ => false
    | _, _, _, _, _ => false
  | _ => false

#guard imported false
#guard imported true

private def failedImport (test : ImportCase) (warm : Bool) (expected : Modules.Error) (retained : List Int) : Bool :=
  match runImport test warm with
  | some (.error (.initialization 1 error) final) =>
    let lists := final.runtime.heap.toList.filterMap fun cell => match cell.contents, cell.frozen with
      | .list [.scalar (.int n)], false => some n
      | _, _ => none
    error == expected && final.cache.map Prod.fst == [0] && lists == retained &&
      (final.runtime.slots (fileSlot "loaded")).isNone && final.runtime.iterators == [123]
  | _ => false

-- The producer's unreachable operand/body allocations remain in both heaps.
-- The missing import skips the full suite. The second-call error retains
-- the factory's saved value, rebinding and earlier importer assignment.
#guard failedImport .missing false (.missingExport "prodé.star" "absent") [61, 44]
#guard failedImport .missing true (.missingExport "prodé.star" "absent") [61, 44]
#guard failedImport .bodyError false (.runtime .indexTarget) [61, 44, 41, 52, 88, 71, 44]
#guard failedImport .bodyError true (.runtime .indexTarget) [61, 44, 41, 52, 88, 71, 44]


private def wrapperMapping (test : ImportCase) : Mapping ⟨[], ["loaded"], ["relay", "result"]⟩ :=
  match test with
  | .bodyError => ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
      .entry (.string "key") (.plain (.int 8)) .empty⟩
  | .ok | .missing => ⟨[(.string "extra", starlark%[9])], [(.atom (.string "extra"), int 9)], [],
      .entry (.string "extra") (.plain (.int 9)) .empty⟩

private def consumerWrapper (test : ImportCase) : Imports.Wrapper where
  label := "prodé.star"
  imported := match test with | .ok | .bodyError => "escaped" | .missing => "absent"
  alias := "loaded"
  name := "relay"
  destination := "result"
  publicImport := by cases test <;> simp [Modules.isPublic, String.startsWith_string_eq_false_iff]
  legalAlias := by decide
  legalName := by decide
  separate := by decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := ⟨[("another", starlark%[[71]])], [("another", boxed 71)], [],
    .cons (.list (.int 71)) .nil, by decide⟩
  star := some (.list (.cons (.int 17) (.cons (.int 18) .nil)))
  mapping := some (wrapperMapping test)
  selects := by cases test <;> exact .enclosing (.enclosing (by decide) (by decide)) .nil

private theorem wrapperCovered (test : ImportCase) :
    (∃ callee, exports (consumerWrapper test).imported = some callee) ∨
      (consumerWrapper test).imported ∉ Trace.names (commands false) := by
  cases test
  · exact .inl ⟨.nested returned, rfl⟩
  · exact .inl ⟨.nested returned, rfl⟩
  · exact .inr (by decide)

example (test : ImportCase) {producer importer : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve (consumerWrapper test).commands producer.program = .ok importer)
    (caller : Lists.State) : (consumerWrapper test).Agrees producer importer (commands false) exports ⟨caller, []⟩ :=
  Imports.Wrapper.cold_agrees (commands := commands false) (consumerWrapper test) (plan false) prod imp (wrapperCovered test) caller

private def runWrapper (test : ImportCase) (warm : Bool) : Option (Loader.Result Modules.Published) := do
  let wrapper := consumerWrapper test
  let producer ← (resolve (commands false)).toOption
  let importer ← (resolve wrapper.commands producer.program).toOption
  let manifest := wrapper.graph producer importer
  let caller : Loader.Session := { runtime := {iterators := [123]} }
  if warm then
    match Loader.load importer.program manifest 0 caller with
    | .ok _ state => some (Loader.load importer.program manifest 1 state)
    | .error .. => none
  else
    some (Loader.load importer.program manifest 1 caller)

private def wrapped (warm : Bool) : Bool :=
  match runWrapper .ok warm with
  | some (.ok published final) =>
    match final.cache.lookup 0, published.exports.lookup "relay", published.exports.lookup "result" with
    | some producer, some (.function relay), some (.list result) =>
      match producer.exports.lookup "escaped", producer.exports.lookup "late", producer.exports.lookup "data" with
      | some (.function escaped), some (.list late), some (.list data) =>
        match final.runtime.heap[relay]?, final.runtime.heap[escaped]? with
        | some ⟨.function wrapper, true⟩, some ⟨.function imported, true⟩ =>
          final.cache.map Prod.fst == [1, 0] && wrapper.declaration == 2 && imported.declaration == 0 &&
          imported.defaults == [(fileSlot "key", .list data)] && result == late &&
          published.exports.lookup "loaded" == none && (final.runtime.slots (fileSlot "loaded")).isNone &&
          final.runtime.heap[late]? == some ⟨.list [.scalar (.int 83)], true⟩ &&
          final.runtime.iterators == [123] &&
          (match wrapper.captures, imported.captures with
           | [alias], [localCapture, globalCapture] =>
             final.runtime.heap[alias.address]? == some ⟨.binding (some (.function escaped)), true⟩ &&
             final.runtime.heap[globalCapture.address]? == some ⟨.binding (some (.list late)), false⟩ &&
             (match final.runtime.heap[localCapture.address]? with
              | some ⟨.binding (some (.list rebound)), true⟩ =>
                final.runtime.heap[rebound]? == some ⟨.list [.scalar (.int 52)], true⟩
              | _ => false)
           | _, _ => false)
        | _, _ => false
      | _, _, _ => false
    | _, _, _ => false
  | _ => false

#guard wrapped false
#guard wrapped true

private def failedWrapper (test : ImportCase) (warm : Bool) (expected : Modules.Error) (retained : List Int) : Bool :=
  match runWrapper test warm with
  | some (.error (.initialization 1 error) final) =>
    let lists := final.runtime.heap.toList.filterMap fun cell => match cell.contents, cell.frozen with
      | .list [.scalar (.int n)], false => some n
      | _, _ => none
    let hasWrapper := final.runtime.heap.any fun cell => match cell.contents, cell.frozen with
      | .function closure, false => closure.declaration == 2
      | _, _ => false
    let reachedWrapper := match test with | .missing => false | _ => true
    error == expected && final.cache.map Prod.fst == [0] && lists == retained &&
      hasWrapper == reachedWrapper && (final.runtime.slots (globalSlot "result")).isNone &&
      (final.runtime.slots (fileSlot "loaded")).isNone && final.runtime.iterators == [123]
  | _ => false

#guard failedWrapper .missing false (.missingExport "prodé.star" "absent") [61, 44]
#guard failedWrapper .missing true (.missingExport "prodé.star" "absent") [61, 44]
#guard failedWrapper .bodyError false (.runtime .indexTarget) [61, 44, 71, 44]
#guard failedWrapper .bodyError true (.runtime .indexTarget) [61, 44, 71, 44]


private def declarationGlobals : List String :=
  ["first", "copied", "marker", "second", "firstOut", "secondOut", "after"]

private def relayMapping (second bad : Bool) : Mapping ⟨[], ["loaded"], declarationGlobals⟩ :=
  if second then
    if bad then
      ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
        .entry (.string "key") (.plain (.int 8)) .empty⟩
    else
      ⟨[(.string "key", starlark%[[72]])], [(.atom (.string "key"), boxed 72)], [],
        .entry (.string "key") (.plain (.list (.int 72))) .empty⟩
  else
    ⟨[(.string "extra", starlark%[9])], [(.atom (.string "extra"), int 9)], [],
      .entry (.string "extra") (.plain (.int 9)) .empty⟩

private def relayDeclaration (second bad : Bool) : Imports.WrapperDeclaration "loaded" ["loaded"] declarationGlobals where
  name := if second then "second" else "first"
  target := by cases second <;> decide
  visible := by decide
  legalAlias := by decide
  parameters := ⟨[], []⟩
  keywordOnly := []
  varargs := none
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := ⟨[("another", starlark%[[71]])], [("another", boxed 71)], [],
    .cons (.list (.int 71)) .nil, by decide⟩
  star := some (.list (.cons (.int 17) (.cons (.int 18) .nil)))
  mapping := some (relayMapping second bad)
  selects := by cases second <;> cases bad <;> exact .enclosing (.enclosing (by decide) (by decide)) .nil

private def callDeclaration (second : Bool) : Imports.Invocation ["loaded"] declarationGlobals where
  callee := if second then "second" else "copied"
  declared := .inr (by cases second <;> decide)
  legal := by cases second <;> decide
  destination := if second then "secondOut" else "firstOut"
  destinationGlobal := by cases second <;> decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := .empty

private def declarationSuite (bad : Bool) : Consumer where
  label := "prodé.star"
  name := "escaped"
  alias := "loaded"
  publicName := by simp [Modules.isPublic, String.startsWith_string_eq_false_iff]
  globals := declarationGlobals
  body :=
    [.define (relayDeclaration false bad),
     .assign "copied" (by decide) (.read (by decide) (.global (by decide) (by decide) (by decide))
       (.module (by decide) (by decide) (by decide))) (.name "first"),
     .assign "marker" (by decide) (.list (.int 88)) .forget,
     .define (relayDeclaration true bad),
     .invoke (callDeclaration false),
     .invoke (callDeclaration true),
     .assign "after" (by decide) (.list (.int 199)) .forget]
  declared := rfl
  separate := by decide

private theorem declarationCovered (bad : Bool) (program : Program) (positive : 0 < program.size) :
    Covered exports (commands false) (declarationSuite bad) program :=
  .inl ⟨.nested returned, rfl,
    ⟨.regular (.nested returned), rfl, positive, .regular (.nested returned), rfl, by change 0 < (program.push _).size; simp,
      .wrapper (relayDeclaration false bad) program.size (.regular (.nested returned)), rfl,
      ⟨.wrapper (relayDeclaration true bad) (program.push (relayDeclaration false bad).site.declaration).size (.regular (.nested returned)), rfl, trivial⟩⟩⟩

example (bad : Bool) {producer importer : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve (declarationSuite bad).commands producer.program = .ok importer)
    (caller : Lists.State) :
    Agrees (commands false) producer importer (declarationSuite bad) exports ⟨caller, []⟩ :=
  cold_agrees (commands := commands false) (plan false) prod (declarationSuite bad) imp
    (declarationCovered bad producer.program (by rw [(plan_code (commands := commands false) (plan false) prod).2]; decide)) caller

private def runDeclarationSuite (consumer : Consumer) (warm : Bool) : Option (Loader.Result Modules.Published × Lists.State) := do
  let producer ← (resolve (commands false)).toOption
  let importer ← (resolve consumer.commands producer.program).toOption
  let manifest := graph producer importer consumer
  let caller : Loader.Session := { runtime := { iterators := [123] } }
  let entry ← if warm then
      match Loader.load importer.program manifest 0 caller with
      | .ok _ reached => some reached
      | .error .. => none
    else some caller
  some (Loader.load importer.program manifest 1 entry, enter importer.source entry.runtime)

private def relaySuiteSuccess (warm : Bool) : Bool :=
  match runDeclarationSuite (declarationSuite false) warm with
  | some (.ok published final, _) =>
    let heap := final.runtime.heap
    match final.cache.lookup 0, published.exports.lookup "first", published.exports.lookup "second" with
    | some producer, some (.function first), some (.function second) =>
      match producer.exports.lookup "late", producer.exports.lookup "escaped", producer.exports.lookup "data",
        heap[first]?, heap[second]? with
      | some (.list late), some (.function escaped), some (.list data),
          some ⟨.function firstRecord, true⟩, some ⟨.function secondRecord, true⟩ =>
        first != second && firstRecord.declaration == 2 && secondRecord.declaration == 3 &&
        firstRecord.captures == secondRecord.captures &&
        (match firstRecord.captures, heap[escaped]? with
         | [capture], some ⟨.function original, true⟩ =>
           original.declaration == 0 && original.defaults == [(fileSlot "key", .list data)] &&
           heap[capture.address]? == some ⟨.binding (some (.function escaped)), true⟩
         | _, _ => false) &&
        published.exports.lookup "copied" == some (.function first) &&
        published.exports.lookup "firstOut" == some (.list late) &&
        published.exports.lookup "secondOut" == some (.list late) &&
        final.cache.map Prod.fst == [1, 0] && final.runtime.iterators == [123]
      | _, _, _, _, _ => false
    | _, _, _ => false
  | _ => false

private def relaySuiteFailure (warm : Bool) : Bool :=
  match runDeclarationSuite (declarationSuite true) warm with
  | some (.error (.initialization 1 (.runtime .indexTarget)) final, entered) =>
    let cell name := (entered.slots (globalSlot name)).bind (fun slot => final.runtime.heap[slot.address]?)
    let allocations := final.runtime.heap.toList.filterMap fun cell =>
      match cell.contents, cell.frozen with
      | .list [.scalar (.int n)], false => some n
      | _, _ => none
    match final.cache.lookup 0 with
    | some producer =>
      final.cache.map Prod.fst == [0] && final.runtime.iterators == [123] &&
      (final.runtime.slots (fileSlot "loaded")).isNone &&
      cell "first" == cell "copied" &&
      cell "firstOut" == some ⟨.binding (producer.exports.lookup "late"), false⟩ &&
      cell "secondOut" == some ⟨.binding none, false⟩ && cell "after" == some ⟨.binding none, false⟩ &&
      allocations == [61, 44, 88, 71, 44, 71, 44]
    | none => false
  | _ => false

#guard relaySuiteSuccess false
#guard relaySuiteSuccess true
#guard relaySuiteFailure false
#guard relaySuiteFailure true


private def factoryWrapperGlobals : List String := ["make", "held", "result"]

private def factoryWrapper : Imports.WrapperDeclaration "loaded" ["loaded"] factoryWrapperGlobals where
  name := "make"
  target := by decide
  visible := by decide
  legalAlias := by decide
  arguments := [starlark%[[41]]]
  codes := [boxed 41]
  reads := []
  operands := .cons (.list (.int 41)) .nil
  keywords := .empty
  selects := .enclosing (.enclosing (by decide) (by decide)) .nil

private def factoryWrapperConsumer : Consumer where
  label := "prodé.star"
  name := "factory"
  alias := "loaded"
  publicName := by simp [Modules.isPublic, String.startsWith_string_eq_false_iff]
  globals := factoryWrapperGlobals
  body := [.define factoryWrapper,
    .invoke { callee := "make", declared := .inr (by decide), legal := by decide
              destination := "held", destinationGlobal := by decide
              arguments := [], codes := [], reads := [], operands := .nil, keywords := .empty },
    .invoke { callee := "held", declared := .inr (by decide), legal := by decide
              destination := "result", destinationGlobal := by decide
              arguments := [starlark%[17]], codes := [int 17], reads := [], operands := .cons (.int 17) .nil
              keywords := .empty }]
  declared := rfl
  separate := by decide

example {producer importer : ResolvedModule} (prod : resolve (commands false) #[] = .ok producer)
    (imp : resolve factoryWrapperConsumer.commands producer.program = .ok importer)
    (caller : Lists.State) :
    Agrees (commands false) producer importer factoryWrapperConsumer exports ⟨caller, []⟩ :=
  cold_agrees (commands := commands false) (plan false) prod factoryWrapperConsumer imp
    (.inl ⟨root.callable, rfl, ⟨.regular root.callable, rfl,
      by rw [(plan_code (commands := commands false) (plan false) prod).2]; decide, .wrapper factoryWrapper producer.program.size (.regular root.callable), rfl,
      ⟨.regular (.nested returned), rfl, trivial⟩⟩⟩) caller

#guard
  match runDeclarationSuite factoryWrapperConsumer false with
  | some (.ok published final, _) =>
    match final.cache.lookup 0, published.exports.lookup "held" with
    | some producer, some (.function held) =>
      match producer.exports.lookup "escaped", final.runtime.heap[held]? with
      | some (.function escaped), some ⟨.function closure, true⟩ =>
        held != escaped && closure.declaration == 0 &&
        published.exports.lookup "result" == producer.exports.lookup "late" &&
        (match closure.defaults with
         | [(slot, .list saved)] =>
           slot == fileSlot "key" && final.runtime.heap[saved]? == some ⟨.list [.scalar (.int 41)], true⟩
         | _ => false)
      | _, _ => false
    | _, _ => false
  | _ => false


private def middleGlobals : List String := ["relay", "before", "reexport"]

private def middleWrapper : Imports.WrapperDeclaration "loaded" ["loaded"] middleGlobals where
  name := "relay"
  target := by decide
  visible := by decide
  legalAlias := by decide
  arguments := [starlark%[17]]
  codes := [int 17]
  reads := []
  operands := .cons (.int 17) .nil
  keywords := .empty
  selects := .enclosing (.enclosing (by decide) (by decide)) .nil

private def middleConsumer : Consumer where
  label := "prodé.star"
  name := "escaped"
  alias := "loaded"
  publicName := by simp [Modules.isPublic, String.startsWith_string_eq_false_iff]
  globals := middleGlobals
  body :=
    [.define middleWrapper,
     .invoke { callee := "relay", declared := .inr (by decide), legal := by decide
               destination := "before", destinationGlobal := by decide
               arguments := [], codes := [], reads := [], operands := .nil, keywords := .empty },
     .assign "reexport" (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide)))
       (.name "loaded")]
  declared := rfl
  separate := by decide

private def lastGlobals : List String := ["held", "first", "marker", "answer", "after"]

private def lastMapping (bad : Bool) : Mapping (block ["transferred"] lastGlobals) :=
  if bad then ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
    .entry (.string "key") (.plain (.int 8)) .empty⟩
  else ⟨[(.string "key", starlark%[[72]])], [(.atom (.string "key"), boxed 72)], [],
    .entry (.string "key") (.plain (.list (.int 72))) .empty⟩

private def lastCall (second bad : Bool) : Imports.Invocation ["transferred"] lastGlobals where
  callee := "held"
  declared := .inr (by decide)
  legal := by decide
  destination := if second then "answer" else "first"
  destinationGlobal := by cases second <;> decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := ⟨[("another", starlark%[[71]])], [("another", boxed 71)], [],
    .cons (.list (.int 71)) .nil, by decide⟩
  star := some (.list (.cons (.int 17) (.cons (.int 18) .nil)))
  mapping := if second then some (lastMapping bad) else none

private def lastConsumer (bad : Bool) : Consumer where
  label := "middle.star"
  name := "reexport"
  alias := "transferred"
  publicName := by simp [Modules.isPublic, String.startsWith_string_eq_false_iff]
  globals := lastGlobals
  body :=
    [.assign "held" (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.name "transferred"),
     .invoke (lastCall false bad),
     .assign "marker" (by decide) (.list (.int 88)) .forget,
     .invoke (lastCall true bad),
     .assign "after" (by decide) (.list (.int 199)) .forget]
  declared := rfl
  separate := by decide

private def chainManifest (producer middle last : ResolvedModule) : Loader.Manifest :=
  #[⟨producer.source, []⟩, ⟨middle.source, [("prodé.star", 0)]⟩, ⟨last.source, [("middle.star", 1)]⟩]

private def chainExports (producer middle : Program) (middlePlan lastPlan : Consumer) (imported : Callee) : Nat → Tracked
  | 0 => Imports.Chain.rootExports exports
  | 1 => Imports.Chain.exportsOf middlePlan producer (.regular (.nested returned))
  | _ => Imports.Chain.exportsOf lastPlan middle imported

private def checkedThree (middlePlan lastPlan : Consumer) {producer middle last : ResolvedModule}
    (producerChecked : resolve (commands false) #[] = .ok producer)
    (middleChecked : resolve middlePlan.commands producer.program = .ok middle)
    (lastChecked : resolve lastPlan.commands middle.program = .ok last)
    (middleDemand : Imports.Chain.Demand middlePlan producer.program (Imports.Chain.rootExports exports)
      producer.source (Imports.Chain.exportsOf middlePlan producer.program (.regular (.nested returned))))
    {imported : Callee}
    (lastDemand : Imports.Chain.Demand lastPlan middle.program
      (Imports.Chain.exportsOf middlePlan producer.program (.regular (.nested returned))) middle.source
      (Imports.Chain.exportsOf lastPlan middle.program imported))
    (rootLabel : middlePlan.label = "prodé.star") (middleLabel : lastPlan.label = "middle.star") :
    Imports.Chain.Graph producer.program (chainManifest producer middle last) where
  commands := lastPlan.commands
  seed := middle.program
  linked := last
  checked := lastChecked
  includesOrigin := fun index entry seen =>
    consumer_preserves lastPlan lastChecked index entry (consumer_preserves middlePlan middleChecked index entry seen)
  exports := chainExports producer.program middle.program middlePlan lastPlan imported
  nodes := by
    intro id bound
    have range : id = 0 ∨ id = 1 ∨ id = 2 := by
      change id < 3 at bound
      omega
    rcases range with rfl | rfl | rfl
    · exact .root (commands := commands false) (plan false) rfl producerChecked (fun _ _ seen => seen) rfl
    · exact .importer middlePlan (show 0 < 1 by decide) middleChecked (fun _ _ seen => seen)
        (consumer_preserves lastPlan lastChecked) rfl (by simp [chainManifest, Loader.resolve, rootLabel]) middleDemand
    · exact .importer lastPlan (show 1 < 2 by decide) lastChecked (consumer_preserves middlePlan middleChecked)
        (fun _ _ seen => seen) rfl (by simp [chainManifest, Loader.resolve, middleLabel]) lastDemand

private def checkedChain (bad : Bool) {producer middle last : ResolvedModule}
    (producerChecked : resolve (commands false) #[] = .ok producer)
    (middleChecked : resolve middleConsumer.commands producer.program = .ok middle)
    (lastChecked : resolve (lastConsumer bad).commands middle.program = .ok last) :
    Imports.Chain.Graph producer.program (chainManifest producer middle last) := by
  have rootSize : producer.program.size = 2 := by rw [(plan_code (commands := commands false) (plan false) producerChecked).2]; rfl
  have midSize : middle.program.size = producer.program.size + 1 := by
    rw [(consumer_layout middleConsumer middleChecked).1]
    change (producer.program.push middleWrapper.site.declaration).size = _
    simp
  exact checkedThree middleConsumer (lastConsumer bad) producerChecked middleChecked lastChecked
    (.found (.regular (.nested returned)) rfl (by change 0 < producer.program.size; omega)
      ⟨.regular (.nested returned), rfl, by change 0 < producer.program.size; omega, .wrapper middleWrapper producer.program.size (.regular (.nested returned)), rfl, trivial⟩)
    (.found (.regular (.nested returned)) rfl (by change 0 < middle.program.size; omega)
      ⟨.regular (.nested returned), rfl, ⟨.regular (.nested returned), rfl, trivial⟩⟩) rfl rfl

example (bad : Bool) {producer middle last : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (mid : resolve middleConsumer.commands producer.program = .ok middle)
    (checked : resolve (lastConsumer bad).commands middle.program = .ok last)
    (caller : Lists.State) (history : List Nat) (bounded : ∀ id ∈ history, id < 3) :
    let graph := checkedChain bad prod mid checked
    ∃ entered out, Imports.Chain.Requests graph history ⟨caller, []⟩ entered ∧
      Imports.Chain.TraceRun (chainManifest producer middle last) 2 entered out ∧
      Loader.load last.program (chainManifest producer middle last) 2 entered = out ∧
      Imports.Chain.Cache producer.program last.program (chainManifest producer middle last) graph.exports (Imports.Chain.resultSession out) := by
  intro graph
  have empty : Imports.Chain.Cache producer.program last.program (chainManifest producer middle last) graph.exports ⟨caller, []⟩ := by
    intro id published seen
    cases seen
  obtain ⟨entered, preload, cache⟩ := Imports.Chain.requests graph history bounded ⟨caller, []⟩ empty
  obtain ⟨out, source, _, meaning, reached⟩ := Imports.Chain.agrees graph 2 (by change 2 < 3; decide) entered cache
  exact ⟨entered, out, preload, source, meaning, reached.cache⟩

private def runChainCommands (middlePlan : Consumer) (source : List Resolve.Command) (preload : Option Nat) :
    Option (Loader.Result Modules.Published × Lists.State) := do
  let producer ← (resolve (commands false)).toOption
  let middle ← (resolve middlePlan.commands producer.program).toOption
  let last ← (resolve source middle.program).toOption
  let manifest := chainManifest producer middle last
  let cold : Loader.Session := { runtime := {iterators := [123]} }
  let ready ← match preload with
    | none => some cold
    | some id =>
      match Loader.load last.program manifest id cold with
      | .ok _ state => some state
      | .error .. => none
  some (Loader.load last.program manifest 2 ready, enter last.source ready.runtime)

private def runChain (bad : Bool) : Option Nat → Option (Loader.Result Modules.Published × Lists.State) :=
  runChainCommands middleConsumer (lastConsumer bad).commands

private def chainOK (preload : Option Nat) : Bool :=
  match runChain false preload with
  | some (.ok published final, _) =>
    match final.cache.lookup 0, final.cache.lookup 1 with
    | some producer, some middle =>
      match producer.exports.lookup "escaped", producer.exports.lookup "late",
        producer.exports.lookup "data", middle.exports.lookup "relay" with
      | some (.function address), some (.list late), some (.list data), some (.function wrapper) =>
        match final.runtime.heap[address]?, final.runtime.heap[wrapper]? with
        | some ⟨.function closure, true⟩, some ⟨.function linked, true⟩ =>
          closure.declaration == 0 && linked.declaration == 2 &&
          closure.defaults == [(fileSlot "key", .list data)] &&
          (match closure.captures, linked.captures with
           | [_, global], [capturedImport] =>
             final.runtime.heap[global.address]? == some ⟨.binding (some (.list late)), false⟩ &&
             final.runtime.heap[capturedImport.address]? == some ⟨.binding (some (.function address)), true⟩
           | _, _ => false) &&
          middle.exports.lookup "reexport" == some (.function address) &&
          middle.exports.lookup "before" == some (.list late) &&
          published.exports.lookup "held" == some (.function address) &&
          published.exports.lookup "first" == some (.list late) &&
          published.exports.lookup "answer" == some (.list late) &&
          final.runtime.heap[late]? == some ⟨.list [.scalar (.int 83)], true⟩ &&
          final.cache.map Prod.fst == [2, 1, 0] && final.runtime.iterators == [123]
        | _, _ => false
      | _, _, _, _ => false
    | _, _ => false
  | _ => false

private def chainError (preload : Option Nat) : Bool :=
  match runChain true preload with
  | some (.error (.initialization 2 (.runtime .indexTarget)) final, entered) =>
    let cell name := (entered.slots (globalSlot name)).bind (fun slot => final.runtime.heap[slot.address]?)
    let marker := match cell "marker" with
      | some ⟨.binding (some (.list address)), false⟩ =>
        final.runtime.heap[address]? == some ⟨.list [.scalar (.int 88)], false⟩
      | _ => false
    match final.cache.lookup 0 with
    | some producer =>
      marker && cell "held" == some ⟨.binding (producer.exports.lookup "escaped"), false⟩ &&
      cell "first" == some ⟨.binding (producer.exports.lookup "late"), false⟩ &&
      cell "answer" == some ⟨.binding none, false⟩ && cell "after" == some ⟨.binding none, false⟩ &&
      (final.runtime.slots (fileSlot "transferred")).isNone && final.runtime.iterators == [123] &&
      final.cache.map Prod.fst == [1, 0]
    | none => false
  | _ => false

#guard chainOK none
#guard chainOK (some 0)
#guard chainOK (some 1)
#guard chainError none
#guard chainError (some 0)
#guard chainError (some 1)


private def exportedWrapper (bad : Bool) : Imports.WrapperDeclaration "loaded" ["loaded"] middleGlobals :=
  { middleWrapper with
    mapping := if bad then some ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
      .entry (.string "key") (.plain (.int 8)) .empty⟩ else none
    selects := by cases bad <;> exact .enclosing (.enclosing (by decide) (by decide)) .nil }

private def middleWithWrapper (bad : Bool) : Consumer :=
  { middleConsumer with
    body := [.define (exportedWrapper bad),
      .invoke { callee := "loaded", declared := .inl (by decide), legal := by decide
                destination := "before", destinationGlobal := by decide
                arguments := [starlark%[17]], codes := [int 17], reads := [], operands := .cons (.int 17) .nil
                keywords := .empty },
      .assign "reexport" (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.name "loaded")]
    declared := rfl }

private def finalWrapperGlobals : List String := ["held", "marker", "outer", "answer", "after"]

private def outerWrapper : Imports.WrapperDeclaration "wrapped" ["wrapped"] finalWrapperGlobals where
  name := "outer"
  target := by decide
  visible := by decide
  legalAlias := by decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := .empty
  selects := .enclosing (.enclosing (by decide) (by decide)) .nil

private def finalWrapperConsumer (nested : Bool) : Consumer where
  label := "middle.star"
  name := "relay"
  alias := "wrapped"
  publicName := by simp [Modules.isPublic, String.startsWith_string_eq_false_iff]
  globals := finalWrapperGlobals
  body :=
    [.assign "held" (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.name "wrapped"),
     .assign "marker" (by decide) (.list (.int 88)) .forget,
     .define outerWrapper,
     .invoke { callee := if nested then "outer" else "held"
               declared := .inr (by cases nested <;> decide)
               legal := by cases nested <;> decide
               destination := "answer", destinationGlobal := by decide
               arguments := [], codes := [], reads := [], operands := .nil, keywords := .empty },
     .assign "after" (by decide) (.list (.int 199)) .forget]
  declared := rfl
  separate := by decide

private def checkedWrapperChain (bad nested : Bool) {producer middle last : ResolvedModule}
    (producerChecked : resolve (commands false) #[] = .ok producer)
    (middleChecked : resolve (middleWithWrapper bad).commands producer.program = .ok middle)
    (lastChecked : resolve (finalWrapperConsumer nested).commands middle.program = .ok last) :
    Imports.Chain.Graph producer.program (chainManifest producer middle last) := by
  let imported := Callee.wrapper (exportedWrapper bad) producer.program.size (.regular (.nested returned))
  have rootSize : producer.program.size = 2 := by rw [(plan_code (commands := commands false) (plan false) producerChecked).2]; rfl
  have midSize : middle.program.size = producer.program.size + 1 := by
    rw [(consumer_layout (middleWithWrapper bad) middleChecked).1]
    change (producer.program.push (exportedWrapper bad).site.declaration).size = _
    simp
  refine checkedThree (middleWithWrapper bad) (finalWrapperConsumer nested) producerChecked middleChecked lastChecked
    (.found (.regular (.nested returned)) rfl (by change 0 < producer.program.size; omega)
      ⟨.regular (.nested returned), rfl, by change 0 < producer.program.size; omega, .regular (.nested returned), rfl, trivial⟩)
    (.found imported rfl (by change producer.program.size < middle.program.size; omega) ?_) rfl rfl
  cases nested
  · exact ⟨imported, rfl, by change producer.program.size < middle.program.size; omega, imported, rfl, trivial⟩
  · exact ⟨imported, rfl, by change producer.program.size < middle.program.size; omega,
      .wrapper outerWrapper middle.program.size imported, rfl, trivial⟩

example (bad nested : Bool) {producer middle last : ResolvedModule}
    (prod : resolve (commands false) #[] = .ok producer)
    (mid : resolve (middleWithWrapper bad).commands producer.program = .ok middle)
    (checked : resolve (finalWrapperConsumer nested).commands middle.program = .ok last)
    (caller : Lists.State) (history : List Nat) (bounded : ∀ id ∈ history, id < 3) :
    let graph := checkedWrapperChain bad nested prod mid checked
    ∃ entered out, Imports.Chain.Requests graph history ⟨caller, []⟩ entered ∧
      Imports.Chain.TraceRun (chainManifest producer middle last) 2 entered out ∧
      Loader.load last.program (chainManifest producer middle last) 2 entered = out ∧
      Imports.Chain.Reached producer.program last.program (chainManifest producer middle last) graph.exports 2 entered out := by
  intro graph
  obtain ⟨entered, preloaded, valid⟩ := Imports.Chain.requests graph history bounded ⟨caller, []⟩
    (fun _ _ missing => nomatch missing)
  obtain ⟨out, source, _, exactRun, reached⟩ := Imports.Chain.agrees graph 2 (by change 2 < 3; decide) entered valid
  exact ⟨entered, out, preloaded, source, exactRun, reached⟩

private def wrapperChainOK (nested : Bool) (preload : Option Nat) : Bool :=
  match runChainCommands (middleWithWrapper false) (finalWrapperConsumer nested).commands preload with
  | some (.ok published final, _) =>
    match final.cache.lookup 0, final.cache.lookup 1 with
    | some producer, some middle =>
      match producer.exports.lookup "escaped", producer.exports.lookup "late",
        producer.exports.lookup "data", middle.exports.lookup "relay", published.exports.lookup "outer" with
      | some (.function original), some (.list late), some (.list data), some (.function inner), some (.function outer) =>
        match final.runtime.heap[original]?, final.runtime.heap[inner]?, final.runtime.heap[outer]? with
        | some ⟨.function source, true⟩, some ⟨.function relay, true⟩, some ⟨.function shell, true⟩ =>
          source.declaration == 0 && relay.declaration == 2 && shell.declaration == 3 &&
          source.defaults == [(fileSlot "key", .list data)] &&
          (match source.captures, relay.captures, shell.captures with
           | [_, global], [innerImport], [outerImport] =>
             final.runtime.heap[global.address]? == some ⟨.binding (some (.list late)), false⟩ &&
             final.runtime.heap[innerImport.address]? == some ⟨.binding (some (.function original)), true⟩ &&
             final.runtime.heap[outerImport.address]? == some ⟨.binding (some (.function inner)), true⟩
           | _, _, _ => false) &&
          published.exports.lookup "held" == some (.function inner) &&
          published.exports.lookup "answer" == some (.list late) &&
          final.cache.map Prod.fst == [2, 1, 0] && final.runtime.iterators == [123]
        | _, _, _ => false
      | _, _, _, _, _ => false
    | _, _ => false
  | _ => false

private def wrapperChainFails (nested : Bool) (preload : Option Nat) : Bool :=
  match runChainCommands (middleWithWrapper true) (finalWrapperConsumer nested).commands preload with
  | some (.error (.initialization 2 (.runtime .indexTarget)) final, entered) =>
    let cell name := (entered.slots (globalSlot name)).bind (fun slot => final.runtime.heap[slot.address]?)
    let lists := final.runtime.heap.toList.filterMap fun cell =>
      match cell.contents, cell.frozen with | .list [.scalar (.int n)], false => some n | _, _ => none
    let cached := (final.cache.lookup 1).bind (fun moduleValue => moduleValue.exports.lookup "relay")
    cached.isSome && cell "held" == some ⟨.binding cached, false⟩ &&
    cell "answer" == some ⟨.binding none, false⟩ && cell "after" == some ⟨.binding none, false⟩ &&
    lists == [61, 44, 44, 88, 44] && final.cache.map Prod.fst == [1, 0] &&
    (final.runtime.slots (fileSlot "wrapped")).isNone && final.runtime.iterators == [123]
  | _ => false

#guard wrapperChainOK false none
#guard wrapperChainOK true none
#guard wrapperChainOK true (some 0)
#guard wrapperChainOK true (some 1)
#guard wrapperChainFails false none
#guard wrapperChainFails true none
#guard wrapperChainFails true (some 0)
#guard wrapperChainFails true (some 1)

open Imports (ImportBinding ImportSite OrderedConsumer)

private def leftLoad : ImportSite :=
  .single "left.star" "relay" "left" (by simp [Modules.isPublic, String.startsWith_string_eq_false_iff])

private def skippedLoad : ImportSite :=
  .single "skip.star" "relay" "skipped" (by simp [Modules.isPublic, String.startsWith_string_eq_false_iff])

private def rightFirst (missing : Bool) : ImportBinding :=
  ⟨if missing then "absentFirst" else "reexport", "rightExtra",
    by cases missing <;> simp [Modules.isPublic, String.startsWith_string_eq_false_iff]⟩

private def rightLast (missing : Bool) : ImportBinding :=
  ⟨if missing then "absentLast" else "relay", "right",
    by cases missing <;> simp [Modules.isPublic, String.startsWith_string_eq_false_iff]⟩

private def rightLoad (firstMissing lastMissing : Bool) : ImportSite :=
  ⟨"right.star", [rightFirst firstMissing, rightLast lastMissing], by simp⟩

private def diamondLoads (firstMissing lastMissing : Bool) : List ImportSite :=
  [leftLoad, rightLoad firstMissing lastMissing] ++ if firstMissing || lastMissing then [skippedLoad] else []

private def diamondGlobals : List String := ["wrapRight", "leftResult", "rightResult", "rightCopy", "after"]

private def diamondWrapper (firstMissing lastMissing : Bool) :
    Imports.WrapperDeclaration "right" ((diamondLoads firstMissing lastMissing).flatMap ImportSite.aliases) diamondGlobals where
  name := "wrapRight"
  target := by decide
  visible := by cases firstMissing <;> cases lastMissing <;> decide
  legalAlias := by decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := .empty
  selects := .enclosing (.enclosing (by change ¬ "right" ∈ ([] : List String); simp) (by cases firstMissing <;> cases lastMissing <;> decide)) .nil

private def diamondConsumer (firstMissing lastMissing : Bool) : OrderedConsumer where
  imports := diamondLoads firstMissing lastMissing
  globals := diamondGlobals
  body :=
    [.define (diamondWrapper firstMissing lastMissing),
     .invoke { callee := "left", declared := .inl (by cases firstMissing <;> cases lastMissing <;> decide), legal := by decide
               destination := "leftResult", destinationGlobal := by decide
               arguments := [], codes := [], reads := [], operands := .nil, keywords := .empty },
     .invoke { callee := "wrapRight", declared := .inr (by decide), legal := by decide
               destination := "rightResult", destinationGlobal := by decide
               arguments := [], codes := [], reads := [], operands := .nil, keywords := .empty },
     .assign "rightCopy" (by decide)
       (.read (by decide) (.owned (by cases firstMissing <;> cases lastMissing <;> decide))
         (.owned (by cases firstMissing <;> cases lastMissing <;> decide))) (.name "rightExtra"),
     .assign "after" (by decide) (.list (.int 199)) .forget]
  declared := rfl

private def diamondManifest (producer left right top : ResolvedModule) : Loader.Manifest :=
  #[⟨producer.source, []⟩, ⟨left.source, [("prodé.star", 0)]⟩,
    ⟨right.source, [("prodé.star", 0)]⟩, ⟨right.source, [("prodé.star", 0)]⟩,
    ⟨top.source, [("left.star", 1), ("right.star", 2), ("skip.star", 3)]⟩]

private def diamondEnv (left right : Callee) : Imports.Tracked :=
  Imports.track (Imports.track (Imports.initial "left" left) "right" (some right)) "rightExtra"
    (some (.regular (.nested returned)))

private def diamondExports (firstMissing lastMissing : Bool) (origin second last : Program) :
    Loader.ModuleId → Imports.Tracked
  | 0 => Imports.Chain.rootExports exports
  | 1 => Imports.Chain.exportsOf middleConsumer origin (.regular (.nested returned))
  | 2 | 3 => Imports.Chain.exportsOf middleConsumer second (.regular (.nested returned))
  | _ => if firstMissing || lastMissing then fun _ => none else fun name =>
    if name ∈ diamondGlobals then
      Imports.trackSuite last
        (diamondEnv (.wrapper middleWrapper origin.size (.regular (.nested returned)))
          (.wrapper middleWrapper second.size (.regular (.nested returned)))) (diamondConsumer false false).body name
    else none

private def checkedDiamond (firstMissing lastMissing : Bool) {producer left right top : ResolvedModule}
    (rootChecked : resolve (commands false) #[] = .ok producer)
    (leftChecked : resolve middleConsumer.commands producer.program = .ok left)
    (rightChecked : resolve middleConsumer.commands left.program = .ok right)
    (topChecked : resolve (diamondConsumer firstMissing lastMissing).commands right.program = .ok top) :
    Imports.Chain.Graph producer.program (diamondManifest producer left right top) := by
  have rootSize : producer.program.size = 2 := by
    rw [(plan_code (commands := commands false) (plan false) rootChecked).2]; rfl
  have leftSize : left.program.size = producer.program.size + 1 := by
    rw [(Imports.consumer_layout middleConsumer leftChecked).1]
    change (producer.program.push middleWrapper.site.declaration).size = _
    simp
  have rightSize : right.program.size = left.program.size + 1 := by
    rw [(Imports.consumer_layout middleConsumer rightChecked).1]
    change (left.program.push middleWrapper.site.declaration).size = _
    simp
  have throughLeft := Imports.consumer_preserves middleConsumer leftChecked
  have throughRight := Imports.consumer_preserves middleConsumer rightChecked
  have throughTop := Imports.ordered_preserves (diamondConsumer firstMissing lastMissing) topChecked
  let linked := diamondExports firstMissing lastMissing producer.program left.program right.program
  let original := Callee.regular (.nested returned)
  let leftWrapper := Callee.wrapper middleWrapper producer.program.size original
  let rightWrapper := Callee.wrapper middleWrapper left.program.size original
  have branchReady (program : Program) (rank : 0 < program.size) :
      Imports.Chain.Demand middleConsumer program (Imports.Chain.rootExports exports) producer.source
        (Imports.Chain.exportsOf middleConsumer program original) :=
    .found original rfl rank ⟨original, rfl, rank, .wrapper middleWrapper program.size original, rfl, trivial⟩
  refine ⟨(diamondConsumer firstMissing lastMissing).commands, right.program, top, topChecked,
    fun index decl saved => throughTop _ _ (throughRight _ _ (throughLeft index decl saved)), linked, ?_⟩
  intro id bound
  have range : id = 0 ∨ id = 1 ∨ id = 2 ∨ id = 3 ∨ id = 4 := by
    change id < 5 at bound
    omega
  rcases range with rfl | rfl | rfl | rfl | rfl
  · exact .root (commands := commands false) (plan false) rfl rootChecked (fun _ _ seen => seen) rfl
  · exact .importer middleConsumer (show 0 < 1 by decide) leftChecked (fun _ _ seen => seen)
      (fun _ _ seen => throughTop _ _ (throughRight _ _ seen)) rfl rfl (branchReady _ (by omega))
  · exact .importer middleConsumer (show 0 < 2 by decide) rightChecked throughLeft
      throughTop rfl rfl (branchReady _ (by omega))
  · exact .importer middleConsumer (show 0 < 3 by decide) rightChecked throughLeft
      throughTop rfl rfl (branchReady _ (by omega))
  · have prefixOrigin : Defaults.Nested.Sequence.PreservesDeclarations producer.program right.program :=
      fun _ _ seen => throughRight _ _ (throughLeft _ _ seen)
    have absentFirst : "absentFirst" ∉ right.source.globals := by
      rw [(Imports.consumer_layout middleConsumer rightChecked).2.2.1]
      decide
    have absentLast : "absentLast" ∉ right.source.globals := by
      rw [(Imports.consumer_layout middleConsumer rightChecked).2.2.1]
      decide
    have start {tail : List ImportSite} {final : Option Imports.Tracked}
        (rest : Imports.Chain.ImportPlan (diamondManifest producer left right top) linked 4 bound
          tail (Imports.initial "left" leftWrapper) final) :
        Imports.Chain.ImportPlan (diamondManifest producer left right top) linked 4 bound (leftLoad :: tail)
          (fun _ => none) final :=
      .load (dependency := 1) (by decide) rfl (.found leftWrapper rfl (.done _))
        (fun _ equal => by cases equal; exact rest) (by simp)
    cases firstMissing <;> cases lastMissing
    · refine .ordered (finalEnv := some (diamondEnv leftWrapper rightWrapper)) (diamondConsumer false false) topChecked
        prefixOrigin (fun _ _ seen => seen) rfl ?_ ?_
      · apply start
        exact .load (dependency := 2) (by decide) rfl
          (.found rightWrapper rfl (.found original rfl (.done _)))
          (fun _ equal => by cases equal; exact .done _) (by simp)
      · exact ⟨⟨rightWrapper, rfl, by change left.program.size < right.program.size; omega,
          leftWrapper, rfl, .wrapper (diamondWrapper false false) right.program.size rightWrapper, rfl, trivial⟩, rfl⟩
    · refine .ordered (finalEnv := none) (diamondConsumer false true) topChecked prefixOrigin (fun _ _ seen => seen) rfl ?_ rfl
      apply start
      exact .load (dependency := 2) (by decide) rfl (.missing absentLast) (by simp) (fun _ => rfl)
    · refine .ordered (finalEnv := none) (diamondConsumer true false) topChecked prefixOrigin (fun _ _ seen => seen) rfl ?_ rfl
      apply start
      exact .load (dependency := 2) (by decide) rfl (.found rightWrapper rfl (.missing absentFirst))
        (by simp) (fun _ => rfl)
    · refine .ordered (finalEnv := none) (diamondConsumer true true) topChecked prefixOrigin (fun _ _ seen => seen) rfl ?_ rfl
      apply start
      exact .load (dependency := 2) (by decide) rfl (.missing absentLast) (by simp) (fun _ => rfl)

example (firstMissing lastMissing : Bool) {producer left right top : ResolvedModule}
    (rootChecked : resolve (commands false) #[] = .ok producer)
    (leftChecked : resolve middleConsumer.commands producer.program = .ok left)
    (rightChecked : resolve middleConsumer.commands left.program = .ok right)
    (topChecked : resolve (diamondConsumer firstMissing lastMissing).commands right.program = .ok top)
    (caller : Lists.State) (history : List Nat) (bounded : ∀ id ∈ history, id < 5) :
    let graph := checkedDiamond firstMissing lastMissing rootChecked leftChecked rightChecked topChecked
    ∃ entered out, Imports.Chain.Requests graph history ⟨caller, []⟩ entered ∧
      Imports.Chain.TraceRun (diamondManifest producer left right top) 4 entered out ∧
      Loader.load top.program (diamondManifest producer left right top) 4 entered = out ∧
      Imports.Chain.Reached producer.program top.program (diamondManifest producer left right top)
        graph.exports 4 entered out := by
  intro graph
  obtain ⟨entered, historyRun, valid⟩ := Imports.Chain.requests graph history bounded ⟨caller, []⟩
    (fun _ _ impossible => nomatch impossible)
  obtain ⟨out, source, _, meaning, reached⟩ := Imports.Chain.agrees graph 4 (by change 4 < 5; decide) entered valid
  exact ⟨entered, out, historyRun, source, meaning, reached⟩

private def runDiamond (firstMissing lastMissing : Bool) (preload : Bool) :
    Option (Loader.Result Modules.Published × Lists.State × Lists.State) := do
  let producer ← (resolve (commands false)).toOption
  let left ← (resolve middleConsumer.commands producer.program).toOption
  let right ← (resolve middleConsumer.commands left.program).toOption
  let top ← (resolve (diamondConsumer firstMissing lastMissing).commands right.program).toOption
  let manifest := diamondManifest producer left right top
  let caller := globalSlot "caller"
  let cold : Loader.Session := {runtime := {
    heap := #[⟨.binding (some (.scalar (.int 73))), false⟩]
    bindings := fun name => if name == caller then some (.scalar (.int 7)) else none
    slots := fun name => if name == caller then some (.owned 0) else none
    iterators := [0] }}
  let reached ← if preload then
      match Loader.load top.program manifest 1 cold with
      | .ok _ reached => some reached
      | .error .. => none
    else some cold
  some (Loader.load top.program manifest 4 reached, enter top.source reached.runtime, reached.runtime)

private def capturedImport (heap : Lists.Heap) (wrapper target : Lists.Value) (index : Nat) : Bool :=
  match wrapper with
  | .function address =>
    match heap[address]? with
    | some ⟨.function record, true⟩ =>
      record.declaration == index &&
        (match record.captures with
         | [capture] => heap[capture.address]? == some ⟨.binding (some target), true⟩
         | _ => false)
    | _ => false
  | _ => false

private def callerRestored (caller final : Lists.State) : Bool :=
  let name := globalSlot "caller"
  final.slots name == caller.slots name &&
    final.bindings name == caller.bindings name &&
    final.heap[0]? == caller.heap[0]? &&
    final.slots (fileSlot "right") == none && final.iterators == caller.iterators

private def importCell (entered final : Lists.State) (slot : Binding) : Option Lists.Cell :=
  (entered.slots slot).bind (fun address => final.heap[address.address]?)

private def diamondOK (warm : Bool) : Bool :=
  match runDiamond false false warm with
  | some (.ok result final, entered, caller) =>
    match final.cache.lookup 0, final.cache.lookup 1, final.cache.lookup 2 with
    | some producer, some left, some right =>
      match producer.exports.lookup "escaped", producer.exports.lookup "late", left.exports.lookup "relay",
          right.exports.lookup "relay", result.exports.lookup "wrapRight" with
      | some escaped, some late, some left, some right, some wrapper =>
        left != right && capturedImport final.runtime.heap left escaped 2 &&
        capturedImport final.runtime.heap right escaped 3 && capturedImport final.runtime.heap wrapper right 4 &&
        result.exports.lookup "leftResult" == some late && result.exports.lookup "rightResult" == some late &&
        importCell entered final.runtime (fileSlot "rightExtra") == some ⟨.binding (some escaped), false⟩ &&
        importCell entered final.runtime (fileSlot "right") == some ⟨.binding (some right), true⟩ &&
        result.exports.lookup "left" == none && result.exports.lookup "right" == none &&
        result.exports.lookup "rightExtra" == none && result.exports.lookup "rightCopy" == some escaped &&
        final.cache.map Prod.fst == [4, 2, 1, 0] && callerRestored caller final.runtime
      | _, _, _, _, _ => false
    | _, _, _ => false
  | _ => false

private def diamondError (firstMissing lastMissing warm : Bool) (name : String) : Bool :=
  match runDiamond firstMissing lastMissing warm with
  | some (.error (.initialization 4 (.missingExport "right.star" missing)) final, frame, caller) =>
    match final.cache.lookup 1 with
    | some left =>
      match left.exports.lookup "relay" with
      | some relay =>
        missing == name &&
        importCell frame final.runtime (fileSlot "left") == some ⟨.binding (some relay), false⟩ &&
        [fileSlot "right", fileSlot "rightExtra", fileSlot "skipped", globalSlot "wrapRight",
          globalSlot "leftResult", globalSlot "rightResult", globalSlot "rightCopy", globalSlot "after"].all (fun slot =>
          importCell frame final.runtime slot == some ⟨.binding none, false⟩) &&
        final.cache.map Prod.fst == [2, 1, 0] && callerRestored caller final.runtime
      | none => false
    | none => false
  | _ => false

#guard diamondOK false
#guard diamondOK true
#guard diamondError true false false "absentFirst"
#guard diamondError true false true "absentFirst"
#guard diamondError false true false "absentLast"
#guard diamondError false true true "absentLast"
#guard diamondError true true false "absentLast"
#guard diamondError true true true "absentLast"

private def positionalGlobals : List String := ["spare", "pick"]

private def spareSite : Site (moduleLex positionalGlobals) [] none none .global where
  name := "spare"
  target := by decide
  parameters := ⟨[], []⟩
  source := .ret (some starlark%[999])
  binders := []
  locals := []
  collects := .ret _
  localOrder := .nil
  body := ⟨.returnExpr (int 999), []⟩
  free := []
  selects := .nil
  defaults := []
  lexical := .nil

private def spareRoot : Root positionalGlobals where
  keywords := []
  varargs := none
  kwargs := none
  site := spareSite
  lexical := .nil
  seed := #[]
  bodyTable := #[]
  children := []
  suite := .plain (.straight (source := .ret starlark%[999]) (.ret (.int 999)))

private def pickBody : Body.Suite :=
  .assign "probe" starlark%[[first]] (.ret starlark%[probe[second]])

private def pickSite : Site (moduleLex positionalGlobals) [] none none .global where
  name := "pick"
  target := by decide
  parameters := ⟨["first", "second"], []⟩
  source := pickBody.source
  binders := ["probe"]
  locals := ["probe"]
  collects := .seq (.assign _ _) (.ret _)
  localOrder := .keep (by decide) .nil
  body := ⟨.seq (.assignExpr (fileSlot "probe") (.list [localRead "first"]))
      (.returnExpr (.index (localRead "probe") (localRead "second"))),
    [fileSlot "first", fileSlot "probe", fileSlot "second"]⟩
  free := []
  selects := .owned (.owned (by decide)) (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil))
  defaults := []
  lexical := .nil

private def pickRoot : Root positionalGlobals where
  keywords := []
  varargs := none
  kwargs := none
  site := pickSite
  lexical := .nil
  seed := spareRoot.table
  bodyTable := spareRoot.table
  children := []
  suite := .plain (.straight (source := pickBody) (.assign (by decide)
    (.list (.read (by decide) (.owned (by decide)) (.owned (by decide))))
    (.ret (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
      (.read (by decide) (.owned (by decide)) (.owned (by decide)))))))

private def positionalCommands : List Resolve.Command := [spareRoot.command, pickRoot.command]

private def positionalExports : Environment :=
  update (update (fun _ => none) "spare" (some spareRoot.callable)) "pick" (some pickRoot.callable)

private theorem positionalPlan : Plan (Trace.names positionalCommands) (fun _ => none)
    positionalCommands #[] [.exec (.define "spare" 0), .exec (.define "pick" 1)] pickRoot.table positionalExports :=
  .define spareRoot (.define pickRoot .done)

private def forwardingLoad : ImportSite :=
  ⟨"positional.star",
    [⟨"spare", "ignored", by simp [Modules.isPublic, String.startsWith_string_eq_false_iff]⟩,
     ⟨"pick", "loaded", by simp [Modules.isPublic, String.startsWith_string_eq_false_iff]⟩], by simp⟩

private def forwardingWrapper : Imports.WrapperDeclaration "loaded" forwardingLoad.aliases ["relay"] where
  name := "relay"
  target := by decide
  visible := by decide
  legalAlias := by decide
  parameters := ⟨["x", "y"], []⟩
  unshadowed := by decide
  arguments := [starlark%[y], starlark%[x]]
  codes := [localRead "y", localRead "x"]
  reads := [fileSlot "y", fileSlot "x"]
  operands := .cons (.read (by decide) (.owned (by decide)) (.owned (by decide)))
    (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil)
  keywords := .empty
  selects := .enclosing (.enclosing (by decide) (by decide))
    (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil))

example (x y : Lists.Value) (checked : forwardingWrapper.site.declaration.signature.validate = .ok ()) :
    Functions.bindArguments forwardingWrapper.site.declaration.signature [] ⟨[x, y], []⟩ =
      .ok ⟨[(fileSlot "x", x), (fileSlot "y", y)], [], []⟩ :=
  Imports.wrapper_positional_binding forwardingWrapper rfl rfl rfl checked (.success (.cons (.cons .nil)))

private def forwarder : OrderedConsumer where
  imports := [forwardingLoad]
  globals := ["relay"]
  body := [.define forwardingWrapper]
  declared := rfl

private inductive ForwardTest where
  | success | arity | body
  deriving DecidableEq

private def downstreamLoad : ImportSite :=
  .single "forwarder.star" "relay" "bound" (by simp [Modules.isPublic, String.startsWith_string_eq_false_iff])

private def downstreamGlobals : List String := ["firstResult", "marker", "out", "after"]

private def downstreamCall (first : Bool) (test : ForwardTest) :
    Imports.Invocation downstreamLoad.aliases downstreamGlobals where
  callee := "bound"
  declared := .inl (by decide)
  legal := by decide
  destination := if first then "firstResult" else "out"
  destinationGlobal := by cases first <;> decide
  arguments := if first then [starlark%[0], starlark%[27]]
    else match test with
    | .success => [starlark%[0], starlark%[53]]
    | .arity => [starlark%[0], starlark%[39], starlark%[55]]
    | .body => [starlark%[1], starlark%[39]]
  codes := if first then [int 0, int 27]
    else match test with
    | .success => [int 0, int 53]
    | .arity => [int 0, int 39, int 55]
    | .body => [int 1, int 39]
  reads := []
  operands := by cases first <;> cases test <;> first
    | exact .cons (.int _) (.cons (.int _) .nil)
    | exact .cons (.int _) (.cons (.int _) (.cons (.int _) .nil))
  keywords := .empty

private def downstream (test : ForwardTest) : OrderedConsumer where
  imports := [downstreamLoad]
  globals := downstreamGlobals
  body :=
    [.invoke (downstreamCall true test),
     .assign "marker" (by decide) (.list (.int 88)) .forget,
     .invoke (downstreamCall false test),
     .assign "after" (by decide) (.list (.int 199)) .forget]
  declared := rfl

private def positionalManifest (producer middle consumer : ResolvedModule) : Loader.Manifest :=
  #[⟨producer.source, []⟩, ⟨middle.source, [("positional.star", 0)]⟩, ⟨consumer.source, [("forwarder.star", 1)]⟩]

private def forwardingEnv : Imports.Tracked :=
  Imports.track (Imports.initial "loaded" (.regular pickRoot.callable)) "ignored" (some (.regular spareRoot.callable))

private def checkedForwarding (test : ForwardTest) {producer middle consumer : ResolvedModule}
    (prod : resolve positionalCommands #[] = .ok producer)
    (mid : resolve forwarder.commands producer.program = .ok middle)
    (top : resolve (downstream test).commands middle.program = .ok consumer) :
    Imports.Chain.Graph producer.program (positionalManifest producer middle consumer) := by
  let wrapper := Callee.wrapper forwardingWrapper producer.program.size (.regular pickRoot.callable)
  let env : Loader.ModuleId → Imports.Tracked
    | 0 => Imports.Chain.rootExports positionalExports
    | 1 => fun name => if name ∈ forwarder.globals then Imports.trackSuite producer.program forwardingEnv forwarder.body name else none
    | _ => fun _ => none
  have throughMiddle := Imports.ordered_preserves forwarder mid
  have throughTop := Imports.ordered_preserves (downstream test) top
  have producerSize : producer.program.size = 2 := by rw [(plan_code positionalPlan prod).2]; rfl
  refine ⟨(downstream test).commands, middle.program, consumer, top,
    fun index decl found => throughTop _ _ (throughMiddle index decl found), env, ?_⟩
  intro id bound
  have range : id = 0 ∨ id = 1 ∨ id = 2 := by change id < 3 at bound; omega
  rcases range with rfl | rfl | rfl
  · exact .root positionalPlan rfl prod (fun _ _ found => found) rfl
  · refine .ordered (finalEnv := some forwardingEnv) forwarder mid (fun _ _ found => found)
      throughTop rfl ?_ ?_
    · exact .load (dependency := 0) (by decide) rfl
        (.found (.regular pickRoot.callable) rfl (.found (.regular spareRoot.callable) rfl (.done _)))
        (fun _ equal => by cases equal; exact .done _) (by simp)
    · exact ⟨⟨.regular pickRoot.callable, rfl, by change 1 < producer.program.size; omega, trivial⟩, rfl⟩
  · refine .ordered (finalEnv := some (Imports.initial "bound" wrapper)) (downstream test) top throughMiddle
      (fun _ _ found => found) rfl ?_ ?_
    · exact .load (dependency := 1) (by decide) rfl (.found wrapper rfl (.done _))
        (fun _ equal => by cases equal; exact .done _) (by simp)
    · refine ⟨⟨wrapper, rfl, wrapper, rfl, trivial⟩, ?_⟩
      funext name
      change (none : Option Callee) = _
      by_cases isAlias : name = "bound"
      · subst name
        rfl
      · simp [downstream, downstreamGlobals, downstreamCall, Imports.trackSuite, Imports.Step.advance,
          Imports.Copy.track, Imports.initial, Imports.track, isAlias, wrapper, Callee.returned, Root.callable, pickRoot]


example (test : ForwardTest) {producer middle consumer : ResolvedModule}
    (prod : resolve positionalCommands #[] = .ok producer)
    (mid : resolve forwarder.commands producer.program = .ok middle)
    (top : resolve (downstream test).commands middle.program = .ok consumer)
    (caller : Lists.State) (history : List Nat) (bounded : ∀ id ∈ history, id < 3) :
    let graph := checkedForwarding test prod mid top
    ∃ entered out, Imports.Chain.Requests graph history ⟨caller, []⟩ entered ∧
      Imports.Chain.TraceRun (positionalManifest producer middle consumer) 2 entered out ∧
      Loader.load consumer.program (positionalManifest producer middle consumer) 2 entered = out ∧
      Imports.Chain.Reached producer.program consumer.program (positionalManifest producer middle consumer)
        graph.exports 2 entered out := by
  intro graph
  obtain ⟨entered, requests, valid⟩ := Imports.Chain.requests graph history bounded ⟨caller, []⟩
    (fun _ _ impossible => nomatch impossible)
  obtain ⟨out, source, _, meaning, reached⟩ := Imports.Chain.agrees graph 2 (by change 2 < 3; decide) entered valid
  exact ⟨entered, out, requests, source, meaning, reached⟩

private def forwardingCaller : Lists.State :=
  let key := globalSlot "caller"
  { heap := #[⟨.binding (some (.scalar (.int 73))), false⟩]
    slots := fun name => if name == key then some (.owned 0) else none
    bindings := fun name => if name == key then some (.scalar (.int 7)) else none
    iterators := [0] }

private def runForwarding (test : ForwardTest) (warm : Bool) :
    Option (Loader.Result Modules.Published × Lists.State × Lists.State) := do
  let producer ← (resolve positionalCommands).toOption
  let middle ← (resolve forwarder.commands producer.program).toOption
  let consumer ← (resolve (downstream test).commands middle.program).toOption
  let manifest := positionalManifest producer middle consumer
  let cold : Loader.Session := {runtime := forwardingCaller}
  let entry ← if warm then
      match Loader.load consumer.program manifest 1 cold with
      | .ok _ ready => some ready
      | .error .. => none
    else some cold
  some (Loader.load consumer.program manifest 2 entry, enter consumer.source entry.runtime, entry.runtime)

private def forwardingRecord (session : Loader.Session) : Bool :=
  match session.cache.lookup 0, session.cache.lookup 1 with
  | some producer, some middle =>
    match producer.exports.lookup "spare", producer.exports.lookup "pick", middle.exports.lookup "relay" with
    | some spare, some pick, some relay =>
      spare != pick && capturedImport session.runtime.heap relay pick 2
    | _, _, _ => false
  | _, _ => false

private def forwardingSuccess (warm : Bool) : Bool :=
  match runForwarding .success warm with
  | some (.ok published final, _, caller) =>
    published.exports.lookup "firstResult" == some (.scalar (.int 27)) &&
      published.exports.lookup "out" == some (.scalar (.int 53)) &&
      final.cache.map Prod.fst == [2, 1, 0] && forwardingRecord final &&
      callerRestored caller final.runtime && (final.runtime.slots (fileSlot "bound")).isNone
  | _ => false

private def forwardingFailure (test : ForwardTest) (warm : Bool) : Bool :=
  match runForwarding test warm with
  | some (.error (.initialization 2 (.runtime error)) final, frame, caller) =>
    let selectedError := match test, error with
      | .arity, .arity 2 3 | .body, .indexRange 1 1 => true
      | _, _ => false
    let listCells := final.runtime.heap.toList.filterMap fun cell => match cell.contents with
      | .list [.scalar (.int value)] => some (value, cell.frozen)
      | _ => none
    selectedError &&
      importCell frame final.runtime (globalSlot "firstResult") == some ⟨.binding (some (.scalar (.int 27))), false⟩ &&
      [globalSlot "out", globalSlot "after"].all (fun slot =>
        importCell frame final.runtime slot == some ⟨.binding none, false⟩) &&
      listCells == (if test == .arity then [(27, false), (88, false)] else [(27, false), (88, false), (39, false)]) &&
      final.runtime.heap.size == (if test == .arity then 21 else 27) &&
      final.cache.map Prod.fst == [1, 0] && forwardingRecord final &&
      callerRestored caller final.runtime && (final.runtime.slots (fileSlot "bound")).isNone
  | _ => false

#guard forwardingSuccess false
#guard forwardingSuccess true
#guard forwardingFailure .arity false
#guard forwardingFailure .arity true
#guard forwardingFailure .body false
#guard forwardingFailure .body true

private def savedGlobals : List String := ["seed", "before", "relay", "later"]

private def savedParameters (bad : Bool) : Parameters :=
  ⟨["x"], [("y", starlark%[[seed]]),
    ("z", if bad then starlark%[[51][1]] else starlark%[[51][0]]),
    ("t", if bad then starlark%[[72][2]] else starlark%[[72][0]])]⟩

private def savedDefaults (bad : Bool) : List PlainPositionalDefault :=
  [⟨"y", starlark%[[seed]], .list [globalRead "seed"], [globalSlot "seed"]⟩,
   ⟨"z", if bad then starlark%[[51][1]] else starlark%[[51][0]],
     .index (boxed 51) (int (if bad then 1 else 0)), []⟩,
   ⟨"t", if bad then starlark%[[72][2]] else starlark%[[72][0]],
     .index (boxed 72) (int (if bad then 2 else 0)), []⟩]

private def savedWrapper (bad : Bool) : Imports.WrapperDeclaration "loaded" forwardingLoad.aliases savedGlobals where
  name := "relay"
  target := by decide
  visible := by decide
  legalAlias := by decide
  parameters := savedParameters bad
  unshadowed := by cases bad <;> decide
  defaults := savedDefaults bad
  lexical := by
    have seedRead : Body.Operand (Imports.block forwardingLoad.aliases savedGlobals)
        starlark%[seed] (globalRead "seed") [globalSlot "seed"] :=
      .read (by decide) (.global (by decide) (by decide) (by decide))
        (.module (by decide) (by decide) (by decide))
    cases bad <;> exact .cons (.list seedRead)
      (.cons (.index (.list (.int 51)) (.int _)) (.cons (.index (.list (.int 72)) (.int _)) .nil))
  arguments := [starlark%[y[0]], starlark%[x]]
  codes := [.index (localRead "y") (int 0), localRead "x"]
  reads := [fileSlot "y", fileSlot "x"]
  operands := by
    cases bad <;> exact .cons (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0))
      (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil)
  keywords := .empty
  selects := by
    cases bad <;> exact .enclosing (.enclosing (by decide) (by decide))
      (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil))

private def relayWithSetup (wrapper : Imports.WrapperDeclaration "loaded" forwardingLoad.aliases savedGlobals)
    (named : wrapper.name = "relay") : OrderedConsumer where
  imports := [forwardingLoad]
  globals := savedGlobals
  body :=
    [.assign "seed" (by decide) (.int 27) .forget,
     .assign "before" (by decide) (.list (.int 76)) .forget,
     .define wrapper,
     .assign "later" (by decide) (.list (.int 199)) .forget]
  declared := by simp [Imports.Step.destination, savedGlobals, named]

private def savedForwarder (bad : Bool) : OrderedConsumer :=
  relayWithSetup (savedWrapper bad) rfl

private inductive SavedTest where
  | success | missing | surplus | defaultError
  deriving DecidableEq

private inductive SavedActuals where
  | omitted | explicit | missing | surplus

private def savedDownstreamGlobals : List String := ["firstResult", "marker", "out", "again", "after"]

private def savedCall (destination : String) (declared : destination ∈ savedDownstreamGlobals)
    (mode : SavedActuals) : Imports.Invocation downstreamLoad.aliases savedDownstreamGlobals where
  callee := "bound"
  declared := .inl (by decide)
  legal := by decide
  destination := destination
  destinationGlobal := declared
  arguments := match mode with
    | .omitted => [starlark%[0]]
    | .explicit => [starlark%[0], starlark%[[53]]]
    | .missing => []
    | .surplus => [starlark%[0], starlark%[[53]], starlark%[1], starlark%[2], starlark%[3]]
  codes := match mode with
    | .omitted => [int 0]
    | .explicit => [int 0, boxed 53]
    | .missing => []
    | .surplus => [int 0, boxed 53, int 1, int 2, int 3]
  reads := []
  operands := by
    cases mode with
    | omitted => exact .cons (.int 0) .nil
    | explicit => exact .cons (.int 0) (.cons (.list (.int 53)) .nil)
    | missing => exact .nil
    | surplus => exact .cons (.int 0) (.cons (.list (.int 53)) (.cons (.int 1) (.cons (.int 2) (.cons (.int 3) .nil))))
  keywords := .empty

private def savedDownstream (test : SavedTest) : OrderedConsumer where
  imports := [downstreamLoad]
  globals := savedDownstreamGlobals
  body :=
    [.invoke (savedCall "firstResult" (by decide) .omitted),
     .assign "marker" (by decide) (.list (.int 88)) .forget,
     .invoke (savedCall "out" (by decide) (match test with
       | .missing => .missing
       | .surplus => .surplus
       | _ => .explicit)),
     .invoke (savedCall "again" (by decide) .omitted),
     .assign "after" (by decide) (.list (.int 198)) .forget]
  declared := rfl

private def checkedSaved (test : SavedTest) {producer middle consumer : ResolvedModule}
    (prod : resolve positionalCommands #[] = .ok producer)
    (mid : resolve (savedForwarder (test = .defaultError)).commands producer.program = .ok middle)
    (top : resolve (savedDownstream test).commands middle.program = .ok consumer) :
    Imports.Chain.Graph producer.program (positionalManifest producer middle consumer) := by
  let forwarder := savedForwarder (test = .defaultError)
  let wrapper := Callee.wrapper (savedWrapper (test = .defaultError)) producer.program.size (.regular pickRoot.callable)
  let env : Loader.ModuleId → Imports.Tracked
    | 0 => Imports.Chain.rootExports positionalExports
    | 1 => fun name => if name ∈ forwarder.globals then Imports.trackSuite producer.program forwardingEnv forwarder.body name else none
    | _ => fun _ => none
  have throughMiddle := Imports.ordered_preserves forwarder mid
  have throughTop := Imports.ordered_preserves (savedDownstream test) top
  have producerSize : producer.program.size = 2 := by rw [(plan_code positionalPlan prod).2]; rfl
  refine ⟨(savedDownstream test).commands, middle.program, consumer, top,
    fun index decl found => throughTop _ _ (throughMiddle index decl found), env, ?_⟩
  intro id bound
  have range : id = 0 ∨ id = 1 ∨ id = 2 := by change id < 3 at bound; omega
  rcases range with rfl | rfl | rfl
  · exact .root positionalPlan rfl prod (fun _ _ found => found) rfl
  · refine .ordered (finalEnv := some forwardingEnv) forwarder mid (fun _ _ found => found)
      throughTop rfl ?_ ?_
    · exact .load (dependency := 0) (by decide) rfl
        (.found (.regular pickRoot.callable) rfl (.found (.regular spareRoot.callable) rfl (.done _)))
        (fun _ equal => by cases equal; exact .done _) (by simp)
    · exact ⟨⟨.regular pickRoot.callable, rfl, by change 1 < producer.program.size; omega, trivial⟩, rfl⟩
  · refine .ordered (finalEnv := some (Imports.initial "bound" wrapper)) (savedDownstream test) top throughMiddle
      (fun _ _ found => found) rfl ?_ ?_
    · exact .load (dependency := 1) (by decide) rfl (.found wrapper rfl (.done _))
        (fun _ equal => by cases equal; exact .done _) (by simp)
    · refine ⟨⟨wrapper, rfl, wrapper, rfl, wrapper, rfl, trivial⟩, ?_⟩
      funext name
      change (none : Option Callee) = _
      by_cases isAlias : name = "bound"
      · subst name
        rfl
      · simp [savedDownstream, savedDownstreamGlobals, savedCall, Imports.trackSuite, Imports.Step.advance,
          Imports.Copy.track, Imports.initial, Imports.track, isAlias, wrapper, Callee.returned, Root.callable, pickRoot]

example (test : SavedTest) {producer middle consumer : ResolvedModule}
    (prod : resolve positionalCommands #[] = .ok producer)
    (mid : resolve (savedForwarder (test = .defaultError)).commands producer.program = .ok middle)
    (top : resolve (savedDownstream test).commands middle.program = .ok consumer)
    (caller : Lists.State) (history : List Nat) (bounded : ∀ id ∈ history, id < 3) :
    let graph := checkedSaved test prod mid top
    ∃ entered out, Imports.Chain.Requests graph history ⟨caller, []⟩ entered ∧
      Imports.Chain.TraceRun (positionalManifest producer middle consumer) 2 entered out ∧
      Loader.load consumer.program (positionalManifest producer middle consumer) 2 entered = out ∧
      Imports.Chain.Reached producer.program consumer.program (positionalManifest producer middle consumer)
        graph.exports 2 entered out := by
  intro graph
  obtain ⟨entered, requests, valid⟩ := Imports.Chain.requests graph history bounded ⟨caller, []⟩
    (fun _ _ impossible => nomatch impossible)
  obtain ⟨out, source, _, meaning, reached⟩ := Imports.Chain.agrees graph 2 (by change 2 < 3; decide) entered valid
  exact ⟨entered, out, requests, source, meaning, reached⟩

private def savedRun (test : SavedTest) (warm : Bool) :
    Option (Loader.Result Modules.Published × Lists.State × Lists.State × Lists.State) := do
  let producer ← (resolve positionalCommands).toOption
  let middle ← (resolve (savedForwarder (test = .defaultError)).commands producer.program).toOption
  let consumer ← (resolve (savedDownstream test).commands middle.program).toOption
  let manifest := positionalManifest producer middle consumer
  let cold : Loader.Session := {runtime := forwardingCaller}
  let entry ← if warm then
      match Loader.load consumer.program manifest (if test = .defaultError then 0 else 1) cold with
      | .ok _ ready => some ready
      | .error .. => none
    else some cold
  let outer := enter consumer.source entry.runtime
  let middleFrame := enter middle.source outer
  some (Loader.load consumer.program manifest 2 entry, outer, middleFrame, entry.runtime)

private def singletonInts (state : Lists.State) : List Int :=
  state.heap.toList.filterMap fun cell => match cell.contents with
    | .list [.scalar (.int value)] => some value
    | _ => none

private def savedRecord (session : Loader.Session) : Bool :=
  match (session.cache.lookup 1).bind (fun value => value.exports.lookup "relay") with
  | some (.function address) =>
    match session.runtime.heap[address]? with
    | some ⟨.function record, true⟩ =>
      match record.defaults with
      | [(first, .list saved), (second, .scalar (.int 51)), (third, .scalar (.int 72))] =>
        first == fileSlot "y" && second == fileSlot "z" && third == fileSlot "t" &&
          session.runtime.heap[saved]? == some ⟨.list [.scalar (.int 27)], true⟩ && forwardingRecord session
      | _ => false
    | _ => false
  | _ => false

private def savedSuccess (warm : Bool) : Bool :=
  match savedRun .success warm with
  | some (.ok published final, _, _, caller) =>
    published.exports.lookup "firstResult" == some (.scalar (.int 27)) &&
      published.exports.lookup "out" == some (.scalar (.int 53)) &&
      published.exports.lookup "again" == some (.scalar (.int 27)) &&
      singletonInts final.runtime == [76, 27, 51, 72, 199, 27, 88, 53, 53, 27, 198] &&
      final.cache.map Prod.fst == [2, 1, 0] && savedRecord final && callerRestored caller final.runtime
  | _ => false

private def savedCallFailure (test : SavedTest) (warm : Bool) : Bool :=
  match savedRun test warm with
  | some (.error (.initialization 2 (.runtime error)) final, frame, _, caller) =>
    let correct := match test, error with
      | .missing, .missingArguments ["x"] | .surplus, .arity 4 5 => true
      | _, _ => false
    correct &&
      importCell frame final.runtime (globalSlot "firstResult") == some ⟨.binding (some (.scalar (.int 27))), false⟩ &&
      [globalSlot "out", globalSlot "again", globalSlot "after"].all (fun slot =>
        importCell frame final.runtime slot == some ⟨.binding none, false⟩) &&
      singletonInts final.runtime == (if test == .missing then [76, 27, 51, 72, 199, 27, 88]
        else [76, 27, 51, 72, 199, 27, 88, 53]) &&
      final.cache.map Prod.fst == [1, 0] && savedRecord final && callerRestored caller final.runtime
  | _ => false

private def savedDefaultFailure (warm : Bool) : Bool :=
  match savedRun .defaultError warm with
  | some (.error (.initialization 1 (.runtime (.indexRange 1 1))) final, outer, middle, caller) =>
    importCell middle final.runtime (globalSlot "seed") == some ⟨.binding (some (.scalar (.int 27))), false⟩ &&
      [globalSlot "relay", globalSlot "later"].all (fun slot =>
        importCell middle final.runtime slot == some ⟨.binding none, false⟩) &&
      [fileSlot "bound", globalSlot "firstResult", globalSlot "marker", globalSlot "out",
        globalSlot "again", globalSlot "after"].all (fun slot =>
          importCell outer final.runtime slot == some ⟨.binding none, false⟩) &&
      singletonInts final.runtime == [76, 27, 51] &&
      !final.runtime.heap.any (fun cell => match cell.contents with
        | .function closure => closure.declaration == 2
        | _ => false) &&
      final.cache.map Prod.fst == [0] && callerRestored caller final.runtime
  | _ => false

#guard savedSuccess false
#guard savedSuccess true
#guard savedCallFailure .missing false
#guard savedCallFailure .missing true
#guard savedCallFailure .surplus false
#guard savedCallFailure .surplus true
#guard savedDefaultFailure false
#guard savedDefaultFailure true

private def keywordWrapper : Imports.WrapperDeclaration "loaded" forwardingLoad.aliases savedGlobals where
  name := "relay"
  target := by decide
  visible := by decide
  legalAlias := by decide
  parameters := ⟨["x"], []⟩
  keywordOnly := [.required "at", .defaulted ⟨"key", starlark%[[seed]], .list [globalRead "seed"], [globalSlot "seed"]⟩]
  unshadowed := by decide
  keywordLexical := .cons (.list (.read (by decide) (.global (by decide) (by decide) (by decide))
    (.module (by decide) (by decide) (by decide)))) .nil
  arguments := [starlark%[key[0]], (.scalar (.read "at"))]
  codes := [.index (localRead "key") (int 0), localRead "at"]
  reads := [fileSlot "key", fileSlot "at"]
  operands := .cons (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0))
    (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil)
  keywords := .empty
  selects := .enclosing (.enclosing (by decide) (by decide))
    (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil))

private def keywordForwarder : OrderedConsumer := relayWithSetup keywordWrapper rfl

private inductive KeywordTest where
  | success | missing | surplus | unknown | duplicate | operandError
  deriving DecidableEq

private abbrev DownstreamBlock := Imports.block downstreamLoad.aliases savedDownstreamGlobals

open Defaults.Nested.Sequence.Recursive.Call.Named (Operands)

private def keywordArguments (test : KeywordTest) : Operands DownstreamBlock :=
  match test with
  | .success =>
    ⟨[("key", starlark%[[53]]), ("at", starlark%[0])], [("key", boxed 53), ("at", int 0)], [],
      .cons (.list (.int 53)) (.cons (.int 0) .nil), by decide⟩
  | .missing =>
    ⟨[("key", starlark%[[63]])], [("key", boxed 63)], [],
      .cons (.list (.int 63)) .nil, by decide⟩
  | .surplus =>
    ⟨[("at", starlark%[[65][0]])], [("at", .index (boxed 65) (int 0))], [],
      .cons (.index (.list (.int 65)) (.int 0)) .nil, by decide⟩
  | .unknown =>
    ⟨[("extra", starlark%[[64]]), ("at", starlark%[[65][0]])],
      [("extra", boxed 64), ("at", .index (boxed 65) (int 0))], [],
      .cons (.list (.int 64)) (.cons (.index (.list (.int 65)) (.int 0)) .nil), by decide⟩
  | .duplicate =>
    ⟨[("at", starlark%[[70][0]]), ("x", starlark%[[71]])],
      [("at", .index (boxed 70) (int 0)), ("x", boxed 71)], [],
      .cons (.index (.list (.int 70)) (.int 0)) (.cons (.list (.int 71)) .nil), by decide⟩
  | .operandError =>
    ⟨[("extra", starlark%[[64]]), ("at", starlark%[[65][1]]), ("key", starlark%[[66]])],
      [("extra", boxed 64), ("at", .index (boxed 65) (int 1)), ("key", boxed 66)], [],
      .cons (.list (.int 64)) (.cons (.index (.list (.int 65)) (.int 1))
        (.cons (.list (.int 66)) .nil)), by decide⟩

private def keywordCall (destination : String) (declared : destination ∈ savedDownstreamGlobals)
    (test : Option KeywordTest) : Imports.Invocation downstreamLoad.aliases savedDownstreamGlobals where
  callee := "bound"
  declared := .inl (by decide)
  legal := by decide
  destination := destination
  destinationGlobal := declared
  arguments := starlark%[0] :: if test = some .surplus then [starlark%[[64]]] else []
  codes := int 0 :: if test = some .surplus then [boxed 64] else []
  reads := []
  operands := by
    by_cases excess : test = some .surplus
    · simp only [excess, ite_true]
      exact .cons (.int 0) (.cons (.list (.int 64)) .nil)
    · simp only [excess, ite_false]
      exact .cons (.int 0) .nil
  keywords := match test with
    | none => ⟨[("at", starlark%[0])], [("at", int 0)], [], .cons (.int 0) .nil, by decide⟩
    | some test => keywordArguments test

private def keywordDownstream (test : KeywordTest) : OrderedConsumer where
  imports := [downstreamLoad]
  globals := savedDownstreamGlobals
  body :=
    [.invoke (keywordCall "firstResult" (by decide) none),
     .assign "marker" (by decide) (.list (.int 88)) .forget,
     .invoke (keywordCall "out" (by decide) (some test)),
     .invoke (keywordCall "again" (by decide) none),
     .assign "after" (by decide) (.list (.int 198)) .forget]
  declared := rfl

private def checkedRelayWithSetup
    (declaration : Imports.WrapperDeclaration "loaded" forwardingLoad.aliases savedGlobals)
    (name : declaration.name = "relay") (consumerPlan : OrderedConsumer)
    (loads : consumerPlan.imports = [downstreamLoad]) {producer middle consumer : ResolvedModule}
    (prod : resolve positionalCommands #[] = .ok producer)
    (mid : resolve (relayWithSetup declaration name).commands producer.program = .ok middle)
    (top : resolve consumerPlan.commands middle.program = .ok consumer)
    (ready : Imports.Chain.OrderedReady consumerPlan middle.program
      (some (Imports.initial "bound" (.wrapper declaration producer.program.size (.regular pickRoot.callable))))
      (fun _ => none)) :
    Imports.Chain.Graph producer.program (positionalManifest producer middle consumer) := by
  let middlePlan := relayWithSetup declaration name
  let wrapper := Callee.wrapper declaration producer.program.size (.regular pickRoot.callable)
  let env : Loader.ModuleId → Imports.Tracked
    | 0 => Imports.Chain.rootExports positionalExports
    | 1 => fun exportName => if exportName ∈ middlePlan.globals then
        Imports.trackSuite producer.program forwardingEnv middlePlan.body exportName else none
    | _ => fun _ => none
  have throughMiddle := Imports.ordered_preserves middlePlan mid
  have throughTop := Imports.ordered_preserves consumerPlan top
  have producerSize : producer.program.size = 2 := by rw [(plan_code positionalPlan prod).2]; rfl
  refine ⟨consumerPlan.commands, middle.program, consumer, top,
    fun index decl found => throughTop _ _ (throughMiddle index decl found), env, ?_⟩
  intro id bound
  have range : id = 0 ∨ id = 1 ∨ id = 2 := by change id < 3 at bound; omega
  rcases range with rfl | rfl | rfl
  · exact .root positionalPlan rfl prod (fun _ _ found => found) rfl
  · refine .ordered (finalEnv := some forwardingEnv) middlePlan mid (fun _ _ found => found)
      throughTop rfl ?_ ?_
    · exact .load (dependency := 0) (by decide) rfl
        (.found (.regular pickRoot.callable) rfl (.found (.regular spareRoot.callable) rfl (.done _)))
        (fun _ equal => by cases equal; exact .done _) (by simp)
    · exact ⟨⟨.regular pickRoot.callable, rfl, by change 1 < producer.program.size; omega, trivial⟩, rfl⟩
  · refine .ordered (finalEnv := some (Imports.initial "bound" wrapper)) consumerPlan top throughMiddle
      (fun _ _ found => found) rfl ?_ ready
    have exported : env 1 "relay" = some wrapper := by
      simp [env, middlePlan, relayWithSetup, savedGlobals, Imports.trackSuite, Imports.Step.advance,
        Imports.Step.emit, Imports.initial, Imports.track, Imports.Copy.track, forwardingEnv, name, wrapper]
      rfl
    rw [loads]
    exact .load (dependency := 1) (by decide) rfl (.found wrapper exported (.done _))
      (fun _ equal => by cases equal; exact .done _) (by simp)

private def checkedKeywordWrapper (test : KeywordTest) {producer middle consumer : ResolvedModule}
    (prod : resolve positionalCommands #[] = .ok producer)
    (mid : resolve keywordForwarder.commands producer.program = .ok middle)
    (top : resolve (keywordDownstream test).commands middle.program = .ok consumer) :
    Imports.Chain.Graph producer.program (positionalManifest producer middle consumer) := by
  let wrapper := Callee.wrapper keywordWrapper producer.program.size (.regular pickRoot.callable)
  apply checkedRelayWithSetup keywordWrapper rfl (keywordDownstream test) rfl prod mid top
  refine ⟨⟨wrapper, rfl, wrapper, rfl, wrapper, rfl, trivial⟩, ?_⟩
  funext name
  change (none : Option Callee) = _
  by_cases isAlias : name = "bound"
  · subst name
    rfl
  · simp [keywordDownstream, savedDownstreamGlobals, keywordCall, Imports.trackSuite, Imports.Step.advance,
      Imports.Copy.track, Imports.initial, Imports.track, isAlias, Callee.returned, Root.callable, pickRoot]

example (test : KeywordTest) {producer middle consumer : ResolvedModule}
    (prod : resolve positionalCommands #[] = .ok producer)
    (mid : resolve keywordForwarder.commands producer.program = .ok middle)
    (top : resolve (keywordDownstream test).commands middle.program = .ok consumer)
    (caller : Lists.State) (history : List Nat) (bounded : ∀ id ∈ history, id < 3) :
    let graph := checkedKeywordWrapper test prod mid top
    ∃ entered out, Imports.Chain.Requests graph history ⟨caller, []⟩ entered ∧
      Imports.Chain.TraceRun (positionalManifest producer middle consumer) 2 entered out ∧
      Loader.load consumer.program (positionalManifest producer middle consumer) 2 entered = out ∧
      Imports.Chain.Reached producer.program consumer.program (positionalManifest producer middle consumer)
        graph.exports 2 entered out := by
  intro graph
  obtain ⟨entered, requests, valid⟩ := Imports.Chain.requests graph history bounded ⟨caller, []⟩
    (fun _ _ impossible => nomatch impossible)
  obtain ⟨out, source, _, meaning, reached⟩ := Imports.Chain.agrees graph 2 (by change 2 < 3; decide) entered valid
  exact ⟨entered, out, requests, source, meaning, reached⟩

private def runRelayWithSetup (wrapper consumerPlan : OrderedConsumer) (warm : Bool) :
    Option (Loader.Result Modules.Published × Lists.State × Lists.State) := do
  let producer ← (resolve positionalCommands).toOption
  let middle ← (resolve wrapper.commands producer.program).toOption
  let consumer ← (resolve consumerPlan.commands middle.program).toOption
  let manifest := positionalManifest producer middle consumer
  let cold : Loader.Session := {runtime := forwardingCaller}
  let entry ← if warm then
      match Loader.load consumer.program manifest 1 cold with
      | .ok _ ready => some ready
      | .error .. => none
    else some cold
  some (Loader.load consumer.program manifest 2 entry, enter consumer.source entry.runtime, entry.runtime)

private def keywordRun (test : KeywordTest) (warm : Bool) :=
  runRelayWithSetup keywordForwarder (keywordDownstream test) warm

private def relayDefaultRecord (session : Loader.Session) (defaultValue : Int := 27) : Bool :=
  match (session.cache.lookup 1).bind (fun value => value.exports.lookup "relay") with
  | some (.function address) =>
    match session.runtime.heap[address]? with
    | some ⟨.function { defaults := [(slot, .list saved)], .. }, true⟩ =>
      slot == fileSlot "key" && session.runtime.heap[saved]? == some ⟨.list [.scalar (.int defaultValue)], true⟩ &&
        forwardingRecord session
    | _ => false
  | _ => false

private def keywordSuccess (warm : Bool) : Bool :=
  match keywordRun .success warm with
  | some (.ok published final, _, caller) =>
    published.exports.lookup "firstResult" == some (.scalar (.int 27)) &&
      published.exports.lookup "out" == some (.scalar (.int 53)) &&
      published.exports.lookup "again" == some (.scalar (.int 27)) &&
      singletonInts final.runtime == [76, 27, 199, 27, 88, 53, 53, 27, 198] &&
      final.cache.map Prod.fst == [2, 1, 0] && relayDefaultRecord final &&
      callerRestored caller final.runtime && (final.runtime.slots (fileSlot "bound")).isNone
  | _ => false

private def keywordFailure (test : KeywordTest) (warm : Bool) : Bool :=
  match keywordRun test warm with
  | some (.error (.initialization 2 (.runtime error)) final, frame, caller) =>
    let correct := match test, error with
      | .missing, .missingArguments ["at"] | .surplus, .arity 1 2
      | .unknown, .unexpectedKeyword "extra" | .duplicate, .multipleArgumentValues "x"
      | .operandError, .indexRange 1 1 => true
      | _, _ => false
    let operands := match test with
      | .missing => [63]
      | .surplus | .unknown | .operandError => [64, 65]
      | .duplicate => [70, 71]
      | .success => []
    correct &&
      importCell frame final.runtime (globalSlot "firstResult") == some ⟨.binding (some (.scalar (.int 27))), false⟩ &&
      [globalSlot "out", globalSlot "again", globalSlot "after"].all (fun slot =>
        importCell frame final.runtime slot == some ⟨.binding none, false⟩) &&
      singletonInts final.runtime == [76, 27, 199, 27, 88] ++ operands &&
      final.runtime.heap.size == 29 + operands.length &&
      final.cache.map Prod.fst == [1, 0] && relayDefaultRecord final &&
      callerRestored caller final.runtime && (final.runtime.slots (fileSlot "bound")).isNone
  | _ => false

#guard keywordSuccess false
#guard keywordSuccess true
#guard [.missing, .surplus, .unknown, .duplicate, .operandError].all (fun test =>
  keywordFailure test false && keywordFailure test true)

#guard
  match resolve [.load downstreamLoad.label (downstreamLoad.bindings.map ImportBinding.item),
    .assign "out" (.call starlark%[bound] [starlark%[0]]
      [("at", starlark%[0]), ("at", starlark%[[64][1]])] none none)] with
  | .error (.validation (.syntax (.duplicateExplicitKeyword "at"))) => true
  | _ => false

private def collectorWrapper : Imports.WrapperDeclaration "loaded" forwardingLoad.aliases savedGlobals where
  name := "relay"
  target := by decide
  visible := by decide
  legalAlias := by decide
  parameters := ⟨["x"], []⟩
  keywordOnly := [.required "at", .defaulted ⟨"key", starlark%[[0]], boxed 0, []⟩]
  varargs := some "rest"
  unshadowed := by decide
  keywordLexical := .cons (.list (.int 0)) .nil
  arguments := [starlark%[rest], .index starlark%[key] (.scalar (.read "at"))]
  codes := [localRead "rest", .index (localRead "key") (localRead "at")]
  reads := [fileSlot "rest", fileSlot "key", fileSlot "at"]
  operands := .cons (.read (by decide) (.owned (by decide)) (.owned (by decide)))
    (.cons (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
      (.read (by decide) (.owned (by decide)) (.owned (by decide)))) .nil)
  keywords := .empty
  selects := .enclosing (.enclosing (by decide) (by decide))
    (.owned (.owned (by decide)) (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil)))

private def collectorForwarder : OrderedConsumer := relayWithSetup collectorWrapper rfl

private inductive CollectorTest where
  | success | missing | unknown | operandError
  deriving DecidableEq

private def collectorCall (destination : String) (declared : destination ∈ savedDownstreamGlobals)
    (test : Option CollectorTest) : Imports.Invocation downstreamLoad.aliases savedDownstreamGlobals where
  callee := "bound"
  declared := .inl (by decide)
  legal := by decide
  destination := destination
  destinationGlobal := declared
  arguments := starlark%[91] :: match test with
    | none => []
    | some .success => [starlark%[17], starlark%[marker], starlark%[18]]
    | some .missing => [starlark%[[63]]]
    | _ => [starlark%[17]]
  codes := int 91 :: match test with
    | none => []
    | some .success => [int 17, globalRead "marker", int 18]
    | some .missing => [boxed 63]
    | _ => [int 17]
  reads := if test = some .success then [globalSlot "marker"] else []
  operands := by
    cases test with
    | none => exact .cons (.int 91) .nil
    | some test =>
      cases test with
      | success =>
        exact .cons (.int 91) (.cons (.int 17) (.cons (.read (by decide)
          (.global (by decide) (by decide) (by decide)) (.module (by decide) (by decide) (by decide)))
          (.cons (.int 18) .nil)))
      | missing => exact .cons (.int 91) (.cons (.list (.int 63)) .nil)
      | unknown | operandError => exact .cons (.int 91) (.cons (.int 17) .nil)
  keywords := match test with
    | none => ⟨[("at", starlark%[0])], [("at", int 0)], [], .cons (.int 0) .nil, by decide⟩
    | some .success =>
      ⟨[("key", .list [.scalar (.int (-1))]), ("at", starlark%[0])], [("key", boxed (-1)), ("at", int 0)], [],
        .cons (.list (.int (-1))) (.cons (.int 0) .nil), by decide⟩
    | some .missing => .empty
    | some .unknown => keywordArguments .unknown
    | some .operandError => keywordArguments .operandError

private def collectorDownstream (test : CollectorTest) : OrderedConsumer where
  imports := [downstreamLoad]
  globals := savedDownstreamGlobals
  body :=
    [.invoke (collectorCall "firstResult" (by decide) none),
     .assign "marker" (by decide) (.list (.int 88)) .forget,
     .invoke (collectorCall "out" (by decide) (some test)),
     .invoke (collectorCall "again" (by decide) none),
     .assign "after" (by decide) (.list (.int 198)) .forget]
  declared := rfl

private def checkedCollectorWrapper (test : CollectorTest) {producer middle consumer : ResolvedModule}
    (prod : resolve positionalCommands #[] = .ok producer)
    (mid : resolve collectorForwarder.commands producer.program = .ok middle)
    (top : resolve (collectorDownstream test).commands middle.program = .ok consumer) :
    Imports.Chain.Graph producer.program (positionalManifest producer middle consumer) := by
  let wrapper := Callee.wrapper collectorWrapper producer.program.size (.regular pickRoot.callable)
  apply checkedRelayWithSetup collectorWrapper rfl (collectorDownstream test) rfl prod mid top
  refine ⟨⟨wrapper, rfl, wrapper, rfl, wrapper, rfl, trivial⟩, ?_⟩
  funext name
  change (none : Option Callee) = _
  by_cases isAlias : name = "bound"
  · subst name
    rfl
  · simp [collectorDownstream, savedDownstreamGlobals, collectorCall, Imports.trackSuite, Imports.Step.advance,
      Imports.Copy.track, Imports.initial, Imports.track, isAlias, Callee.returned, Root.callable, pickRoot]

example (test : CollectorTest) {producer middle consumer : ResolvedModule}
    (prod : resolve positionalCommands #[] = .ok producer)
    (mid : resolve collectorForwarder.commands producer.program = .ok middle)
    (top : resolve (collectorDownstream test).commands middle.program = .ok consumer)
    (caller : Lists.State) (history : List Nat) (bounded : ∀ id ∈ history, id < 3) :
    let graph := checkedCollectorWrapper test prod mid top
    ∃ entered out, Imports.Chain.Requests graph history ⟨caller, []⟩ entered ∧
      Imports.Chain.TraceRun (positionalManifest producer middle consumer) 2 entered out ∧
      Loader.load consumer.program (positionalManifest producer middle consumer) 2 entered = out ∧
      Imports.Chain.Reached producer.program consumer.program (positionalManifest producer middle consumer)
        graph.exports 2 entered out := by
  intro graph
  obtain ⟨entered, requests, valid⟩ := Imports.Chain.requests graph history bounded ⟨caller, []⟩
    (fun _ _ impossible => nomatch impossible)
  obtain ⟨out, source, _, meaning, reached⟩ := Imports.Chain.agrees graph 2 (by change 2 < 3; decide) entered valid
  exact ⟨entered, out, requests, source, meaning, reached⟩

private def tupleCount (state : Lists.State) : Nat :=
  (state.heap.toList.filter (fun cell => match cell.contents with | .tuple .. => true | _ => false)).length

private def emptyTupleCell (state : Lists.State) (address : Nat) (frozen : Bool) : Bool :=
  state.heap[address]? == some ⟨.tuple [] (some [.openTuple, .closeTuple]), frozen⟩

private def collectorSuccess (warm : Bool) : Bool :=
  match runRelayWithSetup collectorForwarder (collectorDownstream .success) warm with
  | some (.ok published final, _, caller) =>
    match published.exports.lookup "firstResult", published.exports.lookup "out",
        published.exports.lookup "again", published.exports.lookup "marker" with
    | some (.tuple first), some (.tuple ordered), some (.tuple again), some (.list marker) =>
      emptyTupleCell final.runtime first true && emptyTupleCell final.runtime again true && first != again &&
      final.runtime.heap[ordered]? == some ⟨.tuple [.scalar (.int 17), .list marker, .scalar (.int 18)] none, true⟩ &&
      tupleCount final.runtime == 3 &&
      final.runtime.heap.any (fun cell => cell.contents == .binding (some (.scalar (.int (-1))))) &&
      final.cache.map Prod.fst == [2, 1, 0] && relayDefaultRecord final 0 &&
      callerRestored caller final.runtime && (final.runtime.slots (fileSlot "bound")).isNone
    | _, _, _, _ => false
  | _ => false

private def collectorFailure (test : CollectorTest) (warm : Bool) : Bool :=
  match runRelayWithSetup collectorForwarder (collectorDownstream test) warm with
  | some (.error (.initialization 2 (.runtime error)) final, frame, caller) =>
    let correct := match test, error with
      | .missing, .missingArguments ["at"] | .unknown, .unexpectedKeyword "extra"
      | .operandError, .indexRange 1 1 => true
      | _, _ => false
    let operands := if test == .missing then [63] else [64, 65]
    match importCell frame final.runtime (globalSlot "firstResult") with
    | some ⟨.binding (some (.tuple address)), false⟩ =>
      correct && emptyTupleCell final.runtime address false && tupleCount final.runtime == 1 &&
      [globalSlot "out", globalSlot "again", globalSlot "after"].all (fun slot =>
        importCell frame final.runtime slot == some ⟨.binding none, false⟩) &&
      singletonInts final.runtime == [76, 0, 199, 88] ++ operands &&
      final.runtime.heap.size == 31 + operands.length &&
      final.cache.map Prod.fst == [1, 0] && relayDefaultRecord final 0 &&
      callerRestored caller final.runtime && (final.runtime.slots (fileSlot "bound")).isNone
    | _ => false
  | _ => false

#guard collectorSuccess false
#guard collectorSuccess true
#guard [.missing, .unknown, .operandError].all (fun test =>
  collectorFailure test false && collectorFailure test true)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

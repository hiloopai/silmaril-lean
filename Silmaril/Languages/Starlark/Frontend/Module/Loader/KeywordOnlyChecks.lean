module

public import Silmaril.Languages.Starlark.Frontend.Module.Loader.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Loader.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module.Loader

public def keywordProducerLabel := "pkg:pick"
public def keywordWrapperLabel := "pkg:relay"

public def keywordProducer :=
  "# 雪\ndef pick(x, ready, fallback):\n  if ready:\n    return fallback\n  return x"

public def keywordWrapper :=
  "# 橋\nload('pkg:pick', loaded='pick')\nseed=7\n" ++
  "def relay(x=3, *, fallback=seed, ready,):\n  return loaded(x, ready, fallback)"

private def downstream (call : String) : String :=
  "# 鍵\nload('pkg:relay', imported='relay')\nout=" ++ call

public inductive KeywordObservation where
  | exported (value : Int)
  | missing (name : String)
  | positionalOverflow (capacity count : Nat)
  deriving DecidableEq

public structure KeywordControl where
  name : String
  source : String
  expected : KeywordObservation

/-- Three-file source controls for a loaded wrapper that calls its own captured import. -/
public def keywordOnlyControls : List KeywordControl := [
  ⟨"loaded-keyword-wrapper-saved-default", downstream "imported(ready=True)", .exported 7⟩,
  ⟨"loaded-keyword-wrapper-override", downstream "imported(ready=True, fallback=11)", .exported 11⟩,
  ⟨"loaded-keyword-wrapper-positional-default", downstream "imported(ready=False)", .exported 3⟩,
  ⟨"loaded-keyword-wrapper-missing-required", downstream "imported(fallback=11)" ++ "\nmarker=99", .missing "ready"⟩,
  ⟨"loaded-keyword-wrapper-positional-overflow", downstream "imported(1, 2, ready=True)" ++ "\nmarker=99",
    .positionalOverflow 1 2⟩]

private def keywordGraph (source : String) : Array TextEntry :=
  #[⟨keywordProducer.toUTF8, []⟩, ⟨keywordWrapper.toUTF8, [(keywordProducerLabel, 0)]⟩,
    ⟨source.toUTF8, [(keywordWrapperLabel, 1)]⟩]

private def savedDefaults (session : Modules.Loader.Session) : Bool := Id.run do
  let some published := session.cache.lookup 1 | return false
  let some (.function address) := published.exports.lookup "relay" | return false
  let some ⟨.function closure, true⟩ := session.runtime.heap[address]? | return false
  return closure.declaration == 1 &&
    decide (closure.defaults.map (fun (binding, value) => (binding.name, value)) =
      [("x", .scalar (.int 3)), ("fallback", .scalar (.int 7))])

private def observeKeyword (source : String) : Option KeywordObservation :=
  match loadUtf8 (keywordGraph source) 2 with
  | .ok (.ok published session) =>
    match published.exports.lookup "out" with
    | some (.scalar (.int value)) =>
      if session.cache.map Prod.fst == [2, 1, 0] && savedDefaults session then some (.exported value) else none
    | _ => none
  | .ok (.error (.initialization 2 (.runtime error)) session) =>
    if session.cache.map Prod.fst != [1, 0] || !savedDefaults session ||
        session.runtime.heap.any (fun cell =>
          match cell.contents with | .binding (some (.scalar (.int 99))) => true | _ => false) then none
    else match error with
      | .missingArguments [name] => some (.missing name)
      | .arity capacity count => some (.positionalOverflow capacity count)
      | _ => none
  | _ => none

#guard keywordOnlyControls.all fun control => decide (observeKeyword control.source = some control.expected)

private def resolvedHeader : Bool := Id.run do
  let .ok prepared := prepare (keywordGraph (downstream "imported(ready=True)")) | return false
  let some declaration := prepared.program[1]? | return false
  return declaration.signature.positional.map (·.slot.name) == ["x"] &&
    declaration.signature.keywordOnly.map (·.slot.name) == ["fallback", "ready"] &&
    declaration.signature.slots.map (·.name) == ["x", "fallback", "ready"] &&
    declaration.signature.defaulted.map (·.1.name) == ["x", "fallback"] &&
    declaration.signature.varargs.isNone && declaration.signature.kwargs.isNone

#guard resolvedHeader

/-- Required-only bare-star syntax reaches the pinned core's normalized validator. -/
public def requiredOnlySource :=
  "# 雪\ndef relay(*, ready):\n  return ready\nout=relay(ready=7)"

#guard match Frontend.Module.runUtf8 requiredOnlySource.toUTF8 with
  | .error (.validation (.validation (.syntax .bareStarWithoutOptional))) => true
  | _ => false

private def leadingSeparator := "# 雪\ndef relay(*, ready, fallback=7):\n  return fallback if ready else 0\n" ++
  "out=relay(ready=True)"

#guard match Frontend.Module.runUtf8 leadingSeparator.toUTF8 with
  | .ok (.ok published _) => published.exports.lookup "out" == some (.scalar (.int 7))
  | _ => false

public def headerSpanSource :=
  "# 雪\r\nseed=7\r\ndef relay(x=3,\r\n  *,  # 鍵\r\n  fallback=seed, ready,\r\n  extra=8,):\r\n  return fallback"

public def headerFormalSpans : List Span := [
  ⟨⟨25, 3, 11⟩, ⟨28, 3, 14⟩⟩, ⟨⟨33, 4, 3⟩, ⟨34, 4, 4⟩⟩,
  ⟨⟨46, 5, 3⟩, ⟨59, 5, 16⟩⟩, ⟨⟨61, 5, 18⟩, ⟨66, 5, 23⟩⟩, ⟨⟨71, 6, 3⟩, ⟨78, 6, 10⟩⟩]

private def headerSpans : Option (List Span × List (Span × Option Span)) := do
  let [_, command] ← (parseFileUtf8 headerSpanSource.toUTF8).toOption | none
  let .define fn := command.command | none
  let suffix ← fn.keywordOnly
  let parsed ← (Frontend.Module.parseUtf8 headerSpanSource.toUTF8).toOption
  let [_, declaration] := parsed.commands | none
  match declaration.command with
  | .define "relay" ⟨[⟨"x", some (.plain (.scalar (.int 3)))⟩],
      [⟨"fallback", some (.plain (.scalar (.read "seed")))⟩, ⟨"ready", none⟩,
        ⟨"extra", some (.plain (.scalar (.int 8)))⟩], none, none⟩ _ =>
    return (fn.parameters.map LocatedParameter.span ++ [suffix.separator] ++ suffix.parameters.map LocatedParameter.span,
      (fn.parameters ++ suffix.parameters).map fun item => (item.nameSpan, item.defaultValue.map LocatedArgument.span))
  | _ => none

example : headerSpans = some (headerFormalSpans, [
    (⟨⟨25, 3, 11⟩, ⟨26, 3, 12⟩⟩, some ⟨⟨27, 3, 13⟩, ⟨28, 3, 14⟩⟩),
    (⟨⟨46, 5, 3⟩, ⟨54, 5, 11⟩⟩, some ⟨⟨55, 5, 12⟩, ⟨59, 5, 16⟩⟩),
    (⟨⟨61, 5, 18⟩, ⟨66, 5, 23⟩⟩, none),
    (⟨⟨71, 6, 3⟩, ⟨76, 6, 8⟩⟩, some ⟨⟨77, 6, 9⟩, ⟨78, 6, 10⟩⟩)]) := by decide +kernel

public structure HeaderControl where
  name : String
  source : String
  diagnostic : DiagnosticKind
  goAccepts : Bool
  goValidationError : Option String := none

public def headerControls : List HeaderControl := [
  ⟨"empty-bare-star", "# 雪\r\ndef f(x, *,):\r\n  return x", .expected "a keyword-only parameter after '*'",
    true, some "bare * must be followed by keyword-only parameters"⟩,
  ⟨"bare-star-before-close", "def f(*):\n  pass", .expected "a keyword-only parameter after '*'",
    true, some "bare * must be followed by keyword-only parameters"⟩,
  ⟨"repeated-bare-star", "def f(*, x=1, *, y=2):\n  pass", .expected "a single bare '*' separator",
    true, some "multiple * parameters not allowed"⟩,
  ⟨"bare-star-requires-comma", "def f(* =1, x=2):\n  pass", .expected "',' after '*'", false, none⟩,
  ⟨"double-comma-after-bare-star", "def f(*,, x=1):\n  pass", .expected "a name", false, none⟩,
  ⟨"duplicate-across-bare-star", "# 雪\r\ndef f(x, *, x=1):\r\n  return x", .duplicateParameter "x",
    true, some "duplicate parameter: x"⟩,
  ⟨"duplicate-within-keyword-only", "def f(*, x, x=1):\n  pass", .duplicateParameter "x",
    true, some "duplicate parameter: x"⟩,
  ⟨"named-positional-collector-header", "def f(*args, x=1):\n  pass", .unsupported .parameters, true, none⟩,
  ⟨"keyword-collector-header", "def f(*, x=1, **kw):\n  pass", .unsupported .parameters, true, none⟩,
  ⟨"call-in-keyword-only-default", "def f(*, x=g()):\n  pass", .unsupported .call, true, none⟩]

private def headerDiagnostic (source : String) : Option Diagnostic :=
  match parseFileUtf8 source.toUTF8 with
  | .error diagnostic => some diagnostic
  | .ok _ => none

#guard headerControls.all fun control =>
  (headerDiagnostic control.source).map Diagnostic.kind == some control.diagnostic

example : headerDiagnostic "# 雪\r\ndef f(x, *,):\r\n  return x" =
    some ⟨.expected "a keyword-only parameter after '*'", ⟨⟨16, 2, 10⟩, ⟨17, 2, 11⟩⟩⟩ :=
  by decide +kernel

example : headerDiagnostic "# 雪\r\ndef f(x, *, x=1):\r\n  return x" =
    some ⟨.duplicateParameter "x", ⟨⟨19, 2, 13⟩, ⟨20, 2, 14⟩⟩⟩ := by decide +kernel

private def standaloneDiagnostic : Option Diagnostic :=
  match parseFunctionUtf8 "# 雪\r\ndef f(*, x=1):\r\n  return x".toUTF8 with
  | .error diagnostic => some diagnostic
  | .ok _ => none

example : standaloneDiagnostic =
    some ⟨.unsupported .parameters, ⟨⟨13, 2, 7⟩, ⟨14, 2, 8⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module.Loader

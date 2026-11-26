# SPDX-License-Identifier: MIT
"""Compare checked saved positional defaults with CPython 3.13.5."""

from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path
import runpy
import sys
import tempfile


ALIAS = """initial = 7
def pick(x=initial, y=None):
    def keep():
        return x
    return x
alias = pick
initial = 11
pick = lambda x=initial: x
omitted = alias()
rebound = pick()
explicit = None
overridden = alias(explicit)
"""

FAIL_DEFAULT = """def factory(x):
    def leaf():
        return x
    return leaf
saved = factory(4)
existing = 99
def existing(x=existing, y=first_missing, z=second_missing):
    return x
unreached = 1
"""

ARITY = """def needs(x, y=10):
    def keep():
        return x
    return x
answer = 23
answer = needs()
"""

COMMON = """
open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run
open Core.Module.SeededCall (Namespace Result Value)

abbrev Bindings := List (String × Value)

private def heap : Core.Closure.Heap :=
  ⟨1, fun index => if index = 0 then some (.int 37) else none⟩

private def contents (heap : Core.Closure.Heap) : List (Option Value) :=
  (List.range heap.next).map fun index => (heap.contents index).map Seeded.seededValue

private def saved (lookup : String → Option Value) (name : String) :
    Option (List Core.Module.Value) :=
  match lookup name with
  | some (.function fn) => some fn.positionalDefaults
  | _ => none

private def seeds : List Namespace :=
  [.empty, Seeded.legacySeed .builtin, Seeded.legacySeed .preamble]

private def both (source : Source.Module) (ordinary : Completion)
    (seeded : Except Seeded.ModuleFailure Unit) (names : List String) (values : Bindings)
    (cells : List Value) (receipts : List (String × Result))
    (check : (String → Option Value) → Bool) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let initial := State.ready (seed .empty heap) compiled.instructions
  let .finished plain completion := (runPrefix compiled.table 256 initial).2 | return false
  let ordinaryLookup := fun name => (plain.globals name).map Seeded.seededValue
  let matchBindings := fun (lookup : String → Option Value) =>
    values.all (fun (name, value) => lookup name == some value) && check lookup
  return completion == ordinary && matchBindings ordinaryLookup && contents plain.heap == cells.map some &&
    seeds.all (fun space =>
      let run := Seeded.run space compiled heap
      let keys := run.residual.moduleGlobals.map Prod.fst
      let expectedKeys := names ++ space.moduleGlobals.map Prod.fst
      run.completion == seeded && matchBindings run.residual.lookupGlobal &&
        keys.length == expectedKeys.length && keys.all expectedKeys.contains &&
        run.residual.builtins == space.builtins && contents run.heap == cells.map some &&
        run.calls.map (fun call => (call.callee, call.observation.result)) == receipts &&
        run.calls.all (fun call => call.observation.caught.isNone))
"""

ALIAS_CHECK = """
#guard both pythonSource .normal (.ok ())
  ["initial", "pick", "alias", "omitted", "rebound", "explicit", "overridden"]
  [("initial", .int 11), ("omitted", .int 7), ("rebound", .int 11),
    ("explicit", .none), ("overridden", .none)]
  [.int 37, .int 7, .none] [("alias", .ok (.int 7)), ("pick", .ok (.int 11)), ("alias", .ok .none)]
  (fun lookup => saved lookup "alias" == some [.int 7, .none] && saved lookup "pick" == some [.int 11])

private def interrupted (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let space := Seeded.legacySeed .builtin
  let noFuel := Seeded.run space compiled heap 0
  let some (Instruction.publishDefaults _ first _) := compiled.instructions[1]? | return false
  let table : Core.Closure.Executor.CodeTable := fun key =>
    if key = first.ref.key then none else compiled.table key
  let imported := space.bindGlobal "imported" (.function (first.withDefaults [.int 7, .none]))
  let rejected := Seeded.runInstructions imported
    [(.call .discard "imported" [] : Instruction compiled.checked.tree.scope)] compiled.table heap
  let damaged := Seeded.runInstructionsIn noFuel.residual { table, heap, fuel := 100 }
    [(.call .discard "alias" [] : Instruction compiled.checked.tree.scope)] .empty ["alias"]
  return noFuel.completion == .error .directCallFuelExhausted && noFuel.calls.isEmpty &&
    contents noFuel.heap == [some (.int 37)] &&
    noFuel.residual.lookupGlobal "omitted" == none &&
    saved noFuel.residual.lookupGlobal "alias" == some [.int 7, .none] &&
    rejected.completion == .error .unsupported && contents rejected.heap == [some (.int 37)] &&
    damaged.completion == .error (.directCallFault (.missingCode first.ref.key)) &&
    damaged.calls.isEmpty && damaged.residual.moduleGlobals == noFuel.residual.moduleGlobals &&
    contents damaged.heap == [some (.int 37)]

#guard interrupted pythonSource
"""

FAIL_CHECK = """
private def residualClosure (lookup : String → Option Value) : Bool :=
  match lookup "saved" with
  | some (.function fn) => fn.captures.toList.map Core.Closure.CellId.address == [1]
  | _ => false

#guard match compile pythonSource with
  | .ok compiled =>
    let run := Seeded.run Namespace.empty compiled heap
    let names := run.residual.moduleGlobals.map Prod.fst
    run.completion == .error (.raised (.runtime (.nameError "first_missing"))) &&
      contents run.heap == [some (.int 37), some (.int 4)] &&
      names.length == 3 && names.all ["factory", "saved", "existing"].contains &&
      run.residual.lookupGlobal "existing" == some (.int 99) &&
      residualClosure run.residual.lookupGlobal &&
      run.calls.length == 1 && run.calls.all (fun call => call.callee == "factory" &&
        call.observation.caught.isNone && call.observation.result.toOption == run.residual.lookupGlobal "saved") &&
      (match (runPrefix compiled.table 256 (.ready (seed .empty heap) compiled.instructions)).2 with
        | .finished session (.raised (.nameError name)) =>
          name == "first_missing" && contents session.heap == [some (.int 37), some (.int 4)] &&
            (session.globals "existing").map Seeded.seededValue == some (.int 99) &&
            residualClosure (fun name => (session.globals name).map Seeded.seededValue)
        | _ => false)
  | .error _ => false
"""

ARITY_CHECK = """
#guard both pythonSource (.raised (.positionalArity 1 0))
  (.error (.raised (.runtime (.positionalArity 1 0)))) ["needs", "answer"] [("answer", .int 23)]
  [.int 37] [("needs", .error (.raised (.runtime (.positionalArity 1 0))))]
  (fun lookup => saved lookup "needs" == some [.int 10])
"""


def lookup_error_check(callee, missing):
    return f"""
#guard both pythonSource (.raised (.nameError "{missing}"))
  (.error (.raised (.runtime (.nameError "{missing}")))) ["needs", "answer"] [("answer", .int 23)]
  [.int 37] [("{callee}", .error (.raised (.runtime (.nameError "{missing}"))))]
  (fun lookup => saved lookup "needs" == some [.int 10])
"""


def cpython(source, placement, error_type=None, error_name=None):
    def helper(left, right):
        assert left == right

    builtins = {"___assertEqual": helper} if placement == "builtin" else {}
    namespace = {"__builtins__": builtins}
    if placement == "preamble":
        namespace["___assertEqual"] = helper
    incoming = dict(namespace)
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        try:
            exec(compile(source, "<saved defaults>", "exec", dont_inherit=True, optimize=0), namespace)
        except (NameError, TypeError) as error:
            assert type(error) is error_type
            assert getattr(error, "name", None) == error_name
        else:
            assert error_type is None
    assert stdout.getvalue() == stderr.getvalue() == ""
    assert all(namespace.pop(key) is value for key, value in incoming.items())
    return namespace


if __name__ == "__main__":
    assert sys.version_info[:3] == (3, 13, 5)
    arguments_first = ARITY.replace("needs()", "needs(1, missing_arg, 3)")
    callee_first = ARITY.replace("needs()", "missing_callee(missing_arg)")
    for placement in ("empty", "builtin", "preamble"):
        observed = cpython(ALIAS, placement)
        assert set(observed) == {"initial", "pick", "alias", "omitted", "rebound", "explicit", "overridden"}
        assert observed["alias"].__defaults__ == (7, None)
        assert observed["pick"].__defaults__ == (11,)
        assert observed["alias"].__code__.co_cellvars == ("x",)
        assert observed["initial"] == 11 and observed["omitted"] == 7 and observed["rebound"] == 11
        assert observed["explicit"] is observed["overridden"] is None
        failed = cpython(FAIL_DEFAULT, placement, NameError, "first_missing")
        assert set(failed) == {"factory", "saved", "existing"}
        assert failed["existing"] == 99 and failed["saved"].__closure__[0].cell_contents == 4
        arity = cpython(ARITY, placement, TypeError)
        assert set(arity) == {"needs", "answer"} and arity["answer"] == 23
        assert cpython(arguments_first, placement, NameError, "missing_arg")["answer"] == 23
        assert cpython(callee_first, placement, NameError, "missing_callee")["answer"] == 23
    here = Path(__file__).resolve().parent
    shared = runpy.run_path(str(here.parent / "source-scope/check_intake.py"))
    imports = runpy.run_path(str(here / "check_return_local_call.py"))["IMPORTS"]
    with tempfile.TemporaryDirectory() as tmp:
        source = Path(tmp) / "Defaults.py"
        lean = Path(tmp) / "Defaults.lean"
        fixtures = (
            (ALIAS, ALIAS_CHECK),
            (FAIL_DEFAULT, FAIL_CHECK),
            (ARITY, ARITY_CHECK),
            (arguments_first, lookup_error_check("needs", "missing_arg")),
            (callee_first, lookup_error_check("missing_callee", "missing_callee")),
        )
        for body, checks in fixtures:
            shared["emit"](source, lean, body)
            shared["check_lean"](lean, COMMON + checks, extra_imports=imports)
    print("Saved defaults agree with CPython 3.13.5 for aliases, explicit None, default errors and arity.")

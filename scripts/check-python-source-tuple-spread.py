# SPDX-License-Identifier: MIT
"""Compare source tuple spreads and fixed/variadic binding with CPython 3.13.5."""

from pathlib import Path
import runpy
import sys
import tempfile


SUCCESS = """def collect(first, *tail):
    def keep():
        return tail
    return tail
saved = collect
collect = 101
answer = saved(*(False,), *(), 8, *(None, True))
empty = saved(*(False,))
plain = saved(5, 6)
def fixed(first, second):
    return (first, second)
fixed_result = fixed(*(False,), None)
def no_prefix(*tail):
    return tail
no_prefix_result = no_prefix(*())
via_lambda = lambda *tail: tail
lambda_result = via_lambda(*(None,))
dynamic_result = saved(5, *answer)
"""

FIXED = """answer = 77
def fixed(one):
    return one
"""

REACHED = """answer = 77
def reached(first, *tail):
    def keep():
        return tail
    return body_missing
answer = reached(*(1, False, None))
"""

FAILURES = (
    (FIXED + "answer = absent(*(first_missing,), later)\n", NameError, "absent",
     '.nameError "absent"', (), ()),
    (FIXED + "answer = fixed(*(1, 2), later)\n", NameError, "later",
     '.nameError "later"', (), ()),
    (FIXED + "answer = fixed(*(first_missing, second_missing))\n", NameError, "first_missing",
     '.nameError "first_missing"', (), ()),
    (FIXED + "answer = fixed(*False, later)\n", TypeError, None,
     ".unpackNonIterable", (), ()),
    (FIXED + "answer = fixed(*(1, 2))\n", TypeError, None,
     ".positionalArity 1 2", (), ("fixed",)),
    (FIXED + "answer = fixed(*())\n", TypeError, None,
     ".positionalArity 1 0", (), ("fixed",)),
    (FIXED + "fixed = 0\nanswer = fixed(*(), later)\n", NameError, "later",
     '.nameError "later"', (), ()),
    (FIXED + "fixed = 0\nanswer = fixed(*())\n", TypeError, None,
     ".notCallable", (), ("fixed",)),
    (REACHED, NameError, "body_missing", '.nameError "body_missing"', ((False, None),), ("reached",)),
)

HELPERS = r"""
open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run
open Core.Module.SeededCall (Namespace Value Result)

private def cells (heap : Core.Closure.Heap) : List (Option Value) :=
  (List.range heap.next).map fun index => (heap.contents index).map Seeded.seededValue

private def initialFinite : Core.Closure.Finite.HeapTable :=
  ((Core.Closure.Finite.HeapTable.empty.reserve 1).write ⟨0⟩ (.int 37)).getD .empty

private def initial : Core.Closure.Heap := initialFinite.project

private def checkRunners (source : Source.Module) (ordinaryStatus : Completion)
    (seededStatus : Except Seeded.ModuleFailure Unit) (bindings : List (String × Value))
    (heap : List Value) (receipts : List (String × Result)) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let .finished ordinary status := (runPrefix compiled.table 256
    (.ready (seed .empty initial) compiled.instructions)).2 | return false
  let ordinaryOK := status == ordinaryStatus && cells ordinary.heap == heap.map some &&
    bindings.all (fun (key, value) => (ordinary.globals key).map Seeded.seededValue == some value)
  let spaces : List Namespace := [.empty, Seeded.legacySeed .builtin, Seeded.legacySeed .preamble]
  return ordinaryOK && spaces.all fun space =>
    let seeded := Seeded.run space compiled initial
    seeded.completion == seededStatus && cells seeded.heap == heap.map some &&
    seeded.residual.builtins == space.builtins && seeded.lists.objects.isEmpty &&
    seeded.calls.map (fun call => (call.callee, call.observation.result)) == receipts &&
    seeded.calls.all (fun call => call.observation.caught.isNone) &&
    bindings.all (fun (key, value) => seeded.residual.lookupGlobal key == some value)

private def checkFinite (source : Source.Module) (steps : Nat)
    (result : Core.Closure.Result) (expectedCells : List Value) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let start := State.ready (seed .empty initial) compiled.instructions
  let .calling invocation _ := (runPrefix compiled.table steps start).2 | return false
  let .running _ frame body stack := invocation.state | return false
  let rows : Core.Closure.Finite.Executor.CodeRows :=
    compiled.entries.zipIdx.foldl (fun rows (entry, index) => rows.insert index entry) ∅
  let (events, finite) := Core.Closure.Finite.Executor.runPrefixIn rows invocation.globals 64
    (.running ⟨initialFinite, frame⟩ body stack)
  let .finished heap observed := finite | return false
  let (ordinaryEvents, ordinary) := invocation.runPrefix compiled.table 64
  let .finished ordinaryHeap ordinaryResult := ordinary.state | return false
  let resultAgrees := fun value : Core.Closure.Result => value.map Seeded.seededValue == result.map Seeded.seededValue
  let exactEvents := match events, ordinaryEvents with
    | [.enter actual, .resume a, .complete b], [.enter expected, .resume c, .complete d] =>
      Seeded.seededValue actual == Seeded.seededValue expected && resultAgrees a && resultAgrees b && resultAgrees c && resultAgrees d
    | _, _ => false
  return resultAgrees observed && resultAgrees ordinaryResult && exactEvents &&
    cells heap.project == expectedCells.map some && cells ordinaryHeap == expectedCells.map some
"""


def cpython(source, error_kind=None, missing=None):
    scope = {"__builtins__": {}}
    try:
        exec(compile(source, "<tuple spread>", "exec", dont_inherit=True, optimize=0), scope)
    except (NameError, TypeError) as error:
        assert type(error) is error_kind and getattr(error, "name", None) == missing
    else:
        assert error_kind is None
    return scope


def scalar(value):
    if value is None:
        return ".none"
    if type(value) is bool:
        return ".bool " + str(value).lower()
    assert type(value) is int
    return f".int ({value})"


def lean_tuple(value, seeded=True):
    assert type(value) is tuple
    ctor = "returnedTuple" if seeded else "tuple"
    return f".{ctor} [{', '.join(map(scalar, value))}]"


def success_checks():
    scope = cpython(SUCCESS)
    assert scope["saved"].__code__.co_cellvars == ("tail",)
    assert scope["collect"] == 101
    expected = {
        "answer": (8, None, True),
        "empty": (),
        "plain": (6,),
        "fixed_result": (False, None),
        "no_prefix_result": (),
        "lambda_result": (None,),
        "dynamic_result": (8, None, True),
    }
    for name, value in expected.items():
        assert type(scope[name]) is tuple
        assert [(type(x), x) for x in scope[name]] == [(type(x), x) for x in value]
    bindings = ['("collect", .int 101)']
    bindings.extend(f'("{key}", {lean_tuple(value)})' for key, value in expected.items())
    callees = ("saved", "saved", "saved", "fixed", "no_prefix", "via_lambda", "saved")
    receipts = [f'("{callee}", .ok ({lean_tuple(value)}))' for callee, value in zip(callees, expected.values())]
    own = ", ".join(lean_tuple(expected[name]) for name in ("answer", "empty", "plain", "dynamic_result"))
    return f"""
#guard checkRunners pythonSource .normal (.ok ()) [{', '.join(bindings)}]
  [.int 37, {own}] [{', '.join(receipts)}]
#guard checkFinite pythonSource 4 (.ok ({lean_tuple(expected["answer"], seeded=False)}))
  [.int 37, {lean_tuple(expected["answer"])}]

private def checkFuel (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let unfinished := Seeded.run .empty compiled initial 1
  return unfinished.completion == .error .directCallFuelExhausted && unfinished.calls.isEmpty &&
    unfinished.residual.lookupGlobal "answer" == none && cells unfinished.heap == [some (.int 37),
      some ({lean_tuple(expected["answer"])})]

#guard checkFuel pythonSource
"""


def failure_checks(source, kind, name, runtime_error, reached_cells, receipts):
    scope = cpython(source, kind, name)
    assert scope["answer"] == 77
    seeded_error = f'.raised (.runtime ({runtime_error}))'
    cells = ", ".join([".int 37", *map(lean_tuple, reached_cells)])
    ledger = ", ".join(f'("{callee}", .error ({seeded_error}))' for callee in receipts)
    check = f"""
#guard checkRunners pythonSource (.raised ({runtime_error})) (.error ({seeded_error}))
  [("answer", .int 77)] [{cells}] [{ledger}]
"""
    if source == REACHED:
        check += f'#guard checkFinite pythonSource 3 (.error ({runtime_error})) [{cells}]\n'
    return check


def main():
    assert sys.version_info[:3] == (3, 13, 5)
    root = Path(__file__).resolve().parents[1] / "tests/languages/python"
    shared = runpy.run_path(str(root / "source-scope/check_intake.py"))
    imports = runpy.run_path(str(root / "source-module-entry/check_return_local_call.py"))["IMPORTS"]
    imports += (
        "import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Thms",
        "meta import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Defs",
        "meta import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Defs",
        "meta import Silmaril.Languages.Python.Core.Closure.Finite.Defs",
        "meta import Mathlib.Data.List.AList",
    )
    fixtures = [(SUCCESS, success_checks())]
    fixtures.extend((case[0], failure_checks(*case)) for case in FAILURES)
    with tempfile.TemporaryDirectory() as tmp:
        source, lean = Path(tmp) / "TupleSpread.py", Path(tmp) / "TupleSpread.lean"
        declarations = []
        for i, (body, guards) in enumerate(fixtures):
            shared["emit"](source, lean, body)
            header, declaration = lean.read_text().split("public def pythonSource", 1)
            declarations.append(f"namespace Case{i}\npublic def pythonSource{declaration}\n{guards}\nend Case{i}")
        lean.write_text(header + HELPERS + "\n".join(declarations))
        shared["check_lean"](lean, "", extra_imports=imports)
    print("CPython 3.13.5 controls and ordinary, Finite, and seeded tuple-spread guards passed.")


if __name__ == "__main__":
    main()

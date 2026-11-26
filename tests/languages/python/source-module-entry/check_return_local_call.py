# SPDX-License-Identifier: MIT
"""Check returned local calls and their use as seeded module arguments."""

from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path
import runpy
import sys
import tempfile


IMPORTS = (
    "import Batteries.Data.Except",
    "import Silmaril.Languages.Python.Compile.Closure.Run.Thms",
    "import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms",
    "import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs",
    "meta import Silmaril.Languages.Python.Core.Module.Functions.Defs",
    "meta import Silmaril.Languages.Python.Core.Module.SeededCall.Defs",
    "meta import Silmaril.Languages.Python.Core.Closure.Defs",
    "meta import Silmaril.Languages.Python.Core.Closure.Executor.Defs",
)

LEAN = """
open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run
open Core.Module.SeededCall

private def integerGlobal (value : Option Core.Closure.Value) : Option Int :=
  match value with | some (.int value) => some value | _ => none

private def checkOrdinary (source : Source.Module) (completion : Completion) (output : Option Int) : Bool :=
  match compile source with
  | .error _ => false
  | .ok compiled =>
    match (runPrefix compiled.table 128 compiled.start).2 with
    | .finished result status => status == completion && integerGlobal (result.globals "answer") == output
    | _ => false

private def initialHeap : Core.Closure.Heap :=
  ⟨1, fun index => if index = 0 then some (.int 37) else none⟩

private def heapInts (heap : Core.Closure.Heap) : List (Option Int) :=
  (List.range heap.next).map (integerGlobal ∘ heap.contents)

private def seed (placement : Seeded.SeedPlacement) : Namespace :=
  Seeded.legacySeed placement

private def checkSeeded (source : Source.Module) (completion : Except Seeded.ModuleFailure Unit)
    (receipts : List (String × Result)) (cells : List Int) (tail : Option Value) : Bool :=
  match compile source with
  | .error _ => false
  | .ok compiled =>
    let accepts (space : Namespace) := Id.run do
      let run := Seeded.run space compiled initialHeap
      let some (.function f) := run.residual.lookupGlobal "f" | return false
      let some (.function g) := run.residual.lookupGlobal "g" | return false
      let expected := ((space.bindGlobal "f" (.function f)).bindGlobal "g" (.function g))
      let expected := tail.elim expected fun value => expected.bindGlobal "answer" value
      return run.completion == completion &&
        run.calls.map (fun call => (call.callee, call.observation.result)) == receipts &&
        run.calls.all (fun call => call.observation.caught.isNone) &&
        heapInts run.heap == cells.map some &&
        run.residual.moduleGlobals == expected.moduleGlobals && run.residual.builtins == expected.builtins
    accepts (seed .builtin) && accepts (seed .preamble)

private def checkNestedStops (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let [.publish "f" f, .publish "g" g, .nestedCall .., _] := compiled.instructions | return false
  let space := ((seed .builtin).bindGlobal "f" (.function f.closure)).bindGlobal "g" (.function g.closure)
  let published := [f.closure, g.closure]
  let instructions := compiled.instructions.drop 2
  let missingG : Core.Closure.Executor.CodeTable := fun key =>
    if key == g.ref.key then none else compiled.table key
  let faulted := Seeded.runInstructionsIn space ⟨missingG, initialHeap, 128, published, []⟩ instructions
  let withFallback := { space with builtins := ("f", .function f.closure) :: space.builtins }
  let shadowed := withFallback.bindGlobal "f" (.int 0)
  let masked := Seeded.runInstructionsIn shadowed ⟨compiled.table, initialHeap, 128, published, []⟩ instructions
  let live := Seeded.runInstructionsIn space ⟨compiled.table, initialHeap, 0, published, []⟩ instructions
  let .error (.directCallFault _) := faulted.completion | return false
  return heapInts faulted.heap == [some 37, some 4] &&
    faulted.calls.map (fun call => (call.callee, call.observation.result)) == [("f", .ok (.int 4))] &&
    faulted.residual.moduleGlobals == space.moduleGlobals && faulted.residual.builtins == space.builtins &&
    masked.completion == .error (.raised (.runtime .notCallable)) && heapInts masked.heap == [some 37] &&
    masked.calls.map (fun call => (call.callee, call.observation.result)) ==
      [("f", .error (.raised (.runtime .notCallable)))] &&
    masked.residual.moduleGlobals == shadowed.moduleGlobals && masked.residual.builtins == shadowed.builtins &&
    live.completion == .error .directCallFuelExhausted && heapInts live.heap == [some 37] &&
    live.calls.isEmpty && live.residual.moduleGlobals == space.moduleGlobals &&
    live.residual.builtins == space.builtins
"""

ORDINARY = """def outer():
    def pick(value):
        return value
    saved = pick
    def pick(value):
        return 9
    return saved(4)
answer = outer()
"""
ORDINARY_PRODUCT = """def target(value):
    return value
def factory(n):
    def leaf(flag):
        return target((n * n) * flag)
    return leaf
saved = factory(9)
def target(value):
    return value + 3
answer = saved(True)
"""

CAPTURES = """def f():
    owned = 4
    def leaf():
        return owned
    return leaf()

def g():
    owned = 4
    def leaf():
        return owned
    return leaf()
"""
SUCCESS = CAPTURES + "___assertEqual(f(), g())\nanswer = 8\n"
LATE_MISSING = CAPTURES + "___assertEqual(f(), missing)\nanswer = 8\n"
MASKED = CAPTURES + "f = 0\n___assertEqual(f(), g())\nanswer = 8\n"


def reference(source, placement):
    def compare(first, second):
        assert first == second

    builtins = {"___assertEqual": compare} if placement == "builtin" else {}
    namespace = {"__builtins__": builtins}
    if placement == "preamble":
        namespace["___assertEqual"] = compare
    initial = dict(namespace)
    completion = ("normal", None)
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        try:
            exec(compile(source, "<local call return>", "exec", dont_inherit=True, optimize=0), namespace)
        except NameError as error:
            completion = ("NameError", error.name)
        except TypeError:
            completion = ("TypeError", None)
    assert stdout.getvalue() == stderr.getvalue() == ""
    assert all(namespace[name] is value for name, value in initial.items())
    return completion, namespace.get("answer")


def check_fixtures(fixtures, regression):
    """Check the emitted cases in separate namespaces in one Lean process."""
    directory = Path(__file__).resolve().parent
    shared = runpy.run_path(str(directory.parent / "source-scope/check_intake.py"))
    with tempfile.TemporaryDirectory() as tmp:
        source_path, lean_path = Path(tmp) / "Example.py", Path(tmp) / "Example.lean"
        header = None
        cases = []
        for index, (source, guard) in enumerate(fixtures):
            shared["emit"](source_path, lean_path, source)
            prefix, declaration, body = lean_path.read_text(encoding="utf-8").partition("public def pythonSource")
            assert declaration and (header is None or header == prefix)
            header = prefix
            namespace = f"Fixture{index}"
            cases.append(f"namespace {namespace}\n{declaration}{body}\n{guard}\nend {namespace}\n")
        assert header is not None
        lean_path.write_text(header + regression + "\n" + "\n".join(cases), encoding="utf-8")
        shared["check_lean"](lean_path, "", extra_imports=IMPORTS)


if __name__ == "__main__":
    arity = ORDINARY.replace("saved(4)", "saved()")
    assert reference(ORDINARY_PRODUCT, "empty") == (("normal", None), 84)
    none_product = ORDINARY_PRODUCT.replace("answer = saved(True)", "flag = None\nanswer = saved(flag)")
    assert reference(none_product, "empty") == (("TypeError", None), None)
    assert reference(ORDINARY, "empty") == (("normal", None), 4)
    assert reference(arity, "empty") == (("TypeError", None), None)
    assert reference(SUCCESS, "empty") == (("NameError", "___assertEqual"), None)
    for placement in ("builtin", "preamble"):
        assert reference(SUCCESS, placement) == (("normal", None), 8)
        assert reference(LATE_MISSING, placement) == (("NameError", "missing"), None)
        assert reference(MASKED, placement) == (("TypeError", None), None)
    fixtures = (
        (ORDINARY_PRODUCT, "#guard checkOrdinary pythonSource .normal (some 84)"),
        (none_product, "#guard checkOrdinary pythonSource (.raised .multiplicationTypeError) none"),
        (ORDINARY, "#guard checkOrdinary pythonSource .normal (some 4)"),
        (arity, "#guard checkOrdinary pythonSource (.raised (.positionalArity 1 0)) none"),
        (SUCCESS, """
#guard checkOrdinary pythonSource (.raised (.nameError "___assertEqual")) none
#guard checkSeeded pythonSource (.ok ())
  [("f", .ok (.int 4)), ("g", .ok (.int 4)), ("___assertEqual", .ok .none)] [37, 4, 4] (some (.int 8))
#guard checkNestedStops pythonSource
"""),
        (LATE_MISSING, """
#guard checkSeeded pythonSource (.error (.raised (.runtime (.nameError "missing"))))
  [("f", .ok (.int 4))] [37, 4] none
"""),
        ("def outside(): return global_target()\nanswer = outside()\n", """
#guard checkOrdinary pythonSource (.raised (.nameError "global_target")) none
"""),
        ("""def outside():
    target = global_target
    def inspect():
        return target
    return target()
""", """
#guard (match compile pythonSource with | .error (.functionBody (.bodyProfile [0])) => true | _ => false)
"""),
    )
    check_fixtures(fixtures, LEAN)
    print(f"CPython {sys.version.split()[0]} and Lean checked returned local calls and seeded argument effects.")

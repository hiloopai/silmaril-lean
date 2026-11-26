# SPDX-License-Identifier: MIT
"""Compare exact None factory binding and live global lookup with CPython."""

from pathlib import Path
import runpy
import sys


REBIND = """f3 = lambda x: lambda y: global_x + y
global_x = 1
inc = f3(None)
global_x = 10
___assertEqual(inc(2), 12)
after = 9
"""

CAPTURE = """make = lambda x, y: lambda: x + y
saved = make(None, 7)
___assertEqual(saved(), 7)
after = 9
"""

ORDER = """make = lambda x: lambda: x
result = 5
{setup}result = {callee}(None{tail})
after = 9
"""

LEAN = """
private def globalLeaf (source : Source.Module) (globalValue : Int) (tail : Option Int)
    (heap : Core.Closure.Heap) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let (_, .finished ordinary (.raised (.nameError "___assertEqual"))) :=
    runPrefix compiled.table 128 compiled.start | return false
  let some (.function factory) := ordinary.globals "f3" | return false
  let some (.function leaf) := ordinary.globals "inc" | return false
  let .ok code := Core.Closure.Dispatch.resolve compiled.table leaf.code | return false
  let .ret (.binaryInt .add (.readGlobal "global_x") (.read (.local _))) := code.body | return false
  let invocation := ordinary.prepareCall .discard (.readGlobal "inc") [.literal (.int 2)]
  let .finished reached (.ok (.int result)) := (invocation.runPrefix compiled.table 128).2.state | return false
  let ordinaryOK := integerGlobal (ordinary.globals "global_x") == some globalValue && result == globalValue + 2 &&
    (ordinary.globals "after").isNone && ordinary.heap.next == 0 && reached.next == 0
  return ordinaryOK && compiled.linked.map (·.path) == [[0], [0, 0]] &&
    factory.code.layout == ⟨1, 0, 0⟩ && leaf.code.layout == ⟨1, 0, 0⟩ &&
    [Namespace.empty, seed .builtin, seed .preamble].all fun space =>
      let run := Seeded.run space compiled heap
      let enabled := (space.lookupGlobal "___assertEqual").isSome
      let expected := ((space.bindGlobal "f3" (.function factory)).bindGlobal "inc" (.function leaf))
        |>.bindGlobal "global_x" (.int globalValue)
      let expected := if enabled then tail.elim expected (fun value => expected.bindGlobal "after" (.int value))
        else expected
      let outcome : Except Seeded.ModuleFailure Unit :=
        if enabled then .ok () else .error (.raised (.runtime (.nameError "___assertEqual")))
      let calls : List (String × Result) := [("f3", .ok (.function leaf))] ++
        (if enabled then [("inc", .ok (.int (globalValue + 2))), ("___assertEqual", .ok .none)] else [])
      run.completion == outcome && heapInts run.heap == heapInts heap &&
        run.residual.moduleGlobals == expected.moduleGlobals && run.residual.builtins == expected.builtins &&
        run.calls.map (fun call => (call.callee, call.observation.result)) == calls &&
        run.calls.all (fun call => call.observation.caught.isNone)

private def capturesWithTags (scope : Source.Scope) (heap : Core.Closure.Heap)
    (closure : Core.Closure.Function) : Bool :=
  let cells := (scope.captures.map (·.name)).zip
    (closure.captures.toList.map fun cell => heap.contents cell.address)
  match cells.lookup "x", cells.lookup "y" with
  | some (some .none), some (some (.int 7)) => true
  | _, _ => false

private def capturedNone (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let some scope := compiled.checked.tree.atPath [0, 0] | return false
  let (_, .finished ordinary (.raised (.nameError "___assertEqual"))) :=
    runPrefix compiled.table 128 compiled.start | return false
  let some (.function saved) := ordinary.globals "saved" | return false
  let inv := ordinary.prepareCall .discard (.readGlobal "saved") []
  let .finished reached (.error .additionTypeError) :=
    (inv.runPrefix compiled.table 128).2.state | return false
  return reached.next == 2 && capturesWithTags scope reached saved &&
    [Namespace.empty, seed .builtin, seed .preamble].all fun space => Id.run do
      let run := Seeded.run space compiled initialHeap
      let some (.function make) := run.residual.lookupGlobal "make" | return false
      let some (.function leaf) := run.residual.lookupGlobal "saved" | return false
      let enabled := (space.lookupGlobal "___assertEqual").isSome
      let expected := (space.bindGlobal "make" (.function make)).bindGlobal "saved" (.function leaf)
      let error := if enabled then Core.Closure.RuntimeError.additionTypeError else .nameError "___assertEqual"
      let calls : List (String × Result) := [("make", .ok (.function leaf))] ++
        (if enabled then [("saved", .error (.raised (.runtime .additionTypeError)))] else [])
      return run.completion == .error (.raised (.runtime error)) && run.heap.next == 3 &&
        integerGlobal (run.heap.contents 0) == some 37 && capturesWithTags scope run.heap leaf &&
        run.residual.moduleGlobals == expected.moduleGlobals && run.residual.builtins == expected.builtins &&
        run.calls.map (fun call => (call.callee, call.observation.result)) == calls &&
        run.calls.all (fun call => call.observation.caught.isNone)

private def orderedStop (source : Source.Module) (callee : String) (ordinaryError : Core.Closure.RuntimeError)
    (seededError : Failure) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let (_, .finished ordinary (.raised actual)) := runPrefix compiled.table 128 compiled.start | return false
  let some (.function make) := ordinary.globals "make" | return false
  return actual == ordinaryError && ordinary.heap.next == 0 &&
    integerGlobal (ordinary.globals "result") == some 5 && (ordinary.globals "after").isNone &&
    [Namespace.empty, seed .builtin, seed .preamble].all fun space =>
      let run := Seeded.run space compiled initialHeap
      let before := ((space.bindGlobal "make" (.function make)).bindGlobal "result" (.int 5))
      let before := if (ordinary.globals "first").isSome then before.bindGlobal "first" (.int 1) else before
      run.completion == .error (.ofCall seededError) && heapInts run.heap == [some 37] &&
        run.residual.moduleGlobals == before.moduleGlobals && run.residual.builtins == before.builtins &&
        run.calls.map (fun call => (call.callee, call.observation.result, call.observation.caught)) ==
          [(callee, .error seededError, none)]
"""


if __name__ == "__main__":
    directory = Path(__file__).resolve().parent
    existing = runpy.run_path(str(directory / "check_return_local_call.py"))
    reference = runpy.run_path(str(directory / "check_factory_results.py"))["reference"]
    for placement in ("empty", "builtin", "preamble"):
        completion, space = reference(REBIND, placement)
        assert completion == ("NameError:___assertEqual" if placement == "empty" else "normal")
        leaf = space["inc"]
        assert leaf.__closure__ is None and leaf.__code__.co_freevars == ()
        assert leaf.__code__.co_names == ("global_x",) and leaf(2) == 12
        assert space["global_x"] == 10 and ("after" in space) == (placement != "empty")
        completion, space = reference(CAPTURE, placement)
        assert completion == ("NameError:___assertEqual" if placement == "empty" else "TypeError")
        leaf = space["saved"]
        assert leaf.__code__.co_freevars == ("x", "y")
        assert leaf.__closure__[0].cell_contents is None and leaf.__closure__[1].cell_contents == 7
        assert "after" not in space
    fixtures = [(REBIND, "#guard globalLeaf pythonSource 10 (some 9) initialHeap"), (CAPTURE, "#guard capturedNone pythonSource")]
    for callee, setup, tail, missing in (
        ("absent", "", ", first, second", "absent"),
        ("make", "", ", first, second", "first"),
        ("make", "first = 1\n", ", first, second", "second"),
        ("make", "", ", 7", None),
    ):
        source = ORDER.format(callee=callee, setup=setup, tail=tail)
        status, space = reference(source, "empty")
        assert status == (f"NameError:{missing}" if missing else "TypeError")
        assert space["result"] == 5 and "after" not in space
        error = f'(.nameError "{missing}")' if missing else "(.positionalArity 1 2)"
        seeded = f'(.raised (.runtime {error}))' if missing else ".unsupported"
        fixtures.append((source, f'#guard orderedStop pythonSource "{callee}" {error} {seeded}'))
    existing["check_fixtures"](fixtures, existing["LEAN"] + LEAN)
    print(f"CPython {sys.version.split()[0]} and Lean checked exact None binding and live factory globals.")

# SPDX-License-Identifier: MIT
"""Compare seeded factory settlement and escaped calls with CPython."""

from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path
import runpy


SUCCESS = """def make(n):
    def leaf(x):
        return n + x
    n = n + 1
    return leaf
first = make(3)
saved = first
def make():
    n = 20
    def leaf(x):
        return n + x
    return leaf
first = make()
___assertEqual(saved(2), 6)
___assertEqual(first(2), 22)
after = 9
"""

FACTORY = """def make(n):
    def leaf(x):
        return n + x
    n = n + 1
    %s
    return leaf
result = 5
result = make(3)
after = 9
"""

FAULT = FACTORY % "def inspect(): return n\n    inspect()"
ASSERTION = FACTORY % "assert False"
ARGUMENT = """def make(n):
    def leaf(x):
        return (n + x) + missing
    return leaf
saved = make(3)
___assertEqual(saved(1), 4)
after = 9
"""


CHAIN = """def outer(a, b, c):
    def middle(x, y, z):
        x = x + a
        def leaf():
            return c + (y + b)
        b = x + z
        def inspect():
            return y
        inspect()
        return leaf
    return middle
active = outer(1, 2, 3)
result = active(2, 4, 6)
___assertEqual(result(), 16)
after = 9
"""

ALIASED_CHAIN = """def origin(seed):
    def next(x):
        def leaf(n):
            return seed + x + n
        return leaf
    return next
active = origin(5)
saved = active
active = origin(15)
left = saved(1)
right = active(4)
___assertEqual(left(1), 7)
___assertEqual(right(1), 20)
after = 9
"""

FACTOR = 2 ** 100
PRODUCT = """def target(value):
    return value
def make(n):
    def leaf():
        return target((n * n) * numeric)
    return leaf
saved = make({factor})
def target(value):
    return value + 3
numeric = 1 == {test}
___assertEqual(saved(), {result})
after = 9
"""


LEAN = """
private def returned (calls : List Seeded.CallEvent) : List (String × Result) :=
  calls.map fun call => (call.callee, call.observation.result)

private def factorySuccess (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  return [Namespace.empty, seed .builtin, seed .preamble].all fun space =>
    Id.run do
      let run := Seeded.run space compiled initialHeap
      let some (.function saved) := run.residual.lookupGlobal "saved" | return false
      let some (.function first) := run.residual.lookupGlobal "first" | return false
      let some (.function live) := run.residual.lookupGlobal "make" | return false
      let expected := ((space.bindGlobal "first" (.function saved)).bindGlobal "saved" (.function saved))
        |>.bindGlobal "make" (.function live) |>.bindGlobal "first" (.function first)
      let factories := [("make", .ok (.function saved)), ("make", .ok (.function first))]
      let outer := ("___assertEqual", .ok .none)
      let (completion, bindings, receipts) :=
        if (space.lookupGlobal "___assertEqual").isSome then
          (.ok (), expected.bindGlobal "after" (.int 9),
            factories ++ [("saved", .ok (.int 6)), outer, ("first", .ok (.int 22)), outer])
        else (.error (.raised (.runtime (.nameError "___assertEqual"))), expected, factories)
      return run.completion == completion && returned run.calls == receipts &&
        run.calls.all (fun call => call.observation.caught.isNone) &&
        run.residual.moduleGlobals == bindings.moduleGlobals && run.residual.builtins == bindings.builtins &&
        saved.captures.toList.map (·.address) == [1] && first.captures.toList.map (·.address) == [2] &&
        heapInts run.heap == [some 37, some 4, some 20]

private def factoryStops (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let .publish "make" top :: _ := compiled.instructions | return false
  let space := seed .builtin
  let expected := (space.bindGlobal "make" (.function top.closure)).bindGlobal "result" (.int 5)
  let missing : Core.Closure.Executor.CodeTable := fun key => if key == 2 then none else compiled.table key
  let wrong : Core.Closure.Executor.CodeTable := fun key => if key == 2 then compiled.table 1 else compiled.table key
  let incomplete := Seeded.run space compiled initialHeap 3
  let fault := Seeded.runInstructions space compiled.instructions missing initialHeap 128
  let mismatch := Seeded.runInstructions space compiled.instructions wrong initialHeap 128
  let .error (.directCallFault (.layoutMismatch ..)) := mismatch.completion | return false
  return incomplete.completion == .error .directCallFuelExhausted &&
    fault.completion == .error (.directCallFault (.missingCode 2)) &&
    [incomplete, fault, mismatch].all (fun run =>
      run.calls.isEmpty && run.residual.moduleGlobals == expected.moduleGlobals &&
      run.residual.builtins == expected.builtins && heapInts run.heap == [some 37, some 4])

private def factoryFailure (source : Source.Module) (callee : String) (failure : Failure)
    (heap : List Int) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let space := seed .builtin
  let run := Seeded.run space compiled initialHeap
  return run.completion == .error (.ofCall failure) &&
    returned run.calls == [(callee, .error failure)] &&
    run.calls.all (fun call => call.observation.caught.isNone) &&
    run.residual.lookupGlobal "after" == none && run.residual.lookupGlobal "result" == some (.int 5) &&
    run.residual.builtins == space.builtins && heapInts run.heap == heap.map some

private def escapedFailure (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let space := seed .builtin
  let failed := Seeded.run space compiled initialHeap
  let missing : Core.Closure.Executor.CodeTable := fun key => if key == 1 then none else compiled.table key
  let fault := Seeded.runInstructions space compiled.instructions missing initialHeap 128
  let some (.function result) := failed.residual.lookupGlobal "saved" | return false
  return failed.completion == .error (.raised (.runtime (.nameError "missing"))) &&
    returned failed.calls == [("make", .ok (.function result)), ("saved", .error (.raised (.runtime (.nameError "missing"))))] &&
    fault.completion == .error (.directCallFault (.missingCode 1)) &&
    returned fault.calls == [("make", .ok (.function result))] &&
    [failed, fault].all (fun run => run.residual.lookupGlobal "after" == none &&
      run.calls.all (fun call => call.observation.caught.isNone) &&
      run.residual.builtins == space.builtins && heapInts run.heap == [some 37, some 3])

private def escapedOutsideHelper (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let run := Seeded.run (seed .builtin) compiled initialHeap
  let some (.function result) := run.residual.lookupGlobal "saved" | return false
  return run.completion == .error .unsupported &&
    returned run.calls == [("make", .ok (.function result)), ("saved", .error .unsupported)] &&
    run.calls.all (fun call => call.observation.caught.isNone) &&
    run.residual.lookupGlobal "after" == none && heapInts run.heap == [some 37, some 3]

private def chainSuccess (source : Source.Module) (binds : List (String × String))
    (sums : List (String × Int)) (cells : List Int) : Bool := Id.run do
  let .ok compiled := compile source | return false
  return [Namespace.empty, seed .builtin, seed .preamble].all fun space =>
    Id.run do
      let run := Seeded.run space compiled initialHeap
      let .some factories := binds.mapM (fun (callee, target) =>
        match run.residual.lookupGlobal target with
        | some (.function fn) => some (callee, (Except.ok (.function fn) : Result))
        | _ => none) | return false
      let seeded := (space.lookupGlobal "___assertEqual").isSome
      let helperCalls : List (String × Result) := sums.flatMap fun (callee, value) =>
        [(callee, .ok (.int value)), ("___assertEqual", .ok .none)]
      let completion : Except Seeded.ModuleFailure Unit :=
        if seeded then .ok () else .error (.raised (.runtime (.nameError "___assertEqual")))
      return run.completion == completion && heapInts run.heap == cells.map some &&
        run.residual.builtins == space.builtins &&
        run.residual.lookupGlobal "after" == (if seeded then some (Value.int 9) else none) &&
        returned run.calls == factories ++ (if seeded then helperCalls else []) &&
        run.calls.all (fun call => call.observation.caught.isNone)

private def chainStops (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let space := seed .builtin
  let missing : Core.Closure.Executor.CodeTable := fun key => if key == 3 then none else compiled.table key
  let fault := Seeded.runInstructions space compiled.instructions missing initialHeap
  let some (.function known) := fault.residual.lookupGlobal "active" | return false
  let prior : List (String × Result) := [("outer", .ok (.function known))]
  let cells := [some 37, some 1, some 3, some 4, some 9]
  let earlier := Seeded.runInstructions space (compiled.instructions.take 2) compiled.table initialHeap
  let samePrefix (run : Seeded.Observation) :=
    run.residual.moduleGlobals == earlier.residual.moduleGlobals && run.residual.builtins == space.builtins
  let exhausted := (List.range 20).any fun fuel =>
    let run := Seeded.run space compiled initialHeap fuel
    run.completion == .error .directCallFuelExhausted && samePrefix run &&
      returned run.calls == prior && heapInts run.heap == cells
  let later := compiled.instructions.drop 2
  let base : Seeded.CallContext := { table := compiled.table, heap := earlier.heap, fuel := 128 }
  let imported := Seeded.runInstructionsIn earlier.residual base later
  let fallback := { earlier.residual with builtins := ("active", .function known) :: space.builtins }
  let masked := fallback.bindGlobal "active" (.int 0)
  let shadowed := Seeded.runInstructionsIn masked { base with escaped := [known] } later
  return fault.completion == .error (.directCallFault (.missingCode 3)) &&
    samePrefix fault && returned fault.calls == prior && heapInts fault.heap == cells &&
    exhausted && imported.completion == .error .unsupported && samePrefix imported &&
    returned imported.calls == [("active", .error .unsupported)] &&
    heapInts imported.heap == heapInts earlier.heap &&
    shadowed.completion == .error (.raised (.runtime .notCallable)) &&
    returned shadowed.calls == [("active", .error (.raised (.runtime .notCallable)))] &&
    shadowed.residual.moduleGlobals == masked.moduleGlobals && shadowed.residual.builtins == masked.builtins &&
    heapInts shadowed.heap == heapInts earlier.heap

private def chainException (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let run := Seeded.run (seed .builtin) compiled initialHeap
  let some (.function active) := run.residual.lookupGlobal "active" | return false
  return run.completion == .error (.raised (.assertionError .empty)) &&
    returned run.calls == [("outer", .ok (.function active)), ("active", .error (.raised (.assertionError .empty)))] &&
    run.calls.all (fun call => call.observation.caught.isNone) &&
    run.residual.lookupGlobal "result" == none && run.residual.lookupGlobal "after" == none &&
    heapInts run.heap == [some 37, some 1, some 3, some 4, some 9]


private def productOutcome (source : Source.Module) (factor : Int) (inner : Result) : Bool := Id.run do
  let .ok compiled := compile source | return false
  return [Namespace.empty, seed .builtin, seed .preamble].all fun space =>
    Id.run do
      let run := Seeded.run space compiled initialHeap
      let some (.function saved) := run.residual.lookupGlobal "saved" | return false
      let some (.function target) := run.residual.lookupGlobal "target" | return false
      let seeded := (space.lookupGlobal "___assertEqual").isSome
      let completed := (if seeded then inner else .error (.raised (.runtime (.nameError "___assertEqual"))))
        |>.map (fun _ => ()) |>.mapError Seeded.ModuleFailure.ofCall
      let calls := [("make", .ok (.function saved))] ++
        (if seeded then [("saved", inner)] ++ (if inner.isOk then [("___assertEqual", .ok .none)] else []) else [])
      return run.completion == completed && returned run.calls == calls &&
        run.calls.all (fun call => call.observation.caught.isNone) &&
        run.residual.lookupGlobal "after" == (if completed.isOk then some (Value.int 9) else none) &&
        run.residual.builtins == space.builtins && heapInts run.heap == [some 37, some factor] &&
        saved.captures.toList.map (·.address) == [1] && target.code.key == 3

"""


def reference(source, placement):
    def equal(left, right):
        assert type(left) is type(right) is int and left == right

    space = {"__builtins__": {"___assertEqual": equal} if placement == "builtin" else {}}
    if placement == "preamble":
        space["___assertEqual"] = equal
    completion = "normal"
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        try:
            exec(compile(source, "<factory>", "exec", dont_inherit=True, optimize=0), space)
        except AssertionError as error:
            assert not error.args
            completion = "AssertionError"
        except NameError as error:
            completion = f"NameError:{error.name}"
        except TypeError:
            completion = "TypeError"
    assert stdout.getvalue() == stderr.getvalue() == ""
    return completion, space


if __name__ == "__main__":
    directory = Path(__file__).resolve().parent
    existing = runpy.run_path(str(directory / "check_return_local_call.py"))
    for placement in ("empty", "builtin", "preamble"):
        completion, space = reference(SUCCESS, placement)
        assert completion == ("NameError:___assertEqual" if placement == "empty" else "normal")
        assert space.get("after") == (None if placement == "empty" else 9)
        assert space["saved"].__closure__[0].cell_contents == 4
        assert space["first"].__closure__[0].cell_contents == 20
        assert space["first"] is not space["saved"]
    completion, space = reference(ASSERTION, "builtin")
    assert completion == "AssertionError" and space["result"] == 5 and "after" not in space
    assert reference(ARGUMENT, "builtin")[0] == "NameError:missing"
    missing_callee = FAULT.replace("make(3)", "absent(missing)")
    masked = FAULT.replace("result = make(3)", "make = 0\nresult = make(missing)")
    noncallable = masked.replace("make(missing)", "make(3)")
    assert reference(missing_callee, "empty")[0] == "NameError:absent"
    assert reference(masked, "empty")[0] == "NameError:missing"
    assert reference(noncallable, "empty")[0] == "TypeError"
    for source, output, expected in ((CHAIN, "result", 16), (ALIASED_CHAIN, "left", 7)):
        for placement in ("empty", "builtin", "preamble"):
            completion, space = reference(source, placement)
            assert completion == ("NameError:___assertEqual" if placement == "empty" else "normal")
            assert space.get("after") == (None if placement == "empty" else 9)
            assert (space[output]() if source == CHAIN else space[output](1)) == expected
    chain_exception = CHAIN.replace("        return leaf", "        assert False\n        return leaf")
    completion, space = reference(chain_exception, "builtin")
    assert completion == "AssertionError" and "active" in space and "result" not in space and "after" not in space
    product = PRODUCT.format(factor=FACTOR, test=1, result=FACTOR * FACTOR + 3)
    zero_product = PRODUCT.format(factor=FACTOR, test=2, result=3)
    product_failures = (
        (product.replace("(n * n) * numeric", "n * target"), "TypeError", ".multiplicationTypeError"),
        (product.replace("(n * n) * numeric", "(target * missing) * n"), "NameError:missing", '(.nameError "missing")'),
        (product.replace("return target((n * n) * numeric)", "return unavailable((target * missing) * n)"),
         "NameError:unavailable", '(.nameError "unavailable")'),
    )
    product_fixtures = []
    for source, answer in ((product, FACTOR * FACTOR + 3), (zero_product, 3)):
        for placement in ("empty", "builtin", "preamble"):
            completion, space = reference(source, placement)
            assert completion == ("NameError:___assertEqual" if placement == "empty" else "normal")
            assert type(space["saved"]()) is int and space["saved"]() == answer
        product_fixtures.append((source, f"#guard productOutcome pythonSource {FACTOR} (.ok (.int {answer}))"))
    for source, expected, error in product_failures:
        for placement in ("builtin", "preamble"):
            completion, space = reference(source, placement)
            assert completion == expected and "after" not in space
        product_fixtures.append((source, f"#guard productOutcome pythonSource {FACTOR} (.error (.raised (.runtime {error})))"))
    fixtures = (
        (CHAIN, """
#guard chainSuccess pythonSource [("outer", "active"), ("active", "result")] [("result", 16)] [37, 1, 3, 4, 9]
#guard chainStops pythonSource
"""),
        (ALIASED_CHAIN, """
#guard chainSuccess pythonSource [("origin", "saved"), ("origin", "active"), ("saved", "left"), ("active", "right")]
  [("left", 7), ("right", 20)] [37, 5, 15, 1, 4]
"""),
        (chain_exception, "#guard chainException pythonSource"),
        (SUCCESS, "#guard factorySuccess pythonSource"),
        (FAULT, "#guard factoryStops pythonSource"),
        (ARGUMENT, "#guard escapedFailure pythonSource"),
        (ARGUMENT.replace("___assertEqual(saved(1), 4)", "saved(1)"), "#guard escapedOutsideHelper pythonSource"),
        (ARGUMENT.replace("___assertEqual(saved(1), 4)", "___assertEqual = 0\n___assertEqual(saved(1), 4)"),
         "#guard escapedOutsideHelper pythonSource"),
        (ASSERTION, '#guard factoryFailure pythonSource "make" (.raised (.assertionError .empty)) [37, 4]'),
        (missing_callee, '#guard factoryFailure pythonSource "absent" (.raised (.runtime (.nameError "absent"))) [37]'),
        (masked, '#guard factoryFailure pythonSource "make" (.raised (.runtime (.nameError "missing"))) [37]'),
        (noncallable, '#guard factoryFailure pythonSource "make" (.raised (.runtime .notCallable)) [37]'),
        (FAULT.replace("make(3)", "make(True)"), '#guard factoryFailure pythonSource "make" .unsupported [37]'),
        (FAULT.replace("return leaf", "return n"), '#guard factoryFailure pythonSource "make" .unsupported [37]'),
    )
    existing["check_fixtures"]((*fixtures, *product_fixtures), existing["LEAN"] + LEAN)
    print("CPython and Lean verified factory results, captured cells, and seeded stops.")

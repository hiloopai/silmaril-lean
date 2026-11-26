# SPDX-License-Identifier: MIT
"""Check module co_varnames compilation and execution against CPython."""

import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


SOURCE = """def probe():
    first = later
    later = 3
    first = later
    def nested():
        child_local = 8
        child_local = 9
    later = 4
    return first

def replacement():
    new = 3

def empty():
    pass

def with_parameter(value):
    return value

def with_cell():
    owned = 4
    def captured():
        return owned

alias = probe
assert "later" in alias.__code__.co_varnames
probe = replacement
assert "new" in probe.__code__.co_varnames
"""

CPYTHON = """
import json
import sys
import types

def tuples(code):
    yield code.co_varnames
    for child in code.co_consts:
        if isinstance(child, types.CodeType):
            yield from tuples(child)

with open(sys.argv[1], 'rb') as source:
    unit = compile(source.read(), sys.argv[1], 'exec', dont_inherit=True, optimize=0)
namespace = {'__builtins__': {}}
exec(unit, namespace)
if len(sys.argv) == 3:
    assert namespace['alias'] is not namespace['probe']
    assert 'first' not in namespace['probe'].__code__.co_varnames
    assert 'child_local' not in namespace['alias'].__code__.co_varnames
children = [item for item in unit.co_consts if isinstance(item, types.CodeType)]
print(json.dumps([sys.version.split()[0], [names for child in children for names in tuples(child)]]))
"""

EXPECTED = [["later", "first", "nested"], ["child_local"], ["new"], [], ["value"], ["captured"], []]
EMITTED = ["later", "first", "later", "later", "first", "nested", "later", "first"]

IMPORTS = ("import Batteries.Data.Except",) + tuple(
    f"{prefix} Silmaril.Languages.Python.{module}"
    for module in (
        "Compile.Closure.VarNames.Thms",
        "Compile.Closure.Link.Defs",
        "Compile.ModuleEntry.Functions.Defs",
        "Compile.ModuleEntry.Functions.Run.Thms",
        "Compile.ModuleEntry.Functions.Run.Seeded.Thms",
        "Core.Closure.Dispatch.Defs",
        "Core.Closure.Defs",
        "Core.Module.SeededCall.Defs",
    )
    for prefix in ("import", "meta import")
)

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure
open Compile.ModuleEntry.Functions

private def observations (source : Module) :
    Option (List (Option (List String)) × List String × Bool) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let blocks := compiled.linked
  let root ← blocks[0]?
  let evidence ← VarNames.checked? compiled.checked.tree blocks ⟨0, root.entry.layout⟩
  let tuples := compiled.entries.map (·.definition.varnames)
  unless tuples == blocks.map (·.entry.definition.varnames) do none
  let wrongLayout := VarNames.checked? compiled.checked.tree blocks ⟨0, ⟨0, 0, 0⟩⟩
  return (tuples, evidence.emittedNames, wrongLayout.isNone)

private def liveReads (source : Module) : Bool :=
  match check source with
  | .ok checked =>
    match checked.actions.drop 5 with
    | [.scalar (.assign "alias" _ (.read "probe" _)),
       .assertVarNames "alias" _ [108, 97, 116, 101, 114],
       .scalar (.assign "probe" _ (.read "replacement" _)),
       .assertVarNames "probe" _ [110, 101, 119]] => true
    | _ => false
  | .error _ => false

private def ordinary (source : Module) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let (log, .finished session .normal) :=
    Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 64 compiled.start | return false
  let some (.function old) := session.globals "alias" | return false
  let some (.function current) := session.globals "probe" | return false
  let some stale := compiled.entries[1]? | return false
  let check := Compile.ModuleEntry.Functions.Run.checkVarNames
  return log.isEmpty && old.code.key == 0 && current.code.key == 2 &&
    check (fun _ => none) session "alias" [108, 97, 116, 101, 114] ==
      .error (.codeFault (.missingCode old.code.key)) &&
    check (fun _ => some stale) session "alias" [108, 97, 116, 101, 114] ==
      .error (.codeFault (.layoutMismatch old.code.layout stale.layout))

#guard liveReads pythonSource
#guard ordinary pythonSource
private def seededLookup (source : Module) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let .publish "probe" probe :: _ := compiled.instructions | return false
  let some stale := compiled.entries[1]? | return false
  let check := Compile.ModuleEntry.Functions.Run.Seeded.checkVarNames
  let needle := [108, 97, 116, 101, 114]
  return [Core.Module.SeededCall.Namespace.empty,
    Compile.ModuleEntry.Functions.Run.Seeded.legacySeed .builtin,
    Compile.ModuleEntry.Functions.Run.Seeded.legacySeed .preamble].all fun seed =>
    let name := "seeded_metadata_target"
    let provided := { seed with builtins := (name, .function probe.closure) :: seed.builtins }
    check provided compiled.table name needle == .ok () &&
    check (provided.bindGlobal name .none) compiled.table name needle == .error .unsupported &&
    check (provided.bindGlobal name (.builtin .int)) compiled.table name needle == .error .unsupported &&
    check provided (fun _ => none) name needle == .error (.varNamesFault (.missingCode probe.ref.key)) &&
    check provided (fun _ => some stale) name needle ==
      .error (.varNamesFault (.layoutMismatch probe.ref.layout stale.layout))

#guard seededLookup pythonSource
#print axioms Compile.ModuleEntry.Functions.Run.advance_assertVarNames
"""

EXACT_NEEDLE = r'''def inspect():
    pass
assert "\ud800" in inspect.__code__.co_varnames
'''

NEEDLE_LEAN = """
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions

#guard (match check pythonSource with
  | .ok checked => match checked.actions with
    | [.define "inspect" .., .assertVarNames "inspect" _ [55296]] => true
    | _ => false
  | .error _ => false)
"""


CASES = (
    ("def target(): pass", 'assert "missing" in target.__code__.co_varnames',
     "AssertionError", ".assertionError", "(.raised (.assertionError .empty))"),
    ("", 'assert "x" in unbound.__code__.co_varnames',
     "NameError", '(.raised (.nameError "unbound"))', '(.raised (.runtime (.nameError "unbound")))'),
    ("target = 9", 'assert "x" in target.__code__.co_varnames',
     "AttributeError", ".unsupportedVarNamesReceiver", ".unsupported"),
    ("def target(parameter): pass", 'assert "missing" in target.__code__.co_varnames',
     "AssertionError", ".assertionError", "(.raised (.assertionError .empty))"),
    ("def target(parameter, second): return parameter", 'assert "parameter" in target.__code__.co_varnames',
     "normal", "(.unprofiledVarNames ⟨0, ⟨2, 0, 0⟩⟩)", ".unsupported"),
    ("def target():\n    \U00010400 = 1\n"
     'assert "\\U00010400" in target.__code__.co_varnames',
     r'assert "\ud801\udc00" in target.__code__.co_varnames',
     "AssertionError", ".assertionError", "(.raised (.assertionError .empty))"),
)

CPYTHON_COMPLETION = """
import json
import sys

space = {'__builtins__': {}}
with open(sys.argv[1], 'rb') as source:
    unit = compile(source.read(), sys.argv[1], 'exec', dont_inherit=True, optimize=0)
try:
    exec(unit, space)
    completion = 'normal'
except (AssertionError, NameError, AttributeError) as error:
    completion = type(error).__name__
print(json.dumps([completion, space.get('before'), space.get('tail')]))
"""

COMPLETION_LEAN = """
open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run

private def completion (source : Module) : Option Completion := do
  let compiled ← (compile source).toOption
  let heap ← (Core.Closure.Heap.empty.reserve 1).write ⟨0⟩ (.int 9)
  let initial := State.ready (seed .empty heap) compiled.instructions
  let (log, .finished session result) := runPrefix compiled.table 64 initial | none
  let some (.int 5) := session.globals "before" | none
  let some (some (.int 9)) := session.heap.lookup ⟨0⟩ | none
  if log.isEmpty && (session.globals "tail").isNone && session.heap.next == 1 then some result
  else none
"""

SEEDED_LEAN = """
private def seededFailure (source : Module) (expected : Seeded.ModuleFailure) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let some heap := (Core.Closure.Heap.empty.reserve 1).write ⟨0⟩ (.int 9) | return false
  return [Core.Module.SeededCall.Namespace.empty, Seeded.legacySeed .builtin, Seeded.legacySeed .preamble].all
    fun space => Id.run do
      let result := Seeded.run space compiled heap
      let some (some (.int 9)) := result.heap.lookup ⟨0⟩ | return false
      return result.completion == .error expected && result.calls.isEmpty &&
        result.heap.next == 1 && result.residual.builtins == space.builtins &&
        Core.Module.SeededCall.lookupBinding result.residual.moduleGlobals "before" == some (.int 5) &&
        (Core.Module.SeededCall.lookupBinding result.residual.moduleGlobals "tail").isNone
"""

RETAINED = """def entry():
    retained = 7
    def child():
        assert retained == 7
    child()

def original():
    old = 1

def replacement():
    pass

target = original
alias = target
entry()
assert "old" in target.__code__.co_varnames
target = replacement
assert "old" in alias.__code__.co_varnames
before = 5
assert "old" in target.__code__.co_varnames
tail = 6
"""

RETAINED_LEAN = """
open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run

private def retained (source : Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let .publish "entry" entry :: .publish "original" original :: .publish "replacement" replacement :: _ :=
    compiled.instructions | return false
  return [Core.Module.SeededCall.Namespace.empty, Seeded.legacySeed .builtin, Seeded.legacySeed .preamble].all
    fun space => Id.run do
      let result := Seeded.run space compiled
      let [receipt] := result.calls | return false
      let some (some (.int 7)) := result.heap.lookup ⟨0⟩ | return false
      let expected := space.bindGlobal "entry" (.function entry.closure)
      let expected := expected.bindGlobal "original" (.function original.closure)
      let expected := expected.bindGlobal "replacement" (.function replacement.closure)
      let expected := expected.bindGlobal "alias" (.function original.closure)
      let expected := expected.bindGlobal "target" (.function replacement.closure)
      let expected := expected.bindGlobal "before" (.int 5)
      return result.completion == .error (.raised (.assertionError .empty)) && result.heap.next == 1 &&
        receipt.callee == "entry" && receipt.observation.result == .ok .none &&
        receipt.observation.caught.isNone && result.residual.builtins == expected.builtins &&
        result.residual.moduleGlobals == expected.moduleGlobals

#guard retained pythonSource
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.effect_assertVarNames
"""


PARAMETERS_SOURCE = """def unread(parameter):
    pass

def ordered(initial):
    first = later
    later = 3
    changed = initial
    initial = 8
    value = later
    return first

def owns_capture(parameter):
    def nested():
        return parameter
    return nested

assert "parameter" in unread.__code__.co_varnames
assert "initial" in ordered.__code__.co_varnames
assert "later" in ordered.__code__.co_varnames
"""

PARAMETER_TUPLES = [["parameter"], ["initial", "later", "first", "changed", "value"],
                    ["parameter", "nested"], []]

PARAMETERS_LEAN = """
open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run

private def parameterProfile (source : Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let blocks := compiled.linked
  let .finished _ .normal := (runPrefix compiled.table 64 compiled.start).2 | return false
  let some unread := blocks[0]? | return false
  let some ordered := blocks[1]? | return false
  let some first := Compile.Closure.VarNames.checked? compiled.checked.tree blocks ⟨0, unread.entry.layout⟩ | return false
  let some second := Compile.Closure.VarNames.checked? compiled.checked.tree blocks ⟨1, ordered.entry.layout⟩ | return false
  let emptyParameters : Core.Closure.Parameters unread.entry.layout := ⟨[], by simp⟩
  let badEntry := { unread.entry with definition := { unread.entry.definition with parameters := emptyParameters } }
  let badBlocks := { unread with entry := badEntry } :: blocks.drop 1
  return first.emittedNames.isEmpty && first.tuple == ["parameter"] &&
    second.emittedNames == ["later", "first", "later", "initial", "changed", "initial", "later", "value", "first"] &&
    compiled.entries.map (·.definition.varnames) ==
      [some ["parameter"], some ["initial", "later", "first", "changed", "value"], none, none] &&
    (Compile.Closure.VarNames.checked? compiled.checked.tree badBlocks ⟨0, unread.entry.layout⟩).isNone &&
    [Core.Module.SeededCall.Namespace.empty, Seeded.legacySeed .builtin, Seeded.legacySeed .preamble].all
      (fun space =>
        let result := Seeded.run space compiled
        result.completion == .ok () && result.calls.isEmpty && result.heap.next == 0)

#guard parameterProfile pythonSource
#print axioms Compile.Closure.VarNames.Evidence.tuple_linked_parameters
#print axioms Compile.Closure.VarNames.Evidence.tuple_single_parameter
#print axioms Compile.Closure.VarNames.Evidence.tuple_without_emitted_names
"""


if __name__ == "__main__":
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    with tempfile.TemporaryDirectory() as temporary:
        source = Path(temporary) / "Example.py"
        destination = Path(temporary) / "Example.lean"
        shared["emit"](source, destination, SOURCE)
        result = subprocess.run([sys.executable, "-I", "-c", CPYTHON, str(source), "aliases"], check=True,
                                text=True, capture_output=True, timeout=10)
        version, tuples = json.loads(result.stdout)
        assert result.stderr == ""
        if version == "3.13.5":
            assert tuples == EXPECTED, tuples
            print(f"CPython {version} matched the fast-local and module-rebinding fixtures.")
        expected = ", ".join(f"some {json.dumps(names)}" for names in EXPECTED[:5])
        lean = LEAN + (
            f"\n#guard observations pythonSource == some ([{expected}, none, none], "
            f"{json.dumps(EMITTED)}, true)\n"
        )
        shared["check_lean"](destination, lean, extra_imports=IMPORTS)
        shared["emit"](source, destination, EXACT_NEEDLE)
        shared["check_lean"](destination, NEEDLE_LEAN, extra_imports=IMPORTS)
        for setup, statement, cpython, lean_outcome, seeded_outcome in CASES:
            fixture = f"{setup}\nbefore = 5\n{statement}\ntail = 6\n"
            shared["emit"](source, destination, fixture)
            result = subprocess.run([sys.executable, "-I", "-c", CPYTHON_COMPLETION, str(source)],
                                    check=True, text=True, capture_output=True, timeout=10)
            assert result.stderr == ""
            if version == "3.13.5":
                assert json.loads(result.stdout) == [cpython, 5, 6 if cpython == "normal" else None]
            lean = COMPLETION_LEAN + f"\n#guard completion pythonSource == some {lean_outcome}\n"
            lean += SEEDED_LEAN + f"\n#guard seededFailure pythonSource {seeded_outcome}\n"
            shared["check_lean"](destination, lean, extra_imports=IMPORTS)
        shared["emit"](source, destination, RETAINED)
        result = subprocess.run([sys.executable, "-I", "-c", CPYTHON_COMPLETION, str(source)],
                                check=True, text=True, capture_output=True, timeout=10)
        assert result.stderr == ""
        if version == "3.13.5":
            assert json.loads(result.stdout) == ["AssertionError", 5, None]
        shared["check_lean"](destination, RETAINED_LEAN, extra_imports=IMPORTS)
        shared["emit"](source, destination, PARAMETERS_SOURCE)
        result = subprocess.run([sys.executable, "-I", "-c", CPYTHON, str(source)], check=True,
                                text=True, capture_output=True, timeout=10)
        assert result.stderr == ""
        if version == "3.13.5":
            assert json.loads(result.stdout) == [version, PARAMETER_TUPLES]
        shared["check_lean"](destination, PARAMETERS_LEAN, extra_imports=IMPORTS)
        for declaration in ("value=missing()", "*value", "*, value", "value: int"):
            shared["emit"](source, destination, f"def inspect({declaration}): pass\n")
            shared["check_lean"](destination, """
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run

#guard (match compile pythonSource with
  | .error (.source (.functionBody .parameterProfile)) => true
  | _ => false)
""", extra_imports=IMPORTS)
        for statement, diagnostic in (
            ('assert "x" not in inspect.__code__.co_varnames', ".expressionProfile"),
            ('assert "x" in inspect().__code__.co_varnames', ".expressionProfile"),
            ('assert "x" in inspect.__code__.co_varnames, "message"', ".assertionMessage"),
        ):
            shared["emit"](source, destination, f"def inspect(): pass\n{statement}\n")
            shared["check_lean"](destination, f"""
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions

#guard (match check pythonSource with
  | .error (.scalar {diagnostic}) => true
  | _ => false)
""", extra_imports=IMPORTS)

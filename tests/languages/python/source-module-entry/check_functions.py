# SPDX-License-Identifier: MIT
"""Check module definition and positional call operands through AST emission."""

from pathlib import Path
import runpy
import tempfile


IMPORTS = (
    "import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Thms",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Defs",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Defs",
    "meta import Silmaril.Languages.Python.Compile.Closure.Body.Defs",
    "meta import Silmaril.Languages.Python.Core.Closure.Defs",
)

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions
"""


if __name__ == "__main__":
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    with tempfile.TemporaryDirectory() as tmp:
        source = Path(tmp) / "Example.py"
        generated = Path(tmp) / "Example.lean"
        shared["emit"](source, generated, """
value = 1
def read(argument):
    return value
def shadow(value):
    return value
value = 2
observed = read(9)
shadow(3)
assert shadow(1)
""")
        shared["check_lean"](generated, LEAN + """
private def hasExpectedActions : Bool :=
  match check pythonSource with
  | .error _ => false
  | .ok compiled =>
    match compiled.actions with
    | [.scalar (.assign "value" _ (.integer 1)),
       .define "read" _ first firstParameters (.ret (.globalName "value")),
       .define "shadow" _ second secondParameters (.ret (.read (.local slot))),
       .scalar (.assign "value" _ (.integer 2)),
       .call (.store "observed" _) "read" _ [.integer 9],
       .call .discard "shadow" _ [.integer 3],
       .call .assertion "shadow" _ [.integer 1]] =>
      first.scope.context.path == [0] && second.scope.context.path == [1] &&
      first.scope.access "value" == some .implicitGlobal &&
      second.scope.access "value" == some .local &&
      (firstParameters.slots.map (Compile.Closure.parameterName first.scope)) == ["argument"] &&
      (secondParameters.slots.map (Compile.Closure.parameterName second.scope)) == ["value"] &&
      slot.val == 0
    | _ => false

#guard hasExpectedActions
#print axioms Positional.length
#print axioms global_read_resolved
""", extra_imports=IMPORTS)
        shared["emit"](source, generated, """
def read():
    global absent
    return absent
read()
""")
        shared["check_lean"](generated, LEAN + """
#guard (match check pythonSource with
  | .ok compiled => match compiled.actions with
    | [.define "read" _ child _ (.ret (.globalName "absent")), .call .discard "read" _ []] =>
      child.scope.access "absent" == some .declaredGlobal
    | _ => false
  | .error _ => false)
""", extra_imports=IMPORTS)
        shared["emit"](source, generated, """
def read(value):
    return value
read(value=1)
""")
        shared["check_lean"](generated, LEAN + """
#guard (match check pythonSource with | .error .argumentProfile => true | _ => false)
""", extra_imports=IMPORTS)
        generator_cases = (
            ("def gen():\n    if False: yield 1\n    return 2\n", "(.unsupportedGenerator [0])"),
            ("def gen(value=0): yield value\n", "(.unsupportedGenerator [0])"),
            ("def outer():\n    def gen(value=0): yield value\n    return 2\n",
             "(.unsupportedGenerator [0, 0])"),
        )
        for function, diagnostic in generator_cases:
            shared["emit"](source, generated, "seed = 1\n" + function)
            shared["check_lean"](generated, LEAN + f"""
#guard (match check pythonSource with
  | .error (.functionBody {diagnostic}) => true
  | _ => false)
""", extra_imports=IMPORTS)

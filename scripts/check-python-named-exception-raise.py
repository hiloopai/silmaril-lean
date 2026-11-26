# SPDX-License-Identifier: MIT
"""Replay named stock raises and explicit empty constructor calls on CPython 3.13.5."""

import argparse
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


RAISE = runpy.run_path(str(Path(__file__).with_name("check-python-stock-exception-raise.py")))
SUITE = RAISE["SUITE"]
INTAKE = RAISE["INTAKE"]
LEAN = RAISE["LEAN"]
bindings = RAISE["bindings"]


def execute(raw, expected, status, *, seed=None, preamble=False, supplied_instance=None):
    builtins = {} if preamble else (seed or {})
    initial = seed if preamble else {}
    namespace = dict(initial or {}, __builtins__=builtins)
    try:
        exec(compile(raw, "<named exception raise>", "exec", dont_inherit=True, optimize=0), namespace)
    except Exception as error:
        assert status is not None
        kind, value = status
        if kind == "name":
            assert type(error) is NameError and error.name == value
        elif kind == "invalid":
            assert type(error) is TypeError and error.args == ("exceptions must derive from BaseException",)
        elif kind == "notCallable":
            assert type(error) is TypeError and error.args == (f"'{value}' object is not callable",)
        else:
            assert kind == "instance" and type(error) is type(value) and error.args == value.args
            if supplied_instance is not None:
                assert error is supplied_instance
    else:
        assert status is None
    assert namespace.pop("__builtins__") is builtins
    wanted = dict(initial or {}) | expected
    assert namespace.keys() == wanted.keys()
    assert all(type(actual) is type(wanted[key]) and actual == wanted[key] for key, actual in namespace.items())


def completions(status):
    if status is None:
        return ".normal", ".ok ()"
    kind, value = status
    if kind == "name":
        error = f".nameError {json.dumps(value)}"
    elif kind == "invalid":
        error = ".invalidRaiseOperand"
    elif kind == "notCallable":
        error = ".notCallable"
    else:
        assert kind == "instance"
        error = f".raisedInstance ({RAISE['instance_code'](value)})"
    return f".raised ({error})", f".error (.raised (.runtime ({error})))"


def guards(expected, status, seed):
    ordinary, seeded = completions(status)
    initial, residual, preamble = bindings(seed), bindings(expected), bindings(seed | expected)
    return f"""#guard ordinaryRaise pythonSource {initial} {preamble} ({ordinary})
#guard seededRaise pythonSource ⟨[], {initial}⟩ {residual} ({seeded}) []
#guard seededRaise pythonSource ⟨{initial}, []⟩ {preamble} ({seeded}) []"""


def check(source, expected, status=None, *, seed=None, supplied_instance=None):
    seed = seed or {}
    for preamble in (False, True):
        execute(source.encode(), expected, status, seed=seed, preamble=preamble, supplied_instance=supplied_instance)
    return source, guards(expected, status, seed)


def controls(upstream):
    for suffix in ("", "()"):
        yield check(f"""
saved = C
C = None
try:
    reached = 7
    raise saved{suffix}
    skipped = 8
finally:
    cleaned = reached
tail = 9
""", {"saved": TypeError, "C": None, "reached": 7, "cleaned": 7}, ("instance", TypeError()),
            seed={"C": TypeError})

        yield check(f"""
try:
    reached = True
    raise Missing{suffix}
finally:
    cleaned = reached
""", {"reached": True, "cleaned": True}, ("name", "Missing"))

        status = ("notCallable", "NoneType") if suffix else ("invalid", None)
        yield check(f"""
C = None
try:
    reached = True
    raise C{suffix}
finally:
    cleaned = reached
""", {"C": None, "reached": True, "cleaned": True}, status, seed={"C": NameError})

    value = Exception("é😀\ud800")
    yield check("""
saved = injected
injected = None
try:
    reached = 7
    raise saved
finally:
    cleaned = reached
""", {"saved": value, "injected": None, "reached": 7, "cleaned": 7}, ("instance", value),
        seed={"injected": value}, supplied_instance=value)

    yield check("""
try:
    reached = 7
    raise injected()
finally:
    cleaned = reached
""", {"reached": 7, "cleaned": 7}, ("notCallable", "Exception"), seed={"injected": value})

    yield check("""
try:
    reached = 7
    raise C
except TypeError:
    wrong = 1
except Exception:
    caught = reached
else:
    wrong = 2
finally:
    cleaned = caught
tail = 9
""", {"reached": 7, "caught": 7, "cleaned": 7, "tail": 9},
        seed={"C": NameError, "Exception": Exception, "TypeError": TypeError})

    yield check("""
try:
    reached = True
    raise C()
finally:
    cleaned = reached
    replaced = cleanup_missing
""", {"reached": True, "cleaned": True}, ("name", "cleanup_missing"), seed={"C": RuntimeError})

    source = """___assertTrue(True)
try:
    reached = 7
    raise C
finally:
    cleaned = reached
"""
    expected = {"reached": 7, "cleaned": 7}
    truth = SUITE["pinned_truth_helper"](upstream)
    execute(source.encode(), expected, ("instance", NameError()), seed={"___assertTrue": truth, "C": NameError})
    yield source, f"""#guard seededRaise pythonSource ⟨[], [("___assertTrue", .helper .assertTrue), ("C", .exceptionClass .nameError)]⟩
  {bindings(expected)} (.error (.raised (.runtime (.raisedInstance (.empty .nameError))))) [("___assertTrue", .ok .none)]"""


def unchanged(upstream):
    path = "tests/python/programs/original/k-python/programs/testassert1.py"
    source = SUITE["pinned_source"](upstream, path, "87d8d9b8f19dab2341aaff9b0d2f63310cd07d41943dc89698269305d2240ce6")
    raw = (upstream / path).read_bytes()
    assert source.encode() == raw
    execute(raw, {}, ("name", "AssertionError"))
    for preamble in (False, True):
        execute(raw, {"x": 5}, None, seed={"AssertionError": AssertionError}, preamble=preamble)
    return source, """#guard ordinaryRaise pythonSource [] [] (.raised (.nameError "AssertionError"))
#guard seededRaise pythonSource .empty [] (.error (.raised (.runtime (.nameError "AssertionError")))) []
#guard seededRaise pythonSource (initial "legacy_builtin") [("x", .int 5)] (.ok ()) []
#guard let space := initial "legacy_preamble"; seededRaise pythonSource space
  (("x", .int 5) :: space.moduleGlobals) (.ok ()) []
#guard ordinaryRaise pythonSource [("AssertionError", .exceptionClass .assertionError)]
  [("AssertionError", .exceptionClass .assertionError), ("x", .int 5)] .normal"""


def module_controls(upstream):
    yield check("""
saved = C
C = None
reached = 7
raise saved
skipped = missing
""", {"saved": TypeError, "C": None, "reached": 7}, ("instance", TypeError()), seed={"C": TypeError})

    yield check("""
C = None
reached = 7
raise C
skipped = missing
""", {"C": None, "reached": 7}, ("invalid", None), seed={"C": TypeError})

    value = Exception("é😀\ud800")
    yield check("""
saved = supplied
supplied = None
raise saved
skipped = missing
""", {"saved": value, "supplied": None}, ("instance", value),
        seed={"supplied": value}, supplied_instance=value)

    source = """___assertTrue(True)
reached = 7
raise C
skipped = missing
"""
    truth = SUITE["pinned_truth_helper"](upstream)
    calls = []

    def traced(value):
        result = truth(value)
        calls.append((type(value), value, result))
        return result

    expected = {"reached": 7}
    execute(source.encode(), expected, ("instance", TypeError()), seed={"___assertTrue": traced, "C": TypeError})
    assert calls == [(bool, True, None)]
    yield source, f"""#guard seededRaise pythonSource ⟨[], [("___assertTrue", .helper .assertTrue), ("C", .exceptionClass .typeError)]⟩
  {bindings(expected)} (.error (.raised (.runtime (.raisedInstance (.empty .typeError))))) [("___assertTrue", .ok .none)]"""


def unchanged_module_raise(upstream):
    path = "tests/python/programs/original/lambda-py/modules/support_exception.py"
    source = SUITE["pinned_source"](upstream, path, "707e76ee92054f0dc049fa3661bfb6340b02c6f4cf4911a21fc88b440e058e9a")
    raw = (upstream / path).read_bytes()
    assert source.encode() == raw
    expected = {"s": 1}
    execute(raw, expected, ("name", "TypeError"))
    for preamble in (False, True):
        execute(raw, expected, ("instance", TypeError()), seed={"TypeError": TypeError}, preamble=preamble)
    ordinary, seeded = completions(("name", "TypeError"))
    entries = bindings(expected)
    fixed = [f"#guard ordinaryRaise pythonSource [] {entries} ({ordinary})"]
    for profile in (".empty", 'initial "legacy_builtin"', 'initial "legacy_preamble"'):
        fixed.append(f"#guard let space : Namespace := {profile}; seededRaise pythonSource space "
                     f"({entries} ++ space.moduleGlobals) ({seeded}) []")
    return source, "\n".join([*fixed, guards(expected, ("instance", TypeError()), {"TypeError": TypeError})])


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5)
    revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"]
    reached = [*controls(args.upstream), *module_controls(args.upstream)]
    pins = [unchanged(args.upstream), unchanged_module_raise(args.upstream)]
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "Fixture.py"
        INTAKE["check_lean_batch"](source, source.with_suffix(".lean"), pins + reached, LEAN,
                                   extra_imports=SUITE["IMPORTS"])
    print(json.dumps({"cpython": "3.13.5", "unchanged_pins": len(pins), "reached_controls": len(reached)}))

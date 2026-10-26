#!/usr/bin/env python3
"""Tests for lps_probes.py: parsers, static guards, the JSON <-> Lean <-> bytes links,
mutation detection, and (where the host allows) live runs of the tiny probes.

Live tests run probes only through lps_probes.py backends, in fresh temporary
directories; they are skipped where the toolchain or tracer is missing."""
from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import lps_probes as probes

ROOT = probes.ROOT
HAVE_BINUTILS = shutil.which("as") is not None and shutil.which("ld") is not None


def native_available() -> bool:
    return HAVE_BINUTILS and probes.NativeBackend().available()[0]


class FixtureRoot:
    """A copy of the probe sources, fixtures, generated Lean data and proof modules."""

    def __init__(self):
        self.directory = tempfile.TemporaryDirectory(prefix="lps-probes-test-")
        self.root = Path(self.directory.name)
        shutil.copytree(ROOT / probes.PROBES, self.root / probes.PROBES)
        shutil.copytree(ROOT / probes.LEAN_PROBES, self.root / probes.LEAN_PROBES)
        problems = Path("Silmaril/Process/LPS/Problems/CoreutilsLite")
        shutil.copytree(ROOT / problems, self.root / problems)

    def json(self, name: str) -> dict:
        return json.loads((self.root / probes.PROBES / "probes" / f"{name}.json").read_text())

    def write_json(self, name: str, data: dict) -> None:
        (self.root / probes.PROBES / "probes" / f"{name}.json").write_text(probes.encoded(data))

    def cleanup(self):
        self.directory.cleanup()


STRACE_SAMPLE = """\
4242  [  59] execve("./probe", ["./probe"], 0x7ffd /* 0 vars */) = 0
4242  [   1] write(0x1, 0x40009a, 0x6) = 6
4242  [  60] exit(0) = ?
4242  +++ exited with 0 +++
"""


class ParserTests(unittest.TestCase):
    def test_strace_raw_calls_after_execve(self):
        calls = probes.parse_strace(STRACE_SAMPLE)
        self.assertEqual([(c["nr"], c["args"], c["ret"]) for c in calls],
                         [(1, [1, 0x40009a, 6], 6), (60, [0], None)])

    def test_strace_errno_return(self):
        text = STRACE_SAMPLE.replace("= 6", "= -1 EBADF (Bad file descriptor)")
        self.assertEqual(probes.parse_strace(text)[0]["ret"], -9)

    def test_strace_injected_denial_fails_loudly(self):
        text = STRACE_SAMPLE.replace("= 6", "= -1 EPERM (Operation not permitted) (INJECTED)")
        with self.assertRaisesRegex(probes.ProbeError, "outside the allowlist"):
            probes.parse_strace(text)

    def test_strace_second_tracee_rejected(self):
        text = STRACE_SAMPLE.replace("4242  [  60]", "4243  [  60]")
        with self.assertRaisesRegex(probes.ProbeError, "more than one tracee"):
            probes.parse_strace(text)

    def test_strace_requires_execve(self):
        with self.assertRaisesRegex(probes.ProbeError, "execve"):
            probes.parse_strace("4242  [   1] write(0x1, 0x0, 0x0) = 0\n")

    def test_qemu_log(self):
        calls = probes.parse_qemu("4242 write(1,0x40009a,6) = 6\n4242 exit(0)\n")
        self.assertEqual([(c["nr"], c["args"], c["ret"]) for c in calls],
                         [(1, [1, 0x40009a, 6], 6), (60, [0], None)])

    def test_raw_arguments_are_unsigned(self):
        # qemu-user prints exit(-6); strace prints the same register unsigned.
        self.assertEqual(probes.parse_args("-6"), [2 ** 64 - 6])
        self.assertEqual(probes.parse_args("0xfffffffffffffffa"), [2 ** 64 - 6])

    def test_qemu_unknown_name(self):
        with self.assertRaises(probes.ProbeError):
            probes.parse_qemu("4242 frobnicate(1) = 0\n")

    def test_qemu_symbolic_arguments_compare_number_and_return_only(self):
        calls = probes.parse_qemu('4242 openat(-100,"in.txt",O_RDONLY) = 3\n4242 exit(0)\n')
        self.assertEqual(calls[0]["unreported"], ["args"])
        expected = {"syscalls": [{"nr": 257, "name": "openat", "args": [4294967196, 4194517, 0, 0], "ret": 3},
                                 {"nr": 60, "name": "exit", "args": [0], "ret": None}],
                    "stdoutHex": "", "stderrHex": "", "outcome": {"exit": 0}}
        observed = dict(expected, syscalls=calls)
        self.assertEqual(probes.disagreements(expected, observed, "q"), [])
        observed["syscalls"][0]["ret"] = 4
        self.assertTrue(probes.disagreements(expected, observed, "q"))


    def test_qemu_unimplemented_number(self):
        calls = probes.parse_qemu("4242 Unknown syscall 999\n4242 exit(-38)\n")
        self.assertEqual(calls[0]["nr"], 999)
        self.assertEqual(calls[0]["unreported"], ["args", "ret"])
        self.assertEqual(calls[1]["args"], [(1 << 64) - 38])
        with self.assertRaises(probes.ProbeError):
            probes.parse_qemu("4242 Unknown syscall 77\n")

class StackArgumentTests(unittest.TestCase):
    def observed(self, first, second):
        return {"syscalls": [{"nr": 0, "name": "read", "args": [3, first, 64], "ret": 3},
                             {"nr": 1, "name": "write", "args": [1, second, 3], "ret": 3}],
                "stdoutHex": "68690a", "stderrHex": "", "outcome": {"exit": 0}}

    def test_entry_stack_pointer_becomes_sp(self):
        observed = self.observed(0x7ffd1000, 0x7ffd1000)
        probes.normalize_stack({"stackArgs": [[0, 1], [1, 1]]}, observed)
        self.assertEqual([call["args"][1] for call in observed["syscalls"]], ["sp", "sp"])

    def test_different_stack_arguments_are_rejected(self):
        with self.assertRaisesRegex(probes.ProbeError, "differ"):
            probes.normalize_stack({"stackArgs": [[0, 1], [1, 1]]}, self.observed(0x7ffd1000, 0x7ffd2000))

    def test_stack_positions_must_exist(self):
        with self.assertRaises(probes.ProbeError):
            probes.normalize_stack({"stackArgs": [[5, 1]]}, self.observed(1, 1))

    def test_generated_lean_records_stack_positions(self):
        data = (ROOT / probes.LEAN_DATA / "OpenRead.lean").read_text()
        self.assertIn("stackArgs := [(1, 1), (2, 1)]", data)


class FinalFilesTests(unittest.TestCase):
    def test_final_files_skip_the_probe_and_sort(self):
        with tempfile.TemporaryDirectory(prefix="lps-probe-test-files-") as directory:
            work = Path(directory)
            (work / "probe").write_bytes(b"\x7fELF")
            (work / "out.txt").write_bytes(b"ok")
            (work / "in.txt").write_bytes(b"hi\n")
            (work / "out.txt").chmod(0)
            self.assertEqual(probes.final_files(work), {"in.txt": "68690a", "out.txt": "6f6b"})
            self.assertEqual(list(probes.final_files(work)), ["in.txt", "out.txt"])

    def test_directories_left_behind_fail_loudly(self):
        with tempfile.TemporaryDirectory(prefix="lps-probe-test-files-") as directory:
            (Path(directory) / "made").mkdir()
            with self.assertRaisesRegex(probes.ProbeError, "non-regular"):
                probes.final_files(Path(directory))

    def test_file_disagreement_is_reported(self):
        reference = {"syscalls": None, "stdoutHex": "", "stderrHex": "", "outcome": {"exit": 2},
                     "files": {"out.txt": "6f6b"}}
        other = dict(reference, files={"out.txt": "6b6f"})
        self.assertTrue(probes.disagreements(reference, other, "f"))

    def test_mutant_differing_only_in_files_is_accepted(self):
        mutant = probes.load_declaration(ROOT, "open_create_ko")
        self.assertEqual(probes.mutant_problems(ROOT, mutant), [])
        same = json.loads(json.dumps(mutant))
        same["expected"]["files"] = probes.load_declaration(ROOT, "open_create")["expected"]["files"]
        self.assertTrue(probes.mutant_problems(ROOT, same))

    def test_generated_lean_has_input_and_final_files(self):
        data = (ROOT / probes.LEAN_DATA / "OpenCreate.lean").read_text()
        self.assertIn("files := [([0x6f, 0x75, 0x74, 0x2e, 0x74, 0x78, 0x74],", data)
        read = (ROOT / probes.LEAN_DATA / "OpenRead.lean").read_text()
        self.assertIn("input := harnessInputFiles inputFiles", read)

    def test_backend_skips_need_a_reason_and_a_remaining_backend(self):
        native = FakeBackend("native", {})
        qemu = FakeBackend("qemu-user", {})
        chosen = probes.usable_backends({"skipBackends": {"qemu-user": "descriptor 3"}}, [native, qemu])
        self.assertEqual([backend.name for backend in chosen], ["native"])
        with self.assertRaises(probes.ProbeError):
            probes.usable_backends({"skipBackends": {"qemu-user": ""}}, [native, qemu])
        with self.assertRaises(probes.ProbeError):
            probes.usable_backends({"skipBackends": {"native": "x", "qemu-user": "y"}}, [native, qemu])


class StaticGuardTests(unittest.TestCase):
    def declaration(self, **extra):
        base = {"probe": "p", "allow": ["exit"], "inputs": {"files": {}, "stdinHex": ""}}
        base.update(extra)
        return base

    def test_accepts_plain_probe(self):
        probes.static_check(self.declaration(), '.ascii "hello\\n"')

    def test_rejects_escaping_input_paths(self):
        for path in ("../x", "/etc/passwd", "a/b", ".."):
            with self.subTest(path=path), self.assertRaises(probes.ProbeError):
                probes.static_check(self.declaration(inputs={"files": {path: ""}}), "")

    def test_rejects_absolute_string_literal(self):
        with self.assertRaises(probes.ProbeError):
            probes.static_check(self.declaration(), '.asciz "/etc/passwd"')

    def test_rejects_forbidden_and_unknown_calls(self):
        for call in ("execve", "fork", "kill", "no_such_call"):
            with self.subTest(call=call), self.assertRaises(probes.ProbeError):
                probes.static_check(self.declaration(allow=["exit", call]), "")

    def test_requires_allowlist(self):
        with self.assertRaises(probes.ProbeError):
            probes.static_check(self.declaration(allow=[]), "")

    def test_inject_set_denies_everything_else(self):
        self.assertEqual(probes.inject_set({"allow": ["write", "exit"]}), "!execve,write,exit")

    def test_native_limits_forbid_processes(self):
        chosen = dict(probes.limits(64 << 20))
        self.assertEqual(chosen[probes.resource.RLIMIT_NPROC], 0)
        self.assertEqual(chosen[probes.resource.RLIMIT_CORE], 0)


class OutputConsistencyTests(unittest.TestCase):
    def observed(self, calls, out="", err=""):
        return {"syscalls": calls, "stdoutHex": out, "stderrHex": err, "outcome": {"exit": 0}}

    def test_write_returns_match_capture(self):
        probes.consistent_output(self.observed(
            [{"nr": 1, "name": "write", "args": [1, 0, 2], "ret": 2}], out="6869"))

    def test_write_returns_mismatch(self):
        with self.assertRaises(probes.ProbeError):
            probes.consistent_output(self.observed(
                [{"nr": 1, "name": "write", "args": [1, 0, 2], "ret": 2}], out="68"))

    def test_read_after_write_rejected(self):
        calls = [{"nr": 1, "name": "write", "args": [1, 0, 1], "ret": 1},
                 {"nr": 0, "name": "read", "args": [0, 0, 1], "ret": 1}]
        with self.assertRaisesRegex(probes.ProbeError, "interleave"):
            probes.consistent_output(self.observed(calls, out="61"))

    def test_stdin_consumed_is_the_returned_prefix(self):
        declaration = {"inputs": {"stdinHex": "70696e670a"}}
        calls = [{"nr": 0, "name": "read", "args": [0, 0, 2], "ret": 2},
                 {"nr": 0, "name": "read", "args": [99, 0, 2], "ret": -9}]
        self.assertEqual(probes.stdin_consumed(declaration, calls), b"pi")
        with self.assertRaises(probes.ProbeError):
            probes.stdin_consumed({"inputs": {"stdinHex": "70"}}, calls)

    def test_interleaved_streams_rejected(self):
        calls = [{"nr": 1, "name": "write", "args": [2, 0, 1], "ret": 1},
                 {"nr": 1, "name": "write", "args": [1, 0, 1], "ret": 1}]
        with self.assertRaisesRegex(probes.ProbeError, "interleave"):
            probes.consistent_output(self.observed(calls, out="61", err="62"))


class FakeBackend(probes.Backend):
    def __init__(self, name, result):
        self.name, self.result = name, result

    def run(self, declaration, elf):
        return json.loads(json.dumps(self.result))


class AgreementTests(unittest.TestCase):
    def test_backend_disagreement_reported(self):
        reference = {"syscalls": [{"nr": 60, "name": "exit", "args": [42], "ret": None}],
                     "stdoutHex": "", "stderrHex": "", "outcome": {"exit": 42}}
        other = json.loads(json.dumps(reference))
        other["outcome"] = {"exit": 43}
        results = probes.run_everywhere({}, b"", [FakeBackend("a", reference), FakeBackend("b", other)])
        problems = probes.cross_check(results, reference, "p")
        self.assertEqual(len(problems), 1)
        self.assertIn("p/b", problems[0])

    def test_untraced_backend_compares_outcome_only(self):
        reference = {"syscalls": [{"nr": 60, "name": "exit", "args": [42], "ret": None}],
                     "stdoutHex": "", "stderrHex": "", "outcome": {"exit": 42}}
        untraced = dict(reference, syscalls=None)
        self.assertEqual(probes.disagreements(reference, untraced, "x"), [])

    def test_untraced_status_above_128_is_exit_or_signal(self):
        reference = {"syscalls": [], "stdoutHex": "", "stderrHex": "", "outcome": {"exit": 218}}
        for outcome, agrees in (({"exit": 218}, True), ({"signal": 90}, True), ({"exit": 217}, False)):
            expected = dict(reference, outcome=outcome)
            observed = dict(reference, syscalls=None, outcome={"exitOrSignal": 218})
            self.assertEqual(probes.disagreements(expected, observed, "x") == [], agrees)

    def test_host_dependent_fields_are_present_but_not_compared(self):
        marks = [{"call": 0, "ret": True, "why": "pid"}, {"call": 1, "arg": 0, "why": "stack"}]
        reference = {"syscalls": [{"nr": 39, "name": "getpid", "args": [], "ret": 100},
                                  {"nr": 318, "name": "getrandom", "args": [0x7ff0, 8, 0], "ret": 8}],
                     "stdoutHex": "", "stderrHex": "", "outcome": {"exit": 0}}
        other = json.loads(json.dumps(reference))
        other["syscalls"][0]["ret"] = 200
        other["syscalls"][1]["args"][0] = 0x7fe0
        self.assertEqual(probes.disagreements(reference, other, "x", marks), [])
        self.assertNotEqual(probes.disagreements(reference, other, "x"), [])
        other["syscalls"][1]["args"][1] = 9
        self.assertNotEqual(probes.disagreements(reference, other, "x", marks), [])

    def test_bad_host_dependent_entry_rejected(self):
        with self.assertRaises(probes.ProbeError):
            probes.host_dependent({"hostDependent": [{"call": 0, "why": "names neither ret nor arg"}]})


class LeanGenerationTests(unittest.TestCase):
    def test_declared_names_follow_namespaces(self):
        text = "namespace A\nnamespace B\ntheorem t : True := trivial\nend B\ninstance i : X := x\nend A\n"
        self.assertEqual(probes.declared_names(text), {"A.B.t", "A.i"})

    def test_empty_output_is_an_empty_list(self):
        self.assertEqual(probes.lean_bytes(b""), "[]")

    def test_stdin_probe_generates_input_and_reads(self):
        data = (ROOT / probes.LEAN_DATA / "ReadEcho.lean").read_text()
        declaration = probes.load_declaration(ROOT, "read_echo")
        stdin = probes.lean_bytes(bytes.fromhex(declaration["inputs"]["stdinHex"]))
        self.assertIn(f"def stdin : List Byte := {stdin}", data)
        self.assertIn("input := harnessInputWith stdin", data)
        self.assertIn(f"stdin := {stdin}", data)

    def test_image_kind(self):
        self.assertEqual(probes.image_kind({}), "rx")
        self.assertEqual(probes.image_kind({"image": "rwx"}), "rwx")
        with self.assertRaises(probes.ProbeError):
            probes.image_kind({"probe": "p", "image": "w"})

    def test_generated_constants_come_from_json(self):
        data = (ROOT / probes.LEAN_DATA / "WriteHello.lean").read_text()
        declaration = probes.load_declaration(ROOT, "write_hello")
        self.assertIn("outcome := .exited 0", data)
        self.assertIn(probes.lean_bytes(bytes.fromhex(declaration["expected"]["stdoutHex"])), data)
        self.assertIn(f"`{declaration['sha256']}`", data)


class LinkTests(unittest.TestCase):
    """Offline check of every link, and mutations that each link must catch."""

    def setUp(self):
        self.fixture = FixtureRoot()
        self.root = self.fixture.root

    def tearDown(self):
        self.fixture.cleanup()

    def check(self, names=None):
        if not HAVE_BINUTILS:
            self.skipTest("GNU as/ld are needed to rebuild the probes")
        return probes.check(self.root, names or probes.probe_names(self.root), None, live=False)

    def test_repository_links_agree(self):
        self.assertEqual(self.check(), [])

    def test_changed_expected_exit_is_caught(self):
        data = self.fixture.json("exit42")
        data["expected"]["outcome"] = {"exit": 41}
        self.fixture.write_json("exit42", data)
        problems = self.check(["exit42"])
        self.assertTrue(any("stale" in problem for problem in problems), problems)

    def test_edited_lean_constant_is_caught(self):
        path = self.root / probes.LEAN_DATA / "Exit42.lean"
        path.write_text(path.read_text().replace(".exited 42", ".exited 41"))
        problems = self.check(["exit42"])
        self.assertTrue(any("stale" in problem for problem in problems), problems)

    def test_changed_source_is_caught(self):
        source = self.root / probes.PROBES / "probes" / "exit42.s"
        source.write_text(source.read_text().replace("$42", "$41"))
        problems = self.check(["exit42"])
        self.assertTrue(any("sha256" in problem for problem in problems), problems)

    def test_changed_pin_is_caught(self):
        pins = probes.read_pins(self.root)
        pins["exit42"] = "0" * 64
        probes.write_pins(self.root, pins)
        problems = self.check(["exit42"])
        self.assertTrue(any(probes.SHA_FILE in problem for problem in problems), problems)

    def test_missing_theorem_is_caught(self):
        data = self.fixture.json("exit42")
        data["lean"]["theorems"].append("Silmaril.Process.LPS.Probes.Exit42.no_such_theorem")
        self.fixture.write_json("exit42", data)
        problems = self.check(["exit42"])
        self.assertTrue(any("no_such_theorem" in problem for problem in problems), problems)

    def test_proof_module_must_use_generated_data(self):
        path = self.root / probes.LEAN_PROBES / "Exit42.lean"
        path.write_text(path.read_text().replace("open Data.Exit42", "open Elsewhere")
                        .replace("Data.Exit42.", "Elsewhere."))
        problems = self.check(["exit42"])
        self.assertTrue(any("never refers" in problem for problem in problems), problems)

    def test_sorry_in_proof_module_is_caught(self):
        path = self.root / probes.LEAN_PROBES / "WriteHello.lean"
        path.write_text(path.read_text() + "\n-- sorry\n")
        problems = self.check(["write_hello"])
        self.assertTrue(any("sorry" in problem for problem in problems), problems)

    def test_changed_image_kind_is_caught(self):
        data = self.fixture.json("read_echo")
        data["image"] = "rx"
        self.fixture.write_json("read_echo", data)
        self.assertTrue(any("read_echo" in problem for problem in self.check(["read_echo"])))

    def test_mutant_with_identical_behaviour_is_caught(self):
        original = self.fixture.json("exit42")
        mutant = self.fixture.json("exit43")
        mutant["expected"] = original["expected"]
        self.assertTrue(probes.mutant_problems(self.root, mutant))


@unittest.skipUnless(native_available(), "native strace backend unavailable")
class LiveTests(unittest.TestCase):
    def run_probe(self, name, declaration=None):
        with tempfile.TemporaryDirectory(prefix="lps-probe-test-build-") as scratch:
            elf = probes.built(ROOT, name, Path(scratch))
        return probes.NativeBackend().run(declaration or probes.load_declaration(ROOT, name), elf)

    def test_exit42_matches_fixture(self):
        observed = self.run_probe("exit42")
        self.assertEqual(probes.disagreements(probes.load_declaration(ROOT, "exit42")["expected"],
                                              observed, "exit42"), [])

    def test_file_probes_match_fixtures(self):
        for name in ("open_read", "open_create", "open_missing", "open_legacy"):
            with self.subTest(probe=name):
                declaration = probes.load_declaration(ROOT, name)
                observed = self.run_probe(name)
                probes.normalize_stack(declaration, observed)
                self.assertEqual(probes.disagreements(declaration["expected"], observed, name), [])

    def test_created_file_is_observed(self):
        self.assertEqual(self.run_probe("open_create")["files"], {"out.txt": "6f6b"})
        self.assertEqual(self.run_probe("open_create_ko")["files"], {"out.txt": "6b6f"})

    def test_mutants_really_differ(self):
        for mutant, original in (("exit43", "exit42"), ("write_hello5", "write_hello")):
            with self.subTest(mutant=mutant):
                self.assertNotEqual(self.run_probe(mutant)["outcome"] if mutant == "exit43"
                                    else self.run_probe(mutant)["stdoutHex"],
                                    probes.load_declaration(ROOT, original)["expected"]
                                    ["outcome" if mutant == "exit43" else "stdoutHex"])
        keys = ("outcome", "stdoutHex", "stderrHex")
        for name in probes.probe_names(ROOT):
            original = probes.load_declaration(ROOT, name).get("mutantOf")
            if original is None:
                continue
            with self.subTest(mutant=name):
                observed = self.run_probe(name)
                expected = probes.load_declaration(ROOT, original)["expected"]
                self.assertNotEqual([observed[key] for key in keys] + [probes.files_of(observed)],
                                    [expected[key] for key in keys] + [probes.files_of(expected)])

    def test_errno_and_echo_fixtures_match(self):
        for name in ("write_efault", "write_closed", "close_twice", "write_zero", "read_badfd", "read_echo"):
            with self.subTest(probe=name):
                observed = self.run_probe(name)
                self.assertEqual(probes.disagreements(probes.load_declaration(ROOT, name)["expected"],
                                                      observed, name), [])

    def test_undeclared_syscall_is_denied_and_fails_loudly(self):
        declaration = probes.load_declaration(ROOT, "write_hello")
        declaration["allow"] = ["exit"]
        with self.assertRaisesRegex(probes.ProbeError, "outside the allowlist"):
            self.run_probe("write_hello", declaration)

    def test_run_leaves_no_files_behind(self):
        before = set(Path(tempfile.gettempdir()).glob("lps-probe-*"))
        self.run_probe("exit42")
        after = set(Path(tempfile.gettempdir()).glob("lps-probe-*"))
        self.assertEqual(after - before, set())


class CommandTests(unittest.TestCase):
    def test_backends_command_lists_every_backend(self):
        output = io.StringIO()
        with redirect_stdout(output), redirect_stderr(io.StringIO()):
            self.assertEqual(probes.main(["backends"]), 0)
        for name in ("container", "bwrap", "native", "qemu-user", "qemu-system"):
            self.assertIn(name, output.getvalue())


if __name__ == "__main__":
    unittest.main()

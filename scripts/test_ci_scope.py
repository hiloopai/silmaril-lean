import importlib.util
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location("ci_scope", Path(__file__).with_name("ci-scope.py"))
ci_scope = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci_scope)

EXES = ["wasm-as", "wasm-dis", "wasm-opt", "wasm-merge", "wasm-shell", "wasm-ctor-eval",
        "wasm-metadce", "wasm-shell-lean"]


class ScopeTests(unittest.TestCase):
    def test_build_configuration_checks_everything(self):
        for path in ["lakefile.toml", "lean-toolchain", "Makefile", ".github/workflows/ci.yml"]:
            self.assertEqual(ci_scope.select({path}), ["Silmaril", "ProjectSelfTest", *EXES])

    def test_a_module_brings_its_importers(self):
        self.assertEqual(ci_scope.select({"Silmaril/Prelude/Defs.lean"}), ["+Silmaril"])

    def test_a_deleted_module_still_selects_its_importers(self):
        self.assertIn("+Silmaril", ci_scope.select({"Silmaril/Deleted/Module.lean"} |
                                                   {"Silmaril/Prelude/Defs.lean"}))
        self.assertEqual(ci_scope.select({"Silmaril/Deleted/Module.lean"}), [])

    def test_an_included_file_selects_its_reader(self):
        self.assertEqual(ci_scope.select({"data/riscv/testfloat-riscv.txt"}),
                         ["+Silmaril.Process.RiscV.Thms"])

    def test_a_needs_input_selects_its_library(self):
        self.assertEqual(ci_scope.select({"examples/project/data/x"}), ["+ProjectSelfTest"])

    def test_release_inputs_add_the_executables(self):
        self.assertEqual(ci_scope.select({"tools/binaryen-lean/check-release.py"}), EXES)
        proof = ci_scope.select({"Silmaril/Wasm/Binaryen/Toolkit/ShellSound.lean"})
        self.assertEqual(proof[-len(EXES):], EXES)

    def test_files_lake_never_reads_select_nothing(self):
        self.assertEqual(ci_scope.select({"docs/ci.md", "scripts/check-layout.sh"}), [])


if __name__ == "__main__":
    unittest.main()

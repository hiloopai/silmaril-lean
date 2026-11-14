module

public import Silmaril.Project.Defs
public import Silmaril.Project.Formats.Defs
public import Silmaril.Project.Shapes.Format.Defs
public import Silmaril.Project.Shapes.Elf.Thms
public import ProjectSelfTest.Machines
-- The Wasm components records (silmaril/wasm-components/*.toml) are part of this project; their
-- modules declare the registry's artifacts first, so this module only adds the rest.
public import Silmaril.Project.WasmComponents.Thms
public import Silmaril.Project.WasmComponents.Relations.Thms
public import Silmaril.Project.WasmComponents.Toy.Thms
public import Silmaril.Project.WasmComponents.Versions.Thms
public import Silmaril.Project.WasmComponents.Wac.Thms
public import Silmaril.Project.WasmComponents.Wac.Verdicts.Thms

/-!
# The `sil project` self-test

One construct per layer, checked end to end by `examples/project/selftest.sh` (`sil project
dump`, `check`, `sqlite`, `explore`):

* records and the DAG: a closed problem with a solution, a conjecture, groups and the root;
* problems over arguments: a predicate with SAT and CSA answers and a refuted instance, and a
  problem in the attribute form with fields and a proved instance from TOML;
* markings: the refuted predicate is deprecated (`silmaril deprecation`) in favour of a
  corrected one, and its refutation is a `spec_bug` (`[[finding]]` in TOML);
* artifacts: the registry `silmaril/artifacts.toml`, with one derivation;
* values: a value with a problem about it, and values read with silmaril's format adapters
  (`wasm.binary.core`, `elf.exec-x86`);
* the TOML route: `silmaril/selftest.toml` (values, instances, rows of the standard shapes
  `value.satisfies` and `elf.entry.x86`, the groups and the root).
-/

namespace ProjectSelfTest

@[expose] public section

@[problem "silmaril.selftest.truth"] def truth : Prop := True
@[solves "silmaril.selftest.truth"] theorem truth_sol : truth := trivial

def Small (n : Nat) : Prop := n < 3

/-- What `silmaril.selftest.small` should have said: a small number is at most 2. -/
def SmallLe (n : Nat) : Prop := Small n → n ≤ 2

/-- The attribute form, with fields: a problem over one argument. -/
@[problem "silmaril.selftest.square" (title := "A perfect square")]
def square (n : Nat) : Prop := ∃ k, k * k = n

/-- The predicate of the standard-shape row (an `abbrev`, so that `silmaril_decide` finds its
`DecidablePred` instance through the shape's argument). -/
abbrev sixBytes (b : Silmaril.Formats.Bytes) : Prop := b.length = 6

end

silmaril problem silmaril.selftest.small := ProjectSelfTest.Small

@[answers "silmaril.selftest.small" sat] public theorem small_sat : ∃ n, Small n :=
  ⟨0, show 0 < 3 by decide⟩
@[answers "silmaril.selftest.small" csa] public theorem small_csa : ∃ n, ¬ Small n :=
  ⟨5, show ¬ 5 < 3 by decide⟩

silmaril instance silmaril.selftest.small.five := silmaril.selftest.small (n := 5)
@[answers "silmaril.selftest.small.five" uns] public theorem five_uns :
    ¬ silmaril.selftest.small.five := by
  show ¬ (5 : Nat) < 3; decide

-- A marking: `silmaril.selftest.small` (every `n` is small) is a wrong statement. It stays, with
-- its refutation, deprecated in favour of the corrected `silmaril.selftest.small_le`; its
-- refutation is classified as a spec bug in `silmaril/selftest.toml` (`[[finding]]`).
silmaril problem silmaril.selftest.small_le := ProjectSelfTest.SmallLe
@[answers "silmaril.selftest.small_le" thm] public theorem small_le_thm : ∀ n, SmallLe n :=
  fun n (h : n < 3) => by omega
silmaril deprecation silmaril.selftest.small (reason := "claims that every n is below 3")
  (superseded_by := [silmaril.selftest.small_le])

silmaril conjecture silmaril.selftest.open : ∀ n : Nat, n + 0 = n

-- The registry: the Wasm components modules imported above already declared its entries (each
-- artifact record must come from one module of the dump), so this adds only what they did not.
silmaril_artifacts_refresh "silmaril/artifacts.toml"
silmaril value silmaril.selftest.hello : bytes := "examples/project/data/hello.txt"
silmaril problem silmaril.selftest.hello.six about silmaril.selftest.hello : fun b => b.length = 6
  := by silmaril_decide

silmaril load "silmaril/selftest.toml"

@[answers "silmaril.selftest.square.n4" thm] public theorem square_n4 :
    silmaril.selftest.square.n4 := ⟨2, rfl⟩

@[answers "silmaril.selftest.hello.six_row" thm] public theorem hello_six_row :
    silmaril.selftest.hello.six_row := by
  silmaril_decide

@[solves "silmaril.selftest.module.parses"] public theorem module_parses :
    silmaril.selftest.module.parses := by
  silmaril_decide

@[solves "silmaril.selftest.exit.parses"] public theorem exit_parses :
    silmaril.selftest.exit.parses := by
  silmaril_decide

/-- A row of `elf.entry.x86`: the file as a `Blob` from its chunk literals, then one run of the
kernel-fast reader. -/
@[answers "silmaril.selftest.exit.entry" thm] public theorem exit_entry :
    silmaril.selftest.exit.entry :=
  Silmaril.Project.Shapes.Entry.x86_of_blob (Silmaril.Project.Shapes.blob_of_decode rfl rfl)
    (by decide +kernel)

/--
info: artifact_type blob (Silmaril.Project.Defs) {"decl":"Silmaril.Project.blob","doc":"Bytes, identified by a raw-codec BLAKE3 CIDv1 (bafkr4i…)"}
-/
#guard_msgs in
#silmaril artifact_type

end ProjectSelfTest

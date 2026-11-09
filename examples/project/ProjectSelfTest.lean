module

public import Silmaril.Project.Defs
public import Silmaril.Project.Formats.Defs
public import Silmaril.Project.Shapes.Format.Defs

/-!
# The `sil project` self-test

One construct per layer, checked end to end by `examples/project/selftest.sh` (`sil project
dump`, `check`, `sqlite`, `explore`):

* records and the DAG: a closed problem with a solution, a conjecture, groups and the root;
* problems over arguments: a predicate with SAT and CSA answers and a refuted instance, and a
  problem in the attribute form with fields and a proved instance from TOML;
* artifacts: the registry `silmaril/artifacts.toml`, with one derivation;
* values: a value with a problem about it, and values read with silmaril's format adapters
  (`wasm.binary.core`, `elf.exec-x86`);
* the TOML route: `silmaril/selftest.toml` (values, instances, a row of a standard shape, the
  groups and the root).
-/

namespace ProjectSelfTest

@[expose] public section

@[problem "silmaril.selftest.truth"] def truth : Prop := True
@[solves "silmaril.selftest.truth"] theorem truth_sol : truth := trivial

def Small (n : Nat) : Prop := n < 3

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

silmaril conjecture silmaril.selftest.open : ∀ n : Nat, n + 0 = n

silmaril artifacts "silmaril/artifacts.toml"
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

/--
info: artifact_type blob (Silmaril.Project.Defs) {"decl":"Silmaril.Project.blob","doc":"Bytes, identified by a raw-codec BLAKE3 CIDv1 (bafkr4i…)"}
-/
#guard_msgs in
#silmaril artifact_type

end ProjectSelfTest

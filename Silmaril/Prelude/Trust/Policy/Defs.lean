module

public import Silmaril.Prelude.Trust.Elab.Defs

/-! # The trust sets and the pinned scope policy

The sets that `policy.toml` names, and the policy itself. `default` is the small set of native
procedures the default profile runs. Add a procedure to it (or to a subset it includes) only
with a reason in its `native_decider` docstring, and say in the pull request what the native
run trusts.

The policy file is pinned by its FNV-1a hash. Lake does not track the file, so editing it
without updating the pin fails here on the next fresh build. `scripts/check-layout.sh` checks
the pin on every run.
-/

/-- Kernel bytes: comparisons and the raw-bytes bridge (`Silmaril.Prelude.Bytes.Native`). -/
trust_set bytes := {bytes.sameBytes, bytes.beq, bytes.wf, bytes.eqByteArray, bytes.cstring}

/-- ELF: the staged layout checker (`Silmaril.Elf`, registered there as `elf.layout`). Naming a
procedure here before it is registered is harmless: sets hold names. -/
trust_set elf := {elf.layout}

/-- What the default profile runs natively. -/
trust_set default := {} includes bytes elf

trust_policy "../../../../policy.toml" pin "0294950de3d882b2"

module

public import Silmaril.Machine.X86.Safe.Defs
public import Silmaril.Machine.X86.Sep.Spec.Thms
public import Silmaril.Proofs.Machine.X86.Safe.Basic

/-!
# Step-indexed safety and triples over any machine: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Machine.X86.Safe.Basic`, names in
`Silmaril.Machine.X86.Safe`), for every step function `step`:

* Refinement: `run_of_refines`, `reaches_of_refines`, `Refines.refl`, `Refines.trans`,
  `safeN_of_refines`, `STriple.of_refines` (**safety and triples transport along a
  refinement of machines**, e.g. from `Open.step` to `Open9.step`).
* `SafeN`: `safeN_succ`, `safeN_mono`, `safeN_le`, `safeN_post`, `run_succ_some`,
  `safeN_of_run`, `safeN_of_reaches`, `safeN_prefix`, `safeN_bind`.
* `STriple`: `zero`, `mono`, `le`, `frame`, `conseq`, `progress_seq`, `sexists_pre`,
  `spure_pre`.
* `Progress`: `frame`, `conseq`; `rsp_of_sep`.

And for every `step` with `[ExtendsOpen step]`, the bridges from the separation-logic layer's total triples
(`Sep.Triple`, over `Open.step`): `reaches_of_open`, `STriple.of_triple`,
`STriple.triple_seq`, `STriple.seq_triple`, `progress_of_rsp`.

Instances: `ExtendsOpen Open.step` (here), `ExtendsOpen Open9.step` (`Safe/Open9/Thms.lean`).
-/

@[expose] public section

namespace Silmaril.Machine.X86.Safe

/-- The open machine extends itself. -/
instance instExtendsOpenOpen : ExtendsOpen Silmaril.Machine.X86.Open.step := ⟨fun h => h⟩

end Silmaril.Machine.X86.Safe

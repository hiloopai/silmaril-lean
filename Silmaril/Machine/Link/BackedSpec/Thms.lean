module

public import Silmaril.Machine.Link.BackedSpec.Defs
public import Silmaril.Proofs.Machine.Link.BackedSpec.Rules

/-! # The backed-stack `FnSpec` template: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Machine.Link.BackedSpec.Rules`, namespace
`Silmaril.Proofs.Machine.Link.BackedSpec`):

* `safeB_of_safe`: **backward compatibility**: `Safe n a S ctx → SafeB n a S ctx`. Nothing
  about `FnSpec`, `SysVPre`/`SysVPost` or `Safe` changes; every existing contract transfers.
* `safeB_zero`, `safeB_mono`.
* `STriple.seq`: same-index sequencing of step-indexed triples.
* `scallB_rule`: the step-indexed call rule for a `SafeB` callee.
* Assertion laws: `blockB_blockAny`, `bytesPt_blockB`, `blockB_split`, `byteAny_byteRd`,
  `blockAny_blockRd`, `bytesAt_blockRd`, `wordPt_blockRd`, `blockRd_add`.

Total variants (`SafeT`, `SafeTB` in `Defs`): `safe_of_safeT`, `safeB_of_safeTB` (total implies
step-indexed at every index), `safeT_of_sat` (a position-independent total `FnSpec.Sat` of the
exact bytes, as the separation-logic layer's libmini `exports_sat`, gives `SafeT` in any image holding them),
`tcall_rule`, `tcallB_rule` (total call rules). These compose along acyclic call graphs by
hand; they are not a `Contract.Logic` (no index, so `link_compose`'s recursion argument does
not apply).

Not done: a `Contract.Logic` instance for `SafeB` (so that `link_compose` could carry
backed-stack exports); a postcondition that gives the budget back writable (see the module
documentation of `Silmaril.Machine.Link.BackedSpec.Defs`).
-/

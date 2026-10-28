# Direct LPS port: shape pins and remaining proof surfaces

**Update (lane #3462, branch `parity/lps-shapes`).** The items below that were listed as
remaining are now translated: the whole of `Shapes.v` (including `Shapes.v:161`, `:455` with
the upstream `image_wf` hypothesis, `:475`, `:491`) in `Shapes.lean`; the entry lemmas of
`Equivalence.v:558-655` and `:1138` in `Equivalence.lean`; all of `OmniRun.v` (`exec`,
`coexec`, `coexec_progress` and `cosafe` as Lean `coinductive` predicates, the prefix-safety
characterisation and every `bh_*_iff`) in `OmniRun.lean`; `EquivalenceDefinition/GatedSize.v`
in `GatedSize.lean`; the core of `MeasureLib.v` plus a countable-sum (`tsum`) reading of the
weight bounds in `MeasureLib.lean`; and positive/negative controls in `ShapesChecks.lean`.
`RunHelpers` and `ShapesParity` now only re-export the earlier names as aliases. The text below
is the audit as it stood before that lane.

This audit distinguishes source-pin agreement, proved Lean helpers, and the
larger semantic parity obligations. It does not certify Rocq-to-Lean semantic
equivalence or whole-corpus instruction/syscall coverage.

## The Shapes pin discrepancy is metadata, not a source delta

The direct port originally cited OSS Verify commit
`8f5f46768858af236a4270f9628e6beed9aa0e72`; the imported example set pins
`98e995d4daced70a0a4aa2c810854b88720735f1` in `import-lock.json`.
The exact public `theories/Shapes.v` blob at the historical pin was downloaded
and compared byte for byte with the imported file at the newer pin:

| Revision | Bytes | SHA-256 |
| --- | ---: | --- |
| `8f5f46768858af236a4270f9628e6beed9aa0e72` | 24,570 | `82b996cbc454c87866c42e4047864730f03f1a54add5d4ec60d15d852b137d7c` |
| `98e995d4daced70a0a4aa2c810854b88720735f1` | 24,570 | `82b996cbc454c87866c42e4047864730f03f1a54add5d4ec60d15d852b137d7c` |

The files are identical, including the omitted proof lemmas discussed below.
Basic, Shapes and the port documentation now cite the imported pin and retain
the historical pin explicitly. This comparison concerns **Shapes.v only**;
it does not assert that the two repositories' other files are identical.

Public source:
<https://raw.githubusercontent.com/theorem-labs/oss-verify-proofs/8f5f46768858af236a4270f9628e6beed9aa0e72/theories/Shapes.v>.
The imported counterpart is retained in this PR's optional source snapshot at
`examples/verification-projects/theorem-dev/lps-native-reference/oss-verify/theories/Shapes.v`.
The snapshot manifest records its source pin and hash; selected semantic sources
are alongside it under `lps/`.
The semantic source pin remains LPS
`f1006fe8178338a499b5e5c41be83006c4edd058`.

## Implemented additive proof helpers

`Silmaril.Process.LPS.RunHelpers` imports the existing run/equivalence
definitions without replacing them. `ShapesParity` imports Shapes and these
helpers. Both new modules were compiled with `-DwarningAsError=true`.

| Pinned source | New Lean result | What it establishes |
| --- | --- | --- |
| `Equivalence.v:558` | `reservedTop_nonneg` | Reservation tops are nonnegative. |
| `Equivalence.v:569` | `imageBrkWitness_bounds` | The rounded break is aligned and less than one page above the top. |
| `Equivalence.v:590` | `imageBrkSatisfiable_sound` | The boolean check supplies an actual valid break. |
| `Run.v:2590` | `entryStackSpan_bound` | Valid argv/envp need at most 2,238,671 bytes. |
| `Equivalence.v:612` | `imageBrkSatisfiable_entry`, `imageWf_entry` | Every valid legacy input has a valid entry for an accepted image. |
| `Equivalence.v:650` | `imageBrkSatisfiable_bites` | A reservation top at or above 2^64 fails the break check. |
| `Shapes.v:161` | `Shapes.agrees_iff_agreesIn_mayFail` | The plain and explicitly may-fail agreement shapes coincide. |
| `Shapes.v:455` | `Shapes.disagreesAtMost_of_classifier_imageWf` | The classifier reduction now needs image well-formedness, without a separate entry-existence assumption. |
| `Shapes.v:475` | `Shapes.disagreesAtMostRv64gc_of_classifier` | The corresponding RV64GC-restricted classifier bound. |
| `Shapes.v:491` | `Shapes.agreementDecidableRv64gc_of_classifier` | A well-formed RV64GC classifier witnesses decidability. |

The original `Shapes.disagreesAtMost_of_classifier` signature is retained for
compatibility. Its replacement corollary derives that signature's extra entry
hypothesis from `ImageWf`, matching the pinned source's assumption strength.
The proof does not need entry fetchability or readable program headers for the
entry-existence step; the break conjunct suffices. Those other checks remain
necessary parts of the public `ImageWf` anti-vacuity contract.

## OmniRun: finite/terminating core implemented; safety/prefix bridge remains

Pinned `LinuxProcessSem/OmniRun.v` is additive upstream too. The module
`RunHelpers` exports its new judgments under `Silmaril.Process.LPS.Omni`:

- `Outcome` retains the halted configuration, or the configuration from which
  an error step was taken. The latter is needed to distinguish faults from
  model gaps.
- `FiniteExec` represents maximal finite runs, including the events of an
  error step. `star_finiteExec`, `finiteExec_error_star` and
  `reachesError_iff_may` connect it to the existing step/star/error relations.
- `Exec` is an inductive universal terminating judgment with a trace/outcome
  postcondition. `Exec.consequence` weakens the postcondition;
  `Exec.sound` covers every admitted finite run; `Exec.realizes` supplies an
  actual finite run. `stuck_no_exec` pins down the progress requirement.
- `mustExitInAt_iff_exec` relates the existing must-exit predicate to the
  normal-exit postcondition, explicitly excluding signal deaths.
- `Progress.halting_path_not_allTracesError` refutes the universal all-error
  observation from any actual halting path; the supporting next/star rules
  make this reusable for concrete ELF execution controls.

These judgments retain the existing arbitrary `UserIsa`, syscall specification
and refusal-filter parameters. There is no architecture-specific interpreter
hidden in the helper. The code follows the finite/inductive source core at
`OmniRun.v:113-355`, with the must-exit connection derived from the existing
Lean definition.

The following portions remain separate work: coinductive `coexec`,
`coexec_progress` and `cosafe`; their safety/prefix characterization theorems;
the `run` wrappers and complete `bh_*_iff` surface; and `OmniEquivalence.v`.
Lean has no native coinductive inductive declaration. A next step can encode
safety by quantifying over `FiniteExec`, and prefix safety over `Star` plus
prefix closure, then prove those encodings satisfy the pinned unfolding and
observable-equivalence laws. A terminal-outcome judgment alone cannot establish
trace equivalence: writing a byte and then diverging differs observably from
silently diverging even though neither run has a finite terminal outcome.

## GatedSize: precise missing scope

`EquivalenceDefinition/GatedSize.v` remains unported. The source at the semantic
pin supplies:

- `slice_accept`/`slice_rest` (215/224), gate-order disjointness and exhaustive
  partition results; forced-only counterparts begin at 734/738.
- `gated_slice_T`/`gated_slice_error_free_T` (330/343), universal-to-slice
  reduction (362/370), and contravariance when the slice shrinks (381/390).
- `weight_bound_pred_T` (421), identification with the classifier's reject
  bound, bound monotonicity, and tests explaining why core distinctness matters.
- Configured comparison shapes (862/877), plus explicit empty-slice and
  missing-source/target-entry vacuity witnesses.

A minimal faithful port should reuse `FinProcInput`, `AcceptsFo`, `RejectsFo`,
`sumWeights` and the existing `StrongEquiv*` definitions. It must keep the
source, target and classifier budgets separate, preserve independent source
and target entry quantifiers, and retain core-level `Nodup` in weight bounds.
There is no general monotonicity of **two-run trace equality** in the refusal
configuration: restricting both runs can remove different traces.

Gate images require inhabited-entry checks too. A universally quantified gate
with no valid entries accepts vacuously, so it can swallow every later slice.
The new `imageWf_entry` supplies the legacy remedy; it does not remove the need
to require `ImageWf` for each named gate.

## Architecture/profile boundary

The entry theorem deliberately proves the existing legacy `ValidEntry` under
`ValidInput`, which fixes Sv48. It does not change `initConfig`, the historical
constant Sv48 syscall gate, alternative-width sealed statement families, or
the new native x86 launch option. `AddressSpaceProfile` and `LaunchBounds` are
separate: a buffer-check limit is not a stack/ASLR policy.

Native x86 statements must use the native launch option and syscall/refusal
adapters together, then establish an analogous inhabited-entry lemma for that
chosen policy. Width-sensitive RISC-V profiles are explicit options; selecting
one is not a proof that every syscall or structure layout respects it. Pending
syscall-family translations and whole-corpus ISA coverage are tracked outside
this shape audit.

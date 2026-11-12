# `bv_decide`, its trusted base, and `bv_decide_kernel`

Status as of 2026-11-12, toolchain `leanprover/lean4:nightly-2026-11-05`
(Lean 4.37.0-nightly, commit `67dafde4`).

## What `bv_decide` trusts

`bv_decide` proves a `BitVec`/`Bool` goal in two stages.

1. **Normalization.** `bv_normalize` rewrites the negated goal with the
   `bv_normalize` simp set. When this reaches `False` the proof is an ordinary
   term, checked by the kernel, on `propext`, `Classical.choice` and `Quot.sound`.
2. **SAT.** Otherwise the goal is reified to a `BVLogicalExpr`, bitblasted to an
   AIG, turned into CNF and sent to the bundled external solver (CaDiCaL). The
   solver's LRAT certificate, a `String`, is checked by
   `Std.Tactic.BVDecide.Reflect.verifyBVExpr`. The tactic does not ask the kernel
   to evaluate that check. `Lean.Meta.nativeEqTrue` compiles it, runs it, and
   asserts the result `verifyBVExpr e cert = true` as a fresh axiom
   `<decl>._native.bv_decide.ax_<n>`. Soundness then follows from the proved
   `unsat_of_verifyBVExpr_eq_true`.

So the external solver is **not** trusted: a bad certificate makes the check
return `false` and the tactic fails. What is trusted in stage 2 is the compiler
and runtime that evaluate `verifyBVExpr` (code generation, `@[extern]`/
`@[implemented_by]` implementations such as `mixHash`, GMP, `ByteArray`), the
same base as `native_decide`. `#print axioms` shows it as the `_native` axiom.
This library's policy (`policy.toml`, AGENTS.md) admits only the three standard
axioms. It forbids `native_decide`, and for the same reason the SAT stage.

## `bv_decide_kernel`

`Silmaril/Prelude/BVDecide/Defs.lean` defines `bv_decide_kernel`, a
fail-closed subset of `bv_decide`. It runs stage 1 only:

* if `bv_normalize` does not close the goal, it fails (it never calls the
  solver);
* it then collects the proof's axioms transitively (`Lean.collectAxioms`) and
  fails unless they are among `propext`, `Classical.choice` and `Quot.sound`.

When it succeeds, it proves the goal as stated, the same statement `bv_decide`
would prove, with a kernel-checked term. It is **not** a kernel LRAT checker:
goals that need SAT are rejected. `scripts/check-layout.sh` rejects plain
`bv_decide` invocations under `Silmaril/`. The six former uses, in
`Silmaril/X86/Float/State.lean`, now use `bv_decide_kernel`. On main they were
already closed in stage 1 and had standard axioms only (measured below), but
nothing checked that.

## Why the SAT stage cannot simply be kernel-checked today

Measured on the toolchain above:

* `decide +kernel` gets stuck on `mixHash 1 2 == mixHash 1 2`: `mixHash` is an
  opaque `@[extern]` constant. Bitblasting (`BVLogicalExpr.bitblast`) hash-conses
  AIG nodes through `HashMap`, so even `e.bitblast.aig.decls.size` for a 4-bit
  equality does not reduce in the kernel.
* `verifyCert` parses the certificate with `partial` functions
  (`Std.Internal.Parsec.manyCore`, `LRAT.Parser.Binary.*.go`), which the kernel
  cannot unfold. This was noted on lean4#12509, which lists the opaque and
  partial dependencies of `verifyBVExpr`.

A kernel-checked SAT stage therefore needs upstream changes: a kernel-reducible
bitblaster (no opaque hashing) and certificate format (pre-parsed actions, not
`String`), or a different evaluator. `Std.Tactic.BVDecide.LRAT.check_sound`
(`check : Array IntAction → CNF Nat → Bool`) is the reusable checker theorem
for that route.

## Upstream status (leanprover/lean4)

Checked with `gh` against `leanprover/lean4` on 2026-11-12. "First release" is
the earliest release tag whose history contains the merge commit (GitHub compare
API). All four merged PRs are also in this repository's toolchain commit
`67dafde4`.

| PR | What | State | Merge commit | First release |
| --- | --- | --- | --- | --- |
| [#12217](https://github.com/leanprover/lean4/pull/12217) | One axiom per native computation (`nativeEqTrue`, `_native.bv_decide.ax_…`) | merged 2026-02-03 | `2907df22ec` | v4.29.0 |
| [#14842](https://github.com/leanprover/lean4/pull/14842) | New LRAT checker (new CNF API, "slightly faster") | merged 2026-08-27 | `f3c6b8462d` | v4.35.0 |
| [#14953](https://github.com/leanprover/lean4/pull/14953) | Remove `Lean.ofReduceBool`/`reduceBool`/`trustCompiler` | merged 2026-08-28 | `2a7175c74b` | v4.35.0 |
| [#15144](https://github.com/leanprover/lean4/pull/15144) | LRAT checker accepts satisfied RUP hints | merged 2026-09-13 | `3824dbfae6` | v4.35.0 |
| [#12509](https://github.com/leanprover/lean4/pull/12509) | Experiment: `bv_decide -native`, certificate checked by `cbv` | **open draft**, last updated 2026-07-14; contains `sorry` | – | – |

Related open items: [#1101](https://github.com/leanprover/lean4/issues/1101)
(faster kernel reduction engine), [#5806](https://github.com/leanprover/lean4/issues/5806)
(optimizing terms for kernel reduction),
[#14977](https://github.com/leanprover/lean4/issues/14977) (kernel logic
renovation). No merged upstream change gives `bv_decide` a kernel-checked SAT
path. This repository has no other LRAT work. Its kernel-evaluation
measurements are for Wasm (silmaril-lean#105).

## Measurements

`benchmarks/bv-decide/run.py`, recorded in
`docs/benchmarks/bv-decide-2026-11-12.json`. These are wall times of `lean FILE`,
minimum of 3 runs (2 for the PR toolchain), on a 2-vCPU sandbox. Lean startup
(about 0.23 s) is included. "native" marks a `_native.bv_decide` axiom in the
proof.

| Goal | `bv_decide` | `bv_normalize` (= `bv_decide_kernel`) | `decide +kernel` (whole domain) | #12509 `bv_decide -native` |
| --- | --- | --- | --- | --- |
| setLane32, zeroLane64, le32, le64 (State.lean shapes) | 0.24–0.28 s, standard axioms | 0.24 s, standard axioms | – | 0.26–0.28 s |
| addsub64 `x + y - y = x` | 0.24 s, standard | 0.24 s, standard | – | 0.26 s |
| xorswap32 | 0.26 s, native | fails | – | kernel rejects (0.61 s) |
| lowbit8 | 0.27 s, native | fails | 0.28 s, standard | kernel rejects (8.4 s) |
| lowbit32 | 0.26 s, native | fails | – | kernel rejects (8.4 s) |
| avg32 | 0.28 s, native | fails | – | kernel rejects (0.70 s) |
| mulcomm8 `x * y = y * x` | 1.64 s, native | fails | 9.85 s, standard | kernel rejects (1.57 s) |
| mulcomm16, muldist8 | solver timeout (10 s default) | fails | – | solver timeout |
| muldist4 | – | – | 0.84 s, standard | – |

"Kernel rejects" means the `cbv` proof of PR #12509's `pr-release-12509`
toolchain (Lean 4.32.0-pre, 2026-06-02) failed with "unexpected kernel
projection term during structural definitional equality". The experiment does not
produce kernel-checkable proofs for any goal here that needs SAT. Exhaustive
`decide +kernel` is the only kernel route measured for those goals. It is about
6× slower than native at 16 input bits (mulcomm8) and grows as 2^bits.

## Proposed CI and modes (not implemented here)

Mode selection belongs to the separate mode-mechanism work. This proposal is for
that work and for review.

* **One statement, two proofs.** A fast mode may prove a goal with `bv_decide`
  (native) only where the paranoid mode proves *the same declaration* by a
  kernel-only route. Both modes should elaborate the same source and
  compare the declaration's type hash, never two copies of a statement. A mode
  switch should be a tactic that reads an option, not two theorem names.
* **Per pull request (fast).** Build with the fast mode; run the layout gate;
  report, per changed module, the declarations whose axioms include `_native`.
* **Daily on main (paranoid).** `nightly.yml` already runs the full
  `make check` on main. Add a paranoid build in which every fast-mode site is
  kernel-only, and fail on any `_native`, `sorryAx` or other non-standard axiom
  of any declaration (a transitive `collectAxioms` over the environment; the
  "transitive automated checking" that `policy.toml` lists as missing).
* **Caching.** Lake traces must include the mode: the option belongs in the
  module's Lake configuration (or a separate Lake library/package), so the
  paranoid build never replays fast-mode artifacts. Its cache keys should differ,
  and its publication should be separate. A cache hit on a paranoid artifact is fine; a fast artifact
  must never count as a paranoid build.
* **Allowlist.** Any native use is an explicit `[[exception]]` in
  `policy.toml` (declaration name, `_native.bv_decide` axioms, reason, and the
  paranoid route that discharges it). The gate fails on native uses not listed.
* **Reproducibility.** Pin the toolchain (already exact) and record the solver
  (`sat.solver` defaults to the bundled CaDiCaL). The certificate is not part of
  the proof term's trust, but an LRAT file (`bv_check`) makes re-runs
  independent of solver nondeterminism and timeouts.

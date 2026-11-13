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
return `false` and the tactic fails. The natively evaluated procedure is the
whole of `verifyBVExpr e cert = verifyCert (AIG.toCNF e.bitblast.relabelNat) cert`,
not only an LRAT check:

| Part | How it is checked |
| --- | --- |
| `bv_normalize` (rewriting) | kernel |
| reification to `BVLogicalExpr` | kernel (the proof that the reflected expression denotes the goal is kernel-checked) |
| bitblasting to an AIG (hash-consed through the opaque `mixHash`) | **native** |
| AIG to CNF, relabeling to `Nat` variables | **native** |
| LRAT parsing (`partial` parser over the certificate `String`) | **native** |
| LRAT checking (`LRAT.check`) | **native** |
| `unsat_of_verifyBVExpr_eq_true` (soundness of all the above) | kernel (proved in `Std`) |
| producing the certificate (CaDiCaL) | untrusted |

The native rows run on the compiler and runtime (code generation,
`@[extern]`/`@[implemented_by]` implementations, GMP, `ByteArray`, `String`), the
same base as `native_decide`. `#print axioms` shows the result as the `_native`
axiom. This library's policy (`policy.toml`, AGENTS.md) admits only the three
standard axioms.

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

## Registered native procedure and modes

The trust framework (`Silmaril.Prelude.Trust`, docs/trust.md) has three profiles.
**default** runs the procedures in the `default` trust set, **local** runs every
procedure a scope's `max` allows, and **paranoid** runs none (kernel fallback or
fail). `bv_decide` goes through it as follows.

* `Silmaril/Prelude/BVDecide/Native/Defs.lean` is the **only** module that invokes
  `bv_decide`, and it does so exactly once (`scripts/check-layout.sh`). Every other
  module uses `bv_decide_kernel` or `bv_decide_policy`. The gate has no per-site
  exceptions.
* It registers the procedure with `native_tactic`:

  | Field | Value |
  | --- | --- |
  | name | `lean.std.bv_decide.verifyBVExpr` (the surface includes bitblasting and the parser, so not "LRAT") |
  | evaluates | `Std.Tactic.BVDecide.Reflect.verifyBVExpr` (`nativeEvaluatedConst`) |
  | axiom tag | `bv_decide`: `<decl>._native.bv_decide.ax_<n>` |
  | components | bitblasting (hash-consed through `mixHash`), AIG to CNF, relabeling, LRAT parser (`partial`), LRAT checker, runtime externs |
  | toolchain | `leanprover/lean4:nightly-2026-11-05`, commit `67dafde4` (`registeredToolchain`, `registeredGithash`) |
  | fallback | **none registered**: the kernel route (`bv_decide_kernel`) covers only goals `bv_normalize` closes, so the registration does not claim a kernel fallback |
  | untrusted | the external SAT solver |

* `bv_decide_policy` checks the registration on every use (`registrationProblem`):
  the evaluated constant exists and is `nativeEvaluatedConst`, the tag is
  `bv_decide`, no kernel fallback is claimed, and the registered toolchain and the
  running Lean's commit are the reviewed ones. Then it:
  1. tries `kernelFallback` and, if that proves the goal, records a `kernel` use;
  2. otherwise runs `bv_decide` only if `Silmaril.Trust.nativeAllowed` admits the
     procedure, and fails if not. No kernel route exists for goals that need SAT.
  3. after a native run, requires every axiom of the proof outside the standard three
     to be absent before this invocation, to have the `bv_decide` name shape, and to
     state one closed `verifyBVExpr e cert = true`. It records each as a `native` use
     with its axiom.
* The procedure is **not** in the `default` set. Adding it needs its own reviewed
  change. Until then, goals that need SAT fail in the default and paranoid profiles,
  and run natively only where a build or module opts into `local`.

Checked outside the library on this branch (a scratch module, so the library holds no
native axiom): in profile `local`, `x * y = y * x` on `BitVec 8` is proved with
`sat._native.bv_decide.ax_1_5`. It is recorded as a `native` use with that axiom, and
`trust_audit` passes under `local` and fails under `default`. The library tests cover
the registration check, the kernel route, and the failure of SAT goals in the default
and paranoid profiles.

**Known gap in the audit (core).** `trust_audit` classifies a `_native.bv_decide`
axiom as the registered procedure by its tag alone. A plain `bv_decide` outside the
framework, which records no use, passes `trust_audit` under `local` with no violation
(checked in a scratch module). Today only the textual gate prevents this. The audit
should require each native-tactic axiom to match a recorded `native` use with that
axiom (`Use.ax`) and the registered toolchain, and report a violation otherwise.

`Silmaril/Prelude/BVDecide/Defs.lean` exports the hooks used here:

* `kernelFallback : MVarId → (cfg := …) → TermElabM KernelResult`: `.proved`, or
  `.needsSat` with the goal restored unassigned. It throws on `sorry` or
  non-standard axioms.
* `nonstandardAxioms : Expr → MetaM (Array Name)`: the transitive axioms of a
  proof outside the standard three.
* `isBvDecideNativeAxiom : Name → Bool`: name-shape recognition only, never
  authorization.
* `isBvDecideNativeStatement : Name → MetaM Bool`: an axiom's statement is one closed
  `verifyBVExpr e cert = true`.
* `nativeEvaluatedConst`, `nativeSoundnessConst`: resolved at compile time.

There is **no kernel-checked SAT route**. Paranoid mode cannot prove a goal that
needs SAT except by a different, goal-specific proof (for example `decide +kernel`
over a small domain, measured above).

## CI

* **Per pull request (default mode).** Build; run the layout gate; report each
  declaration whose transitive axioms include a registered native procedure, and
  fail on any native axiom not bound to a registered entry.
* **Occasionally on main (paranoid, timed).** Every site uses its kernel fallback.
  Record wall time (the nightly already runs `/usr/bin/time -v make check`).
  Fail on any non-standard axiom anywhere, and list the `needsSat` sites as
  unsupported. Today `main` has no native uses at all, so every build is already
  the paranoid build. On #107, `lean / check` took 2 min 14 s, scoped and cached.
* **Same statements.** Both modes elaborate the same source, and a mode is an
  option read by the tactic, so the declaration names and types are identical by
  construction. A paranoid run should still compare each declaration's type hash
  with the default run.
* **Caching.** The mode must be part of Lake's trace (a Lake option or a separate
  library), so a default-mode artifact never satisfies a paranoid build. Paranoid
  artifacts may be cached and reused, but only as paranoid artifacts.
* **Reproducibility.** Pin the toolchain (already exact) and record the solver.
  An LRAT file (`bv_check`) removes solver nondeterminism and timeouts from
  re-runs, but it is still checked natively.

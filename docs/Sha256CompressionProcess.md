# SHA compression in process executions

Tracking: [#3033](https://github.com/hiloopai/silmaril/issues/3033),
[PR #3040](https://github.com/hiloopai/silmaril/pull/3040),
[campaign #3025](https://github.com/hiloopai/silmaril/issues/3025).
Baseline: merged #2938, `dae375685d8459ceccc6fb3fa083b3ff8d895b22`.

The new results connect the existing compression theorem to actual finite
process steps. They do not prove the SHA driver's I/O, padding, hex output,
launch or global progress contracts. There are no new compiler variants,
instruction semantics, axioms, admitted proofs or unmerged PR dependencies.

## Generic adapter

Import `Silmaril.Process.CLI.X86Linux.Silent`.

* `step_of_ext_retired` and `step_of_ext_returned` translate actual `Ext.step`
  results. `Ext.fetch_length` reconciles the Ext executor's default length
  with the Linux wrapper's fetched length. A decoded Ext instruction cannot
  begin with executable `0F 05`: the decoder rejects that prefix with every
  possible suffix. No unsupported opcode is assumed to crash.
* `runs_of_ext_run` adapts exactly the supplied finite retirements.
  `runs_of_ext_returns` also executes the final RET; a function return is
  another internal instruction, not process exit. Both emit `[]`.
* `continue_of_ext_returns` prepends that segment without changing the
  continuation's observable trace. It supplies an execution witness; it does
  not claim every caller terminates.

`Env.Lawful` has memory-readback and exit-preservation laws, but lacks update
identity and overwrite. The separate `Env.MemoryLens` interface adds those
two laws; Linux and its three restrictions satisfy them by record update.
The generic endpoint is exactly `E.withMemory s final.memory`. Hidden state
for an arbitrary environment is specified only by that expression. In
concrete Linux, descriptors and exit state are unchanged, as recorded by
`linux_endpoint_preserved`.

## The sha256sum machine

Import `Silmaril.Apps.Sha256sum.X86Sys.Silent`.

`toExtState` projects the core/memory; `withExtState` replaces precisely those
fields, preserving `brkStart`, `brk` and `faulted`. From `faulted = false`,
`ext_run_tauRun` gives exactly `n` internal steps, and `ext_returns_tauRun`
gives `n + 1`, including RET. `TauRun.reach` keeps the exact kernel state.
`TauRun.exec_iff` and `exec_iff_of_ext_returns` keep the entire continuation's
call/reply list and exit status in any `Sys.Env`.

Every theorem quantifies over `r11Of`. Syscall R11 choices outside the segment
remain unrestricted. R11 is not among the callee-saved guarantees.
`TauRun` is an adapter-local, tau-only relation; it neither replaces the
shared process trace API nor states the driver's trace contract.

## Linked callee and caller obligations

Import `Silmaril.Apps.Sha256sum.Binary.Process`.

* `compress_returns_silent` pairs the actual silent segment with the unchanged
  `Binary.compress_contract` postcondition.
* `compress_silent` reuses the already proved callee execution theorem to
  supply such a segment at a valid entry. This adds no global driver budget.
* `compress_exec_iff` and `compress_exec_continuation` expose the certified
  endpoint inside completed `Sys.Exec` executions. `Post.compressed`, RSP
  after RET, System V callee-saved registers, and `Post.untouched` are retained.
* `compress_cli_returns` and `compress_cli_continue` instantiate the generic
  CLI adapter at the same linked layout.
* `compress_silent_of_loaded` combines the caller-owned clauses with loaded
  code/K preservation and applies the process contract immediately.

`Binary.CallSite` retains every `SysVEntry` clause except `code`, `kTable`
and `relocFits`. `CallSite.entry` supplies those constants and the checked
linked relocation. `CallSite.entry_of_loaded` uses `loaded_code` and
`loaded_kTable` from an earlier mapped memory and a `WritesWithin` fact whose
footprint excludes code and K. It does not require mutable image data to
retain their initial contents at call time. `callSite_realisable` uses the
existing backed-entry construction to prove these caller clauses satisfiable
at the linked layout, for every return address.

`post_readWith_region`, `post_readBytes_region` and `post_fetchBytes_region`
preserve any driver buffer disjoint from the state output and callee frame.
`post_code` and `post_kTable` specialize the existing separation facts so
another compression call can reuse the constants.

The driver still owes its actual call-site registers, backed buffers, return
slot, alignment, frame mapping and separation; preservation of constants
through its preceding writes; and its read/padding/output invariants.
The SHA owner is [#3029](https://github.com/hiloopai/silmaril/issues/3029).
General Ext instruction changes belong to
[#3032](https://github.com/hiloopai/silmaril/issues/3032).

## Evidence and reproduction

These are ordinary Lean proofs over the repository's handwritten Ext and
Linux process models. The linked byte transcription, load facts and existing
compression proof are reused, not regenerated. This is a model-relative
binary callee composition result, not hardware correspondence or a complete
`sha256sum-min` execution proof. No native SMT result or runtime example is
used as a proof premise. No new Rust/PyO3 proposal tool is needed for these
lemma applications.

The ELF ingestion boundary remains the existing generated `Binary.Image`
embedding. No new theorem connects a live external file or a hardware run
to that embedding; the adapter preserves the inherited boundary.

The inherited x86-64 binary is `sha256sum-min`, GCC 13.3.0 `-O2` driver with
the Clang 18.1.3 `-O2` compression callee. Its ELF SHA-256 is
`22fa6345cc5bed08f07d4d5a0836885118259a73402470e4d7f7a7a81ad42817`.
Exact object/byte/K hashes and upstream command references remain in
`Crypto/X86/Sha256O2/Image.lean`, `Binary/Compress.lean`,
`Binary/Layout.lean` and `scripts/sha256sum/regen-binary.sh`.
The existing filter's independent manifest remains
`apps/sha256-cli/manifest.json`. This patch makes no new `-O3` result;
the campaign's named GCC/Clang `-O3` artifacts and residual obligations
in other PRs are unchanged and are not imported dependencies.

Run only the affected targets:

```sh
lake build Silmaril.Process.CLI.X86Linux.Silent \
  Silmaril.Process.CLI.X86Linux.ExtStepControls \
  Silmaril.Apps.Sha256sum.Binary.Process \
  Silmaril.Apps.Sha256sum.X86Sys.SilentControls
sil gen umbrellas --check
sil gate
git diff --check
```

The final validation receipt is `scripts/sha256sum/compress-bridge-validation.json`.
It records source fingerprints, proof artifact sizes, commands, assisted proof
status, and the pending CI/replay boundary. Artifact sizes are Lean module
artifacts, not a standalone compressed proof certificate. Model-source hashes
cover exactly the named source files, not a separately replayed transitive
axiom closure. Dependency cache fetching and full SHA proof reuse are not new
compression-proof measurements. Paid agent cost is available only in session
accounting and is not estimated here. Full local builds, local kernel replay
and full axiom audits were not run; CI supplies those checks.

Completion correctness and prefix safety remain independently selectable.
An unchanged completed continuation trace does not establish a prefix policy
for some later failing run, or coverage/progress for the surrounding driver.

## Concrete filter call-site increment

[PR #3052](https://github.com/hiloopai/silmaril/pull/3052) is stacked on
#3040, with its adapter interfaces as the explicit dependency. No other
unmerged implementation is copied. New modules:

* `X86Linux.Call` checks actual direct CALL execution, its five-byte length,
  return-slot backing and disjoint read preservation. `direct_call_frame`
  includes both the callee footprint and CALL's return-slot write; omitting the
  slot would be false. `ext_returns_target` exposes the exact continuation PC.
* `X86Linux.SilentTransport` cancels or inserts silent segments in completed
  observations/contracts while retaining the exact event list, final state
  and outcome. It assumes only instruction-result determinism, leaving syscall
  replies/resume nondeterministic. Prefix transport separately requires
  acceptance of `[]` because a finite prefix can end inside the segment.
* `Sha256Cli.Compress` binds the retained filter's entire 459-byte callee at
  `0x4002e0` and K table at `0x4004c0` to the existing proof. Its actual final
  padding CALL is `E8 B2 00 00 00` at `0x400229`, returning to `0x40022e`.
  Loader/frame facts and concrete buffer/stack geometry are proved, including
  offset/length rejection controls.
* `Sha256O2.Reference` proves, for every hash state and complete 64-byte block,
  agreement with the canonical `SHA256.processBlock`. It reuses the existing
  cryptographic equivalence and proves the byte parsing/representation bridge.
  `Post.compressed_reference` is the small interface for the SHA owner's
  `Driver.compressBlock` transition; no Driver module is imported.
* `Sha256Cli.EmptyCall` prepares the full mapped filter memory with checked
  writes of the initial hash and the canonical padding of empty input, then
  proves the actual CALL, stack write and every callee-entry hypothesis.
  `empty_call_result` gives the published empty hash, PC `0x40022e`, restored
  caller RSP/callee-saved registers and the entire caller-visible frame.
  `empty_call_reference` gives exactly the canonical `SHA256.hash []` state.
  The environment witness has standard descriptors and is still running.
* `empty_completed_contract` reduces any completed-observation contract to the
  certified continuation. `empty_prefix_contract` is separately conditional
  on permitting `[]`. These can feed #3047's institutional interpretation
  without adding a second institution or a totality premise.

The concrete stack is caller RSP `0x7ffeffe0`, callee RSP `0x7ffeffd8`;
buffers are the binary's actual H `0x401660` and block `0x401620`.
These are nonvacuous executable-model call-site results. The prepared state
is not asserted reachable from launch: the original EOF/read path and the
driver's actual initialization/padding stores still need that connection.
Hex serialization, accepted output and final exit correctness remain with
#3029. No source-equivalence, graph-to-machine, O3 or hardware result follows
merely from the call-site theorem. Unknown instructions remain residual.

Additional targeted reproduction:

```sh
lake build Silmaril.Process.CLI.Sha256Cli.EmptyCall \
  Silmaril.Process.CLI.X86Linux.CallControls
lake env lean scripts/sha256sum/SilentTransportControls.lean
sil gen umbrellas --check
sil gate
```

The concrete control script proves an actual RET-to-exit completed CLI run,
two-way silent cancellation, exclusion of a premature stop and rejection of a
syscall mutation as silent. Other controls reject a wrong CALL length, wrong
return target, off-by-one callee extraction and wrong hash word. The new
receipt is `scripts/sha256sum/callsite-validation.json`; the first-slice
receipt above remains a historical checkpoint. All published proof files
compile; no pending lemma is in the import closure. Full builds/replay and
the full axiom audit remain CI work, and follow-up features have no merge
authorization.

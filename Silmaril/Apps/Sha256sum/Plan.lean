module

public import Silmaril.Apps.Sha256sum.X86Sys
public import Silmaril.Apps.Sha256sum.StdinRef
public import Silmaril.Apps.Sha256sum.Binary

/-! # PLAN: the binary theorems, stated

**The `def … : Prop`s in this file are targets, not results.** Nothing here asserts them;
there is no `sorry`. The theorems at the end are proved: they say what each target buys.

## The full statement

`FullGoal`: for every way Linux may fill `r11`, every launch of `sha256sum-min` on a world
of `FullDom` (any `argv`, `POSIXLY_CORRECT` or not, any file system, any standard input,
standard output full or not) has

* **safety** (`SatisfiesRel`): every exiting run, under every read chunking and write split
  `Sys.WorldStep` admits, writes exactly `(sha256sum w).stdout` to fd 1 and
  `(sha256sum w).stderr` to fd 2 and exits with `(sha256sum w).status`;
* **liveness within a budget** (`LiveRel`): no run gets stuck (no fault, nothing unmodeled,
  no bad pointer passed to the kernel) and every run on `w` is at most `N w` steps.

`FullDom` excludes only what the kernel itself fixes: `argv` nonempty and NUL-free, the
empty path and paths of 4096 bytes or more failing as Linux makes them fail. The
specification's own exclusions (spec.md §1: C locale, descriptors 0–2 open, default
`SIGPIPE`, no concurrent file change, no out-of-memory) are built into `Sys.WorldStep` and
`X86Sys`.

`CompletedGoal` and `SafetyGoal` below separate successful answers and all
exiting observations from that optional liveness requirement. Neither implies
anything about output prefixes of a later failing run. The independent
digest-prefix target for the retained freestanding filter is
`Process.CLI.Sha256Cli.prefixGoal`.

The current `X86Sys.brkStep` is an idealized allocator: growth is always granted,
with no address-limit or overlap test. `Init` puts the heap above the image but
does not separate all future heap growth from the initial stack. Thus even a
proof of these targets would need a heap/frame and allocation-refusal bridge
before implying real Linux behavior; OOM is not a proved hardware crash.

## Stage S1, through the reference program

`S1Refines`: on `Sys.StdinDom` (no operand, finite stdin, stdout not full) every exiting run
of the binary is, call for call, an exiting run of `Sys.refMachine`. `s1_satisfies` (proved)
turns it into the S1 safety statement for the binary, using `Sys.ref_satisfies`. `S1Live`
is the matching liveness target; the reference program's version is `Sys.ref_live`.

## What blocks the binary proofs (measured)

1. **The ISA model.** `tools/x86-lift --process` on `sha256sum-min` stops at its first
   instruction outside `X86.Ext`: `test %cl,%cl` (`Test_rm8_r8`) at `0x40102f`.
   `X86.Ext.Sz` has only 32- and 64-bit operand sizes for ALU forms, and gcc uses 8-bit
   `cmp`, `test`, `sub`, `or`, `and`, `xor` and `shr` about 300 times in the driver (byte
   and character tests; an `objdump` count). `cmov` (2) and `mul` (2) are only in `X86.Ext.Wire`. Until `Ext` has 8-bit ALU
   forms, the binary cannot be transcribed, and no step of it outside `sha256_compress`
   can be reasoned about.
2. **The call bridge.** `Binary.compress_contract` is an `Ext.Returns` statement about a
   called function; using it inside a `Sys.Exec` run needs a lemma that an `Ext.Returns`
   run of a callee is a sequence of `X86Sys` `tau` steps with no system call. The same
   lemma is open for the `apps/sha256-cli` binary (`Process/CLI/Plan.lean` item 3).
3. **The driver's invariants.** Read loop, buffer management (`sha_update`/`sha_final`),
   hex output, the stdout buffer and `close_stdout`; then option scanning, `quotef`, and
   the `--check` parser, each against the matching part of the specification
   (`Options`, `Quote`, `CheckLine`, `Run`).
4. **Non-vacuity.** `InitRealisable`: every world of the domain has a launch state. The
   `apps/sha256-cli` proof `init_exists` is the template.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Plan

open Silmaril.Apps.Sha256sum
open Silmaril.Apps.Sha256sum.Sys
open Silmaril.Apps.Sha256sum.X86Sys

/-- The worlds the binary is claimed for. -/
def FullDom (w : World) : Prop :=
  w.argv ≠ [] ∧ (∀ a ∈ w.argv, (0 : UInt8) ∉ a) ∧ w.fs [] = .openErr .ENOENT ∧
    ∀ p : Bytes, 4096 ≤ p.length → w.fs p = .openErr .ENAMETOOLONG

/-- **The full theorem** for `sha256sum-min`: safety, and liveness within a per-world step
budget, over the x86-64 Linux process model with files. -/
def FullGoal : Prop :=
  ∀ r11Of : Core → Silmaril.X86.Word,
    SatisfiesRel (x86Machine r11Of) WorldStep (Init Binary.Image.image) FullDom ∧
      ∀ w, FullDom w → ∃ N,
        LiveRel (x86Machine r11Of) WorldStep (Init Binary.Image.image) (· = w) fun _ => N

/-- Correct successful answers only, independently of prefix safety and progress.
This is a target over the existing idealized allocator, not a binary result. -/
def CompletedGoal : Prop :=
  ∀ (r11Of : Core → Silmaril.X86.Word) (w : World), FullDom w →
    ∀ s, Init Binary.Image.image w s → ∀ evs,
      Exec (x86Machine r11Of) (WorldStep w) s (KState.init w) evs 0 →
        observe evs 0 = sha256sum w

/-- All exiting observations agree with the spec; progress is independent.
Completion-only refinement does not supply a prefix theorem. -/
def SafetyGoal : Prop :=
  ∀ r11Of : Core → Silmaril.X86.Word,
    SatisfiesRel (x86Machine r11Of) WorldStep (Init Binary.Image.image) FullDom

theorem safety_of_fullGoal (h : FullGoal) : SafetyGoal := fun r11Of => (h r11Of).1

theorem completed_of_safety (h : SafetyGoal) : CompletedGoal :=
  fun r11Of w hw s init evs run => h r11Of w hw s init evs 0 run

/-- **S1**: on the stdin path the binary trace-refines the reference program. -/
def S1Refines : Prop :=
  ∀ r11Of : Core → Silmaril.X86.Word,
    TraceRefinesRel (x86Machine r11Of) refMachine WorldStep (Init Binary.Image.image)
      (fun _ => .reading []) StdinDom

/-- **S1 liveness**: linear in the length of standard input. -/
def S1Live : Prop :=
  ∃ c, ∀ r11Of : Core → Silmaril.X86.Word,
    LiveRel (x86Machine r11Of) WorldStep (Init Binary.Image.image) StdinDom
      fun w => c * ((match w.stdin with | .bytes b => b.length | .dir => 0) + 1)

/-- Non-vacuity: every world of the domain has a launch state. -/
def InitRealisable : Prop :=
  ∀ w, FullDom w → ∃ s, Init Binary.Image.image w s

/-- What `S1Refines` buys: S1 safety for the binary, from the reference program's proof. -/
theorem s1_satisfies (h : S1Refines) (r11Of : Core → Silmaril.X86.Word) :
    SatisfiesRel (x86Machine r11Of) WorldStep (Init Binary.Image.image) StdinDom :=
  SatisfiesRel.of_traceRefines (h r11Of) ref_satisfies

/-- What `FullGoal` buys at a smaller environment: the same statements hold for any kernel
that admits fewer replies (for example one that never splits a write). -/
theorem fullGoal_mono (h : FullGoal) {env : World → Env} (le : ∀ w, Env.Le (env w) (WorldStep w))
    (r11Of : Core → Silmaril.X86.Word) :
    SatisfiesRel (x86Machine r11Of) env (Init Binary.Image.image) FullDom ∧
      ∀ w, FullDom w → ∃ N, LiveRel (x86Machine r11Of) env (Init Binary.Image.image) (· = w)
        fun _ => N := by
  obtain ⟨hs, hl⟩ := h r11Of
  refine ⟨hs.mono le, fun w hw => ?_⟩
  obtain ⟨N, hN⟩ := hl w hw
  exact ⟨N, hN.mono le⟩

end Silmaril.Apps.Sha256sum.Plan

module

public import Silmaril.Problems.Basic
public import Silmaril.Problems.Compose
public import Silmaril.Process.LPS.Problems.GnuSha256sum.SysBridge
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Fetchable
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Launch
public import Silmaril.Process.LPS.Problems.Sha256Cli.Registry

/-! # GNU `sha256sum` as problems

Problems in the family `sha256` about the pinned ELF `sha256sum-min`
(`GnuSha256sum.elfBytes`, 35512 bytes, SHA-256 `22fa6345…d42817`);
`problems/sha256/gnu-sha256sum-x86-64/` holds their `problem.toml` files.

* `…/lps-total`: total correctness in LPS on the stdin tier (`TotalGoal`). Open; linked from
  `sys-total` and `lps-bridge` by `lpsTotal_link` (VERIFIED).
* `…/lps-bounded-1024`, `…/lps-partial`: the weaker tiers, linked from `lps-total` (VERIFIED).
* `…/sys-total`: the middle statement over `X86Sys` (`SysTotalOn`). Open; it splits into five
  segments with parametric cut points (`sysTotalOn_of_segments`, VERIFIED).
* `…/lps-bridge`: the simulation obligation from `X86Sys` to LPS (`SimulationObligation`).
  **Solved**: `lpsBridge_solution` (`GnuSha256sum.simulationObligation`: the launch
  correspondence, `read(0)`/`write(1)`/`close`/`exit_group` and the instruction level).
* `…/agree-sha256-cli`: composition with the solved `sha256` filter problems: on the same
  stdin, every exiting complete run of GNU `sha256sum` writes exactly what the filter writes
  with its final `"\n"` replaced by `"  -\n"` (`Sha256Cli.gnu_stdout`). Linked from
  `gnu lps-total` and `sha256-cli lps-total` by `agree_link` (VERIFIED), so it is solved
  once `lps-total` is.
* `…/profile-total` (`GnuSha256sum.Profile`): the stdin tier as `ProfileProblem` statements in
  the parity format (`Parity.problem`), linked from `lps-total` by
  `Parity.profileTotal_link` (VERIFIED).

Status: every theorem in this file is VERIFIED (no `sorry`, no new axiom); `lps-bridge` is
solved; `lps-total`, `lps-bounded-1024`, `lps-partial`, `sys-total`, `agree-sha256-cli` and
`profile-total` are solved in `GnuSha256sum.Close`, and each follows from `sys-total` alone
(`lpsTotal_of_sysTotal`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum.Registry

open Silmaril.Problems
open Silmaril.Process.LPS

/-- The pinned binary's bytes. -/
abbrev elf : List Byte := GnuSha256sum.elfBytes

/-- Total correctness of `sha256sum-min` in LPS on the stdin tier. -/
@[problem "sha256/gnu-sha256sum-x86-64/lps-total"]
def lpsTotal : Prop := TotalGoal

/-- Total correctness in LPS on stdin of at most 1024 bytes. -/
@[problem "sha256/gnu-sha256sum-x86-64/lps-bounded-1024"]
def lpsBounded : Prop := BoundedGoal 1024

/-- Partial correctness (safety) in LPS on the stdin tier. -/
@[problem "sha256/gnu-sha256sum-x86-64/lps-partial"]
def lpsPartial : Prop := PartialGoal

/-- Total correctness over the `X86Sys` middle model on the stdin tier. -/
@[problem "sha256/gnu-sha256sum-x86-64/sys-total"]
def sysTotal : Prop := SysTotalOn fun _ => True

/-- The simulation of LPS by the middle model at every admissible launch. -/
@[problem "sha256/gnu-sha256sum-x86-64/lps-bridge"]
def lpsBridge : Prop := SimulationObligation

/-- GNU `sha256sum` and the `sha256` filter agree: on the same stdin, the bytes an exiting
complete run of `sha256sum-min` writes are those an exiting complete run of the filter writes,
with the final `"\n"` replaced by `"  -\n"`. -/
@[problem "sha256/gnu-sha256sum-x86-64/agree-sha256-cli"]
def agree : Prop :=
  ∀ (oracle : Nat → Machines.X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en en' : ExecEntry) (inp inp' : ProcInput) (message out out' : List Byte)
    (fs fs' : Fs.FileSystem),
    GnuSha256sum.Admissible oracle en inp message →
    Sha256Cli.Admissible oracle en' inp' message →
    (GnuSha256sum.behaviour oracle refusals limit en inp).traces
      (message.map (Event.readEv 0) ++ out.map (Event.writeEv 1) ++ [Event.exitEv 0 fs]) →
    (Sha256Cli.behaviour oracle refusals limit en' inp').traces
      (message.map (Event.readEv 0) ++ out'.map (Event.writeEv 1) ++ [Event.exitEv 0 fs']) →
    out = out'.dropLast ++ [0x20, 0x20, 0x2d, 0x0a]

/-! ## Links (VERIFIED) -/

theorem lpsTotal_link : All [sysTotal, lpsBridge] → lpsTotal := fun ⟨sys, bridge, _⟩ =>
  totalGoal_of_sys_simulation sys bridge

theorem lpsBounded_link : All [lpsTotal] → lpsBounded := fun ⟨total, _⟩ =>
  boundedGoal_of_totalGoal total 1024

theorem lpsPartial_link : All [lpsTotal] → lpsPartial := fun ⟨total, _⟩ =>
  partialGoal_of_totalGoal total

/-- A trace that reads `message`, writes `O` and exits, and is a prefix of a trace that reads
`message`, writes `E` and exits, writes exactly `E`. -/
theorem written_of_prefix {message O E : List Byte} {x x' : Event}
    (exitX : ∀ ch b, x ≠ Event.writeEv ch b) (exitX' : ∀ ch b, x' ≠ Event.writeEv ch b)
    (pre : message.map (Event.readEv 0) ++ O.map (Event.writeEv 1) ++ [x] <+:
      message.map (Event.readEv 0) ++ E.map (Event.writeEv 1) ++ [x']) : O = E := by
  simp only [List.append_assoc] at pre
  have pre' := (List.prefix_append_right_inj _).mp pre
  clear pre
  induction O generalizing E with
  | nil =>
    cases E with
    | nil => rfl
    | cons e es =>
      obtain ⟨rest, h⟩ := pre'
      simp only [List.map_nil, List.nil_append, List.map_cons, List.cons_append,
        List.cons.injEq] at h
      exact absurd h.1 (exitX _ _)
  | cons o os ih =>
    cases E with
    | nil =>
      obtain ⟨rest, h⟩ := pre'
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.cons.injEq] at h
      exact absurd h.1.symm (exitX' _ _)
    | cons e es =>
      simp only [List.map_cons, List.cons_append] at pre'
      have head := (List.cons_prefix_cons.mp pre').1
      have tail := (List.cons_prefix_cons.mp pre').2
      simp only [Event.writeEv.injEq, true_and] at head
      rw [head, ih tail]

theorem agree_link : All [lpsTotal, Sha256Cli.Registry.lpsTotal] → agree := by
  rintro ⟨gnu, cli, _⟩ oracle refusals limit en en' inp inp' message out out' fs fs'
    adm adm' run run'
  have pre := (gnu oracle refusals limit en inp message trivial adm).safety.safe _ run
  have pre' := (cli oracle refusals limit en' inp' message trivial adm').safety.safe _ run'
  have notWrite : ∀ (fs : Fs.FileSystem) ch b, Event.exitEv 0 fs ≠ Event.writeEv ch b := by
    intro _ _ _ h; cases h
  have gnuOut : out = expected message :=
    written_of_prefix (notWrite fs) (notWrite inp.fs) pre
  have cliOut : out' = CLI.Sha256.expected message :=
    written_of_prefix (notWrite fs') (notWrite inp'.fs) pre'
  rw [gnuOut, cliOut, expected_eq_filter]

/-- `agree` modulo the GNU `lps-total`, through the solved filter problem (VERIFIED). -/
theorem agree_of_lpsTotal (total : lpsTotal) : agree :=
  compose (components := [lpsTotal, Sha256Cli.Registry.lpsTotal])
    ⟨total, Sha256Cli.Registry.lpsTotal_solution, trivial⟩ agree_link

/-- `lps-total` modulo its two components (VERIFIED). -/
theorem lpsTotal_of (sys : sysTotal) (bridge : lpsBridge) : lpsTotal :=
  compose (components := [sysTotal, lpsBridge]) ⟨sys, bridge, trivial⟩ lpsTotal_link

/-- **`lps-bridge` (VERIFIED).** -/
@[solves "sha256/gnu-sha256sum-x86-64/lps-bridge"]
theorem lpsBridge_solution : lpsBridge := simulationObligation

/-- `lps-total` modulo `sys-total` alone (VERIFIED). -/
theorem lpsTotal_of_sysTotal (sys : sysTotal) : lpsTotal := lpsTotal_of sys lpsBridge_solution

/-! ## Non-vacuity (VERIFIED) -/

/-- The hypotheses of the LPS problems hold on every message, for every flag oracle. -/
theorem lps_hypotheses (oracle : Nat → Machines.X86FlagChoices.Choice) (message : List Byte) :
    ∃ en inp, Admissible oracle en inp message :=
  admissible oracle message

/-- The hypotheses of `sys-total` are not contradictory with its conclusion's shape: `Ok`
holds at the empty history of any running, unfaulted process. -/
theorem ok_nil (message : List Byte) (g : GS) (running : g.exited = none)
    (unfaulted : g.x.faulted = false) : Ok message g [] :=
  ⟨running, by simp, by simp [stdinRead], by simp [out], .inl rfl, unfaulted⟩

end Silmaril.Process.LPS.Problems.GnuSha256sum.Registry

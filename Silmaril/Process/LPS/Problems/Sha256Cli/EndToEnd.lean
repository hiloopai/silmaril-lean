module

public import Silmaril.Process.LPS.Problems.Sha256Cli.LoopSegment
public import Silmaril.Process.LPS.Problems.Sha256Cli.Tail
public import Silmaril.Process.LPS.Problems.Sha256Cli.OutputSegment
public import Silmaril.Process.LPS.Problems.Sha256Cli.Launch

/-! # The `sha256` filter end to end: assembly of the four segments

* `cli_total` (VERIFIED): the CLI-level end-to-end theorem. From every CLI launch of the
  chain's image, under every read partition and write split the reliable environment allows,
  every run keeps `Ok`, always progresses, and ends in `Done` (exit 0 with stdout exactly
  `hex(SHA-256(stdin)) ++ "\n"`). It composes `LoopProof.loop_segment_proof`,
  `Tail.tail_segment_proved` and `output_segment_proved`.
* `sha256cli_lps_total` (VERIFIED): the LPS target `TotalGoal`. The bridge is
  `bridge_of_readSim` with the read obligations of `ReadSim.lean` and the launch
  correspondence `Launch.launchObligation` (every admissible LPS launch of the pinned ELF is
  related, under the descriptor relation `StdRel`, to a CLI `Launch` of the chain's image).
  Instructions, `read`, `write` and `exit` are simulated (`Instr`, `ReadStep`/`ReadSim`,
  `WriteStep`, `Syscalls`).
* The weaker tiers follow the same way.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

/-- The three CLI segments, all proved. -/
theorem loop_segment : LoopSegment fun _ => True := LoopProof.loop_segment_proof
theorem tail_segment : TailSegment fun _ => True := Tail.tail_segment_proved
theorem output_segment : OutputSegment fun _ => True := output_segment_proved

/-- **CLI end to end (VERIFIED).** -/
theorem cli_total : CliTotalOn fun _ => True :=
  cliTotalOn_of_segments loop_segment tail_segment output_segment

/-- The CLI end-to-end theorem on any domain. -/
theorem cli_totalOn (domain : List Byte → Prop) : CliTotalOn domain :=
  fun message input x _ stdin valid launch => cli_total message input x trivial stdin valid launch

/-- The open remainder of the bridge segment: for every admissible LPS launch, a CLI launch
aligned with it and a descriptor relation under which the stdin `read` is simulated. -/
def ReadSimObligation : Prop :=
  ∀ oracle refusals limit en inp message, Admissible oracle en inp message →
    ReadSimAt oracle refusals limit en inp message

/-- The bridge segment, modulo `ReadSimObligation` (VERIFIED as an implication). -/
theorem bridge_segment_of_readSim (h : ReadSimObligation) : BridgeSegment :=
  bridge_of_readSim h

/-- `ReadSimObligation` reduces to the launch (VERIFIED as an implication). -/
theorem readSimObligation_of_launch (h : LaunchObligation) : ReadSimObligation :=
  readSim_of_launch h

/-- **The LPS end-to-end target, modulo `LaunchObligation`** (VERIFIED as an implication). -/
theorem sha256cli_lps_total_of_launch (h : LaunchObligation) : TotalGoal :=
  totalGoal_of_segments loop_segment tail_segment output_segment
    (bridge_segment_of_readSim (readSimObligation_of_launch h))

/-- **The LPS end-to-end target, modulo `ReadSimObligation`** (VERIFIED as an implication). -/
theorem sha256cli_lps_total_of_readSim (h : ReadSimObligation) : TotalGoal :=
  totalGoal_of_segments loop_segment tail_segment output_segment (bridge_segment_of_readSim h)

/-- Bounded tier, modulo `ReadSimObligation`. -/
theorem sha256cli_lps_bounded_of_readSim (h : ReadSimObligation) (n : Nat) : BoundedGoal n :=
  boundedGoal_of_totalGoal (sha256cli_lps_total_of_readSim h) n

/-- Partial tier, modulo `ReadSimObligation`. -/
theorem sha256cli_lps_partial_of_readSim (h : ReadSimObligation) : PartialGoal :=
  partialGoal_of_totalGoal (sha256cli_lps_total_of_readSim h)

/-- **The LPS end-to-end theorem (VERIFIED).** Total correctness of the pinned ELF in LPS on
every finite stdin, for every flag oracle, refusal configuration and budget. -/
theorem sha256cli_lps_total : TotalGoal :=
  sha256cli_lps_total_of_launch launchObligation

/-- Bounded tier (VERIFIED). -/
theorem sha256cli_lps_bounded (n : Nat) : BoundedGoal n :=
  boundedGoal_of_totalGoal sha256cli_lps_total n

/-- Partial tier (VERIFIED). -/
theorem sha256cli_lps_partial : PartialGoal :=
  partialGoal_of_totalGoal sha256cli_lps_total

end Silmaril.Process.LPS.Problems.Sha256Cli

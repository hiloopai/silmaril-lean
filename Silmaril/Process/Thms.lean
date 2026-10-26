module

public import Silmaril.Process.Defs
public import Silmaril.Process.LPS.Checks.SoundReference
public import Silmaril.Process.LPS.Problems.Sha256Cli.EndToEnd
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Close

namespace Silmaril.Process

theorem lpsTranslatedArms_length : LPS.translatedArms.length = 90 :=
  LPS.translatedArms_length

theorem lpsSpecTable_complete : LPS.specTable.all (·.status == .translated) = true :=
  LPS.specTable_all_translated

theorem sha256Cli_total : LPS.Problems.Sha256Cli.TotalGoal :=
  LPS.Problems.Sha256Cli.sha256cli_lps_total

/-! ## GNU `sha256sum-min` (stdin tier)

The release theorems for the libc-free reimplementation of GNU coreutils 9.4
`sha256sum`, with no hypothesis. The statements are in
`LPS.Problems.GnuSha256sum.Registry` and `LPS.Problems.GnuSha256sum.Parity`. -/

/-- Total correctness over the `X86Sys` middle model on the stdin tier. -/
theorem gnuSha256sum_sysTotal : LPS.Problems.GnuSha256sum.Registry.sysTotal :=
  LPS.Problems.GnuSha256sum.Close.sysTotal_close

/-- Total correctness in LPS on the stdin tier: the GNU digest line of the input. -/
theorem gnuSha256sum_lpsTotal : LPS.Problems.GnuSha256sum.Registry.lpsTotal :=
  LPS.Problems.GnuSha256sum.Close.lpsTotal_close

/-- Total correctness in LPS on standard input of at most 1024 bytes. -/
theorem gnuSha256sum_lpsBounded : LPS.Problems.GnuSha256sum.Registry.lpsBounded :=
  LPS.Problems.GnuSha256sum.Close.lpsBounded_close

/-- Partial correctness (safety) in LPS on the stdin tier. -/
theorem gnuSha256sum_lpsPartial : LPS.Problems.GnuSha256sum.Registry.lpsPartial :=
  LPS.Problems.GnuSha256sum.Close.lpsPartial_close

/-- Agreement with `sha256-cli`: on the same standard input, `sha256sum-min` writes what
the filter writes, with its final `"\n"` replaced by `"  -\n"`. -/
theorem gnuSha256sum_agree : LPS.Problems.GnuSha256sum.Registry.agree :=
  LPS.Problems.GnuSha256sum.Close.agree_close

/-- The parity `ProfileProblem` statements. -/
theorem gnuSha256sum_profileTotal : LPS.Problems.GnuSha256sum.Parity.profileTotal :=
  LPS.Problems.GnuSha256sum.Close.profileTotal_close

end Silmaril.Process

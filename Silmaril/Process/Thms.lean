module

public import Silmaril.Process.Defs
public import Silmaril.Process.LPS.Checks.SoundReference
public import Silmaril.Process.LPS.Problems.Sha256Cli.EndToEnd

namespace Silmaril.Process

theorem lpsTranslatedArms_length : LPS.translatedArms.length = 90 :=
  LPS.translatedArms_length

theorem lpsSpecTable_complete : LPS.specTable.all (·.status == .translated) = true :=
  LPS.specTable_all_translated

theorem sha256Cli_total : LPS.Problems.Sha256Cli.TotalGoal :=
  LPS.Problems.Sha256Cli.sha256cli_lps_total

end Silmaril.Process

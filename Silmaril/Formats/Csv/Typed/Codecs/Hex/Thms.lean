module

public import Silmaril.Formats.Csv.Typed.Codecs.Hex.Defs
import Silmaril.Proofs.Formats.Csv.Typed.Codecs.Hex.Correctness

public section

namespace Silmaril.Formats.Csv.Typed.Codecs.Hex

theorem parsePrint : codec.ParsePrint :=
  Proofs.Formats.Csv.Typed.Codecs.Hex.parsePrint

theorem printParse : codec.PrintParse :=
  Proofs.Formats.Csv.Typed.Codecs.Hex.printParse

end Silmaril.Formats.Csv.Typed.Codecs.Hex

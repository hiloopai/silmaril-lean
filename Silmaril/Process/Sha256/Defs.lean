module

public import Silmaril.Process.CLI.Sha256Cli.Binary
public import Silmaril.Process.LPS.Problems.Sha256Cli.Statement
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Statement
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Registry
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Profile

/-! The two SHA-256 programs and their LPS statements: the freestanding
`sha256-cli` filter and GNU `sha256sum-min` (`GnuSha256sum.Registry`,
`GnuSha256sum.Parity`). -/

namespace Silmaril.Process.Sha256
end Silmaril.Process.Sha256

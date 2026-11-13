module

public import Silmaril.Wasi.Versions.WitImport.KCert.Cli3.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:cli@0.3.2`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.cli3.envEq`, the worlds, `KC.cli3.pkg`,
`KC.cli3.valid`, `KC.cli3.unique`, `KC.cli3.elab` and `KC.cli3.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.cli3 env from versioned all [KF.v3.cli.environment, KF.v3.cli.exit, KF.v3.cli.run, KF.v3.cli.stdio, KF.v3.cli.terminal]
  "../../../../../../../specs/wasi/0.3.2/cli/environment.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/exit.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/run.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/terminal.wit"

wit_kcert KC.cli3 world from versioned all [KF.v3.cli.environment, KF.v3.cli.exit, KF.v3.cli.run, KF.v3.cli.stdio, KF.v3.cli.terminal]
  "../../../../../../../specs/wasi/0.3.2/cli/environment.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/exit.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/run.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/terminal.wit"

wit_kcert KC.cli3 final from versioned all [KF.v3.cli.environment, KF.v3.cli.exit, KF.v3.cli.run, KF.v3.cli.stdio, KF.v3.cli.terminal]
  "../../../../../../../specs/wasi/0.3.2/cli/environment.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/exit.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/run.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/terminal.wit"

end Silmaril.Wasi.Versions.WitImport

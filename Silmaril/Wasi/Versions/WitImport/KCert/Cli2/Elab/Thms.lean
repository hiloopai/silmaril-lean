module

public import Silmaril.Wasi.Versions.WitImport.KCert.Cli2.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:cli@0.2.12`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.cli2.envEq`, the worlds, `KC.cli2.pkg`,
`KC.cli2.valid`, `KC.cli2.unique`, `KC.cli2.elab` and `KC.cli2.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.cli2 env from unversioned all [KF.v2.cli.environment, KF.v2.cli.exit, KF.v2.cli.run, KF.v2.cli.stdio, KF.v2.cli.terminal, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/cli/environment.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/exit.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/run.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/terminal.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.cli2 world from unversioned all [KF.v2.cli.environment, KF.v2.cli.exit, KF.v2.cli.run, KF.v2.cli.stdio, KF.v2.cli.terminal, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/cli/environment.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/exit.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/run.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/terminal.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.cli2 final from unversioned all [KF.v2.cli.environment, KF.v2.cli.exit, KF.v2.cli.run, KF.v2.cli.stdio, KF.v2.cli.terminal, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/cli/environment.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/exit.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/run.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/terminal.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport

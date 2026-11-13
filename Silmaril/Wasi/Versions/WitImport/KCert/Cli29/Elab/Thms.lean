module

public import Silmaril.Wasi.Versions.WitImport.KCert.Cli29.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:cli@0.2.9`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.cli29.envEq`, the worlds, `KC.cli29.pkg`,
`KC.cli29.valid`, `KC.cli29.unique`, `KC.cli29.elab` and `KC.cli29.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.cli29 env from unversioned all [KF.v29.cli.environment, KF.v29.cli.exit, KF.v29.cli.run, KF.v29.cli.stdio, KF.v29.cli.terminal, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/cli/environment.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/exit.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/run.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/stdio.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/terminal.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.cli29 world from unversioned all [KF.v29.cli.environment, KF.v29.cli.exit, KF.v29.cli.run, KF.v29.cli.stdio, KF.v29.cli.terminal, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/cli/environment.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/exit.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/run.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/stdio.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/terminal.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.cli29 final from unversioned all [KF.v29.cli.environment, KF.v29.cli.exit, KF.v29.cli.run, KF.v29.cli.stdio, KF.v29.cli.terminal, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/cli/environment.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/exit.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/run.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/stdio.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/terminal.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport

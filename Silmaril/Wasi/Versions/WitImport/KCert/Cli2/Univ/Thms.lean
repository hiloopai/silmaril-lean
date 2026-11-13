module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Cli.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Io.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:cli@0.2.12`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.cli2.U` and `KC.cli2.univ`, its validity `KC.cli2.check`, and one `Elab.elabBody`
equation per interface (`KC.cli2.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.cli2 univ from unversioned all [KF.v2.cli.environment, KF.v2.cli.exit, KF.v2.cli.run, KF.v2.cli.stdio, KF.v2.cli.terminal, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/cli/environment.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/exit.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/run.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/terminal.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.cli2 check from unversioned all [KF.v2.cli.environment, KF.v2.cli.exit, KF.v2.cli.run, KF.v2.cli.stdio, KF.v2.cli.terminal, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/cli/environment.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/exit.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/run.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/terminal.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.cli2 body from unversioned all [KF.v2.cli.environment, KF.v2.cli.exit, KF.v2.cli.run, KF.v2.cli.stdio, KF.v2.cli.terminal, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/cli/environment.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/exit.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/run.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.2.12/cli/terminal.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport

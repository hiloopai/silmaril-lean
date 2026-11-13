module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V29Cli.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V29Io.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:cli@0.2.9`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.cli29.U` and `KC.cli29.univ`, its validity `KC.cli29.check`, and one `Elab.elabBody`
equation per interface (`KC.cli29.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.cli29 univ from unversioned all [KF.v29.cli.environment, KF.v29.cli.exit, KF.v29.cli.run, KF.v29.cli.stdio, KF.v29.cli.terminal, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/cli/environment.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/exit.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/run.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/stdio.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/terminal.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.cli29 check from unversioned all [KF.v29.cli.environment, KF.v29.cli.exit, KF.v29.cli.run, KF.v29.cli.stdio, KF.v29.cli.terminal, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/cli/environment.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/exit.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/run.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/stdio.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/terminal.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.cli29 body from unversioned all [KF.v29.cli.environment, KF.v29.cli.exit, KF.v29.cli.run, KF.v29.cli.stdio, KF.v29.cli.terminal, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/cli/environment.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/exit.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/run.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/stdio.wit"
  "../../../../../../../specs/wasi/v0.2.9/cli/terminal.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport

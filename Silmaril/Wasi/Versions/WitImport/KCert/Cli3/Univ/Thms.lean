module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V3Cli.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:cli@0.3.2`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.cli3.U` and `KC.cli3.univ`, its validity `KC.cli3.check`, and one `Elab.elabBody`
equation per interface (`KC.cli3.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.cli3 univ from versioned all [KF.v3.cli.environment, KF.v3.cli.exit, KF.v3.cli.run, KF.v3.cli.stdio, KF.v3.cli.terminal]
  "../../../../../../../specs/wasi/0.3.2/cli/environment.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/exit.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/run.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/terminal.wit"

wit_kcert KC.cli3 check from versioned all [KF.v3.cli.environment, KF.v3.cli.exit, KF.v3.cli.run, KF.v3.cli.stdio, KF.v3.cli.terminal]
  "../../../../../../../specs/wasi/0.3.2/cli/environment.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/exit.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/run.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/terminal.wit"

wit_kcert KC.cli3 body from versioned all [KF.v3.cli.environment, KF.v3.cli.exit, KF.v3.cli.run, KF.v3.cli.stdio, KF.v3.cli.terminal]
  "../../../../../../../specs/wasi/0.3.2/cli/environment.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/exit.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/run.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/stdio.wit"
  "../../../../../../../specs/wasi/0.3.2/cli/terminal.wit"

end Silmaril.Wasi.Versions.WitImport

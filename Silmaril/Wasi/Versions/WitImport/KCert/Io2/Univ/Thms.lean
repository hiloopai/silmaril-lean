module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Io.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:io@0.2.12`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.io2.U` and `KC.io2.univ`, its validity `KC.io2.check`, and one `Elab.elabBody`
equation per interface (`KC.io2.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.io2 univ from unversioned all [KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.io2 check from unversioned all [KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.io2 body from unversioned all [KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport

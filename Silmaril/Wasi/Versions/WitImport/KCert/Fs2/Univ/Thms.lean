module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Fs.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Io.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:filesystem@0.2.12`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.fs2.U` and `KC.fs2.univ`, its validity `KC.fs2.check`, and one `Elab.elabBody`
equation per interface (`KC.fs2.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.fs2 univ from unversioned all [KF.v2.fs.types, KF.v2.fs.preopens, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.2.12/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.fs2 check from unversioned all [KF.v2.fs.types, KF.v2.fs.preopens, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.2.12/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.fs2 body from unversioned all [KF.v2.fs.types, KF.v2.fs.preopens, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.2.12/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport

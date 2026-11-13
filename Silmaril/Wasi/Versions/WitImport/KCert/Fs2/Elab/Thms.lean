module

public import Silmaril.Wasi.Versions.WitImport.KCert.Fs2.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:filesystem@0.2.12`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.fs2.envEq`, the worlds, `KC.fs2.pkg`,
`KC.fs2.valid`, `KC.fs2.unique`, `KC.fs2.elab` and `KC.fs2.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.fs2 env from unversioned all [KF.v2.fs.types, KF.v2.fs.preopens, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.2.12/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.fs2 world from unversioned all [KF.v2.fs.types, KF.v2.fs.preopens, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.2.12/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

wit_kcert KC.fs2 final from unversioned all [KF.v2.fs.types, KF.v2.fs.preopens, KF.v2.clocks.monotonic_clock, KF.v2.clocks.wall_clock, KF.v2.clocks.timezone, KF.v2.io.error, KF.v2.io.poll, KF.v2.io.streams]
  "../../../../../../../specs/wasi/0.2.12/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.2.12/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/0.2.12/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.2.12/io/error.wit"
  "../../../../../../../specs/wasi/0.2.12/io/poll.wit"
  "../../../../../../../specs/wasi/0.2.12/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport

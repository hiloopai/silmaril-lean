module

public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks29.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:clocks@0.2.9`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.clocks29.envEq`, the worlds, `KC.clocks29.pkg`,
`KC.clocks29.valid`, `KC.clocks29.unique`, `KC.clocks29.elab` and `KC.clocks29.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.clocks29 env from unversioned all [KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.clocks29 world from unversioned all [KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.clocks29 final from unversioned all [KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport

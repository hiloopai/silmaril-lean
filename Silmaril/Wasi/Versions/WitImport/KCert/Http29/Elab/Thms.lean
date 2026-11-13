module

public import Silmaril.Wasi.Versions.WitImport.KCert.Http29.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:http@0.2.9`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.http29.envEq`, the worlds, `KC.http29.pkg`,
`KC.http29.valid`, `KC.http29.unique`, `KC.http29.elab` and `KC.http29.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.http29 env from unversioned all [KF.v29.http.types, KF.v29.http.handler, KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/http/types.wit"
  "../../../../../../../specs/wasi/v0.2.9/http/handler.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.http29 world from unversioned all [KF.v29.http.types, KF.v29.http.handler, KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/http/types.wit"
  "../../../../../../../specs/wasi/v0.2.9/http/handler.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.http29 final from unversioned all [KF.v29.http.types, KF.v29.http.handler, KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/http/types.wit"
  "../../../../../../../specs/wasi/v0.2.9/http/handler.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport

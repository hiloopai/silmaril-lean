module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V29Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V29Io.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:clocks@0.2.9`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.clocks29.U` and `KC.clocks29.univ`, its validity `KC.clocks29.check`, and one `Elab.elabBody`
equation per interface (`KC.clocks29.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.clocks29 univ from unversioned all [KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.clocks29 check from unversioned all [KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

wit_kcert KC.clocks29 body from unversioned all [KF.v29.clocks.monotonic_clock, KF.v29.clocks.wall_clock, KF.v29.clocks.timezone, KF.v29.io.error, KF.v29.io.poll, KF.v29.io.streams]
  "../../../../../../../specs/wasi/v0.2.9/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/wall-clock.wit"
  "../../../../../../../specs/wasi/v0.2.9/clocks/timezone.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/error.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/poll.wit"
  "../../../../../../../specs/wasi/v0.2.9/io/streams.wit"

end Silmaril.Wasi.Versions.WitImport

module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V3Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V3Http.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:http@0.3.2`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.http3.U` and `KC.http3.univ`, its validity `KC.http3.check`, and one `Elab.elabBody`
equation per interface (`KC.http3.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.http3 univ from versioned ifaces [KF.v3.http.worlds, KF.v3.http.types, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/http/worlds.wit"
  "../../../../../../../specs/wasi/0.3.2/http/types.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

wit_kcert KC.http3 check from versioned ifaces [KF.v3.http.worlds, KF.v3.http.types, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/http/worlds.wit"
  "../../../../../../../specs/wasi/0.3.2/http/types.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

wit_kcert KC.http3 body from versioned ifaces [KF.v3.http.worlds, KF.v3.http.types, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/http/worlds.wit"
  "../../../../../../../specs/wasi/0.3.2/http/types.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

end Silmaril.Wasi.Versions.WitImport

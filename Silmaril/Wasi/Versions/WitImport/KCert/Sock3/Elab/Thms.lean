module

public import Silmaril.Wasi.Versions.WitImport.KCert.Sock3.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:sockets@0.3.2`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.sock3.envEq`, the worlds, `KC.sock3.pkg`,
`KC.sock3.valid`, `KC.sock3.unique`, `KC.sock3.elab` and `KC.sock3.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.sock3 env from versioned all [KF.v3.sock.types, KF.v3.sock.ip_name_lookup, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/sockets/types.wit"
  "../../../../../../../specs/wasi/0.3.2/sockets/ip-name-lookup.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

wit_kcert KC.sock3 world from versioned all [KF.v3.sock.types, KF.v3.sock.ip_name_lookup, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/sockets/types.wit"
  "../../../../../../../specs/wasi/0.3.2/sockets/ip-name-lookup.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

wit_kcert KC.sock3 final from versioned all [KF.v3.sock.types, KF.v3.sock.ip_name_lookup, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/sockets/types.wit"
  "../../../../../../../specs/wasi/0.3.2/sockets/ip-name-lookup.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

end Silmaril.Wasi.Versions.WitImport

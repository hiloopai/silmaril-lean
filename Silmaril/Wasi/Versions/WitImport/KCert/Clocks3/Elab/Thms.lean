module

public import Silmaril.Wasi.Versions.WitImport.KCert.Clocks3.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:clocks@0.3.2`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.clocks3.envEq`, the worlds, `KC.clocks3.pkg`,
`KC.clocks3.valid`, `KC.clocks3.unique`, `KC.clocks3.elab` and `KC.clocks3.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.clocks3 env from versioned all [KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

wit_kcert KC.clocks3 world from versioned all [KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

wit_kcert KC.clocks3 final from versioned all [KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

end Silmaril.Wasi.Versions.WitImport

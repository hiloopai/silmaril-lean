module

public import Silmaril.Wasi.Versions.WitImport.KCert.Fs3.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:filesystem@0.3.2`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.fs3.envEq`, the worlds, `KC.fs3.pkg`,
`KC.fs3.valid`, `KC.fs3.unique`, `KC.fs3.elab` and `KC.fs3.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.fs3 env from versioned all [KF.v3.fs.types, KF.v3.fs.preopens, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.3.2/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

wit_kcert KC.fs3 world from versioned all [KF.v3.fs.types, KF.v3.fs.preopens, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.3.2/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

wit_kcert KC.fs3 final from versioned all [KF.v3.fs.types, KF.v3.fs.preopens, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.3.2/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

end Silmaril.Wasi.Versions.WitImport

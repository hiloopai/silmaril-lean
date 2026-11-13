module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V3Clocks.Thms
public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V3Fs.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:filesystem@0.3.2`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.fs3.U` and `KC.fs3.univ`, its validity `KC.fs3.check`, and one `Elab.elabBody`
equation per interface (`KC.fs3.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.fs3 univ from versioned all [KF.v3.fs.types, KF.v3.fs.preopens, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.3.2/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

wit_kcert KC.fs3 check from versioned all [KF.v3.fs.types, KF.v3.fs.preopens, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.3.2/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

wit_kcert KC.fs3 body from versioned all [KF.v3.fs.types, KF.v3.fs.preopens, KF.v3.clocks.monotonic_clock, KF.v3.clocks.system_clock, KF.v3.clocks.timezone, KF.v3.clocks.types]
  "../../../../../../../specs/wasi/0.3.2/filesystem/types.wit"
  "../../../../../../../specs/wasi/0.3.2/filesystem/preopens.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/monotonic-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/system-clock.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/timezone.wit"
  "../../../../../../../specs/wasi/0.3.2/clocks/types.wit"

end Silmaril.Wasi.Versions.WitImport

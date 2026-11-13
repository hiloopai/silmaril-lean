module

public import Silmaril.Wasi.Versions.WitImport.KCert.Rand29.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:random@0.2.9`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.rand29.envEq`, the worlds, `KC.rand29.pkg`,
`KC.rand29.valid`, `KC.rand29.unique`, `KC.rand29.elab` and `KC.rand29.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.rand29 env from unversioned all [KF.v29.rand.insecure_seed, KF.v29.rand.insecure, KF.v29.rand.random]
  "../../../../../../../specs/wasi/v0.2.9/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/insecure.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/random.wit"

wit_kcert KC.rand29 world from unversioned all [KF.v29.rand.insecure_seed, KF.v29.rand.insecure, KF.v29.rand.random]
  "../../../../../../../specs/wasi/v0.2.9/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/insecure.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/random.wit"

wit_kcert KC.rand29 final from unversioned all [KF.v29.rand.insecure_seed, KF.v29.rand.insecure, KF.v29.rand.random]
  "../../../../../../../specs/wasi/v0.2.9/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/insecure.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/random.wit"

end Silmaril.Wasi.Versions.WitImport

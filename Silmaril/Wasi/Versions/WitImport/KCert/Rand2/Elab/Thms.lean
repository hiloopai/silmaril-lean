module

public import Silmaril.Wasi.Versions.WitImport.KCert.Rand2.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:random@0.2.12`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.rand2.envEq`, the worlds, `KC.rand2.pkg`,
`KC.rand2.valid`, `KC.rand2.unique`, `KC.rand2.elab` and `KC.rand2.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.rand2 env from unversioned all [KF.v2.rand.insecure_seed, KF.v2.rand.insecure, KF.v2.rand.random]
  "../../../../../../../specs/wasi/0.2.12/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.2.12/random/insecure.wit"
  "../../../../../../../specs/wasi/0.2.12/random/random.wit"

wit_kcert KC.rand2 world from unversioned all [KF.v2.rand.insecure_seed, KF.v2.rand.insecure, KF.v2.rand.random]
  "../../../../../../../specs/wasi/0.2.12/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.2.12/random/insecure.wit"
  "../../../../../../../specs/wasi/0.2.12/random/random.wit"

wit_kcert KC.rand2 final from unversioned all [KF.v2.rand.insecure_seed, KF.v2.rand.insecure, KF.v2.rand.random]
  "../../../../../../../specs/wasi/0.2.12/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.2.12/random/insecure.wit"
  "../../../../../../../specs/wasi/0.2.12/random/random.wit"

end Silmaril.Wasi.Versions.WitImport

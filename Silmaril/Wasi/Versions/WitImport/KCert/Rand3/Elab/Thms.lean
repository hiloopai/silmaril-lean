module

public import Silmaril.Wasi.Versions.WitImport.KCert.Rand3.Univ.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:random@0.3.2`: environment, worlds and package

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`): `KC.rand3.envEq`, the worlds, `KC.rand3.pkg`,
`KC.rand3.valid`, `KC.rand3.unique`, `KC.rand3.elab` and `KC.rand3.importKD`, the kernel importer `importKD` on the
files without doc comments.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.rand3 env from versioned all [KF.v3.rand.insecure_seed, KF.v3.rand.insecure, KF.v3.rand.random]
  "../../../../../../../specs/wasi/0.3.2/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.3.2/random/insecure.wit"
  "../../../../../../../specs/wasi/0.3.2/random/random.wit"

wit_kcert KC.rand3 world from versioned all [KF.v3.rand.insecure_seed, KF.v3.rand.insecure, KF.v3.rand.random]
  "../../../../../../../specs/wasi/0.3.2/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.3.2/random/insecure.wit"
  "../../../../../../../specs/wasi/0.3.2/random/random.wit"

wit_kcert KC.rand3 final from versioned all [KF.v3.rand.insecure_seed, KF.v3.rand.insecure, KF.v3.rand.random]
  "../../../../../../../specs/wasi/0.3.2/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.3.2/random/insecure.wit"
  "../../../../../../../specs/wasi/0.3.2/random/random.wit"

end Silmaril.Wasi.Versions.WitImport

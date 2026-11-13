module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V3Rand.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:random@0.3.2`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.rand3.U` and `KC.rand3.univ`, its validity `KC.rand3.check`, and one `Elab.elabBody`
equation per interface (`KC.rand3.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.rand3 univ from versioned all [KF.v3.rand.insecure_seed, KF.v3.rand.insecure, KF.v3.rand.random]
  "../../../../../../../specs/wasi/0.3.2/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.3.2/random/insecure.wit"
  "../../../../../../../specs/wasi/0.3.2/random/random.wit"

wit_kcert KC.rand3 check from versioned all [KF.v3.rand.insecure_seed, KF.v3.rand.insecure, KF.v3.rand.random]
  "../../../../../../../specs/wasi/0.3.2/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.3.2/random/insecure.wit"
  "../../../../../../../specs/wasi/0.3.2/random/random.wit"

wit_kcert KC.rand3 body from versioned all [KF.v3.rand.insecure_seed, KF.v3.rand.insecure, KF.v3.rand.random]
  "../../../../../../../specs/wasi/0.3.2/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.3.2/random/insecure.wit"
  "../../../../../../../specs/wasi/0.3.2/random/random.wit"

end Silmaril.Wasi.Versions.WitImport

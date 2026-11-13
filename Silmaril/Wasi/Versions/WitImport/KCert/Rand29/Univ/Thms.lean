module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V29Rand.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:random@0.2.9`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.rand29.U` and `KC.rand29.univ`, its validity `KC.rand29.check`, and one `Elab.elabBody`
equation per interface (`KC.rand29.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.rand29 univ from unversioned all [KF.v29.rand.insecure_seed, KF.v29.rand.insecure, KF.v29.rand.random]
  "../../../../../../../specs/wasi/v0.2.9/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/insecure.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/random.wit"

wit_kcert KC.rand29 check from unversioned all [KF.v29.rand.insecure_seed, KF.v29.rand.insecure, KF.v29.rand.random]
  "../../../../../../../specs/wasi/v0.2.9/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/insecure.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/random.wit"

wit_kcert KC.rand29 body from unversioned all [KF.v29.rand.insecure_seed, KF.v29.rand.insecure, KF.v29.rand.random]
  "../../../../../../../specs/wasi/v0.2.9/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/insecure.wit"
  "../../../../../../../specs/wasi/v0.2.9/random/random.wit"

end Silmaril.Wasi.Versions.WitImport

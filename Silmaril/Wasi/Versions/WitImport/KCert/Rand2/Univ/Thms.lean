module

public import Silmaril.Wasi.Versions.WitImport.KCert.Files.V2Rand.Thms

@[expose] public section

/-!
# Kernel certificate for `wasi:random@0.2.12`: universe, check and interface bodies

`wit_kcert` (`Silmaril.Wasi.Versions.WitImport.KQuote`) on the files without doc comments: the
gated universe `KC.rand2.U` and `KC.rand2.univ`, its validity `KC.rand2.check`, and one `Elab.elabBody`
equation per interface (`KC.rand2.body<k>`), each checked by the kernel.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

wit_kcert KC.rand2 univ from unversioned all [KF.v2.rand.insecure_seed, KF.v2.rand.insecure, KF.v2.rand.random]
  "../../../../../../../specs/wasi/0.2.12/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.2.12/random/insecure.wit"
  "../../../../../../../specs/wasi/0.2.12/random/random.wit"

wit_kcert KC.rand2 check from unversioned all [KF.v2.rand.insecure_seed, KF.v2.rand.insecure, KF.v2.rand.random]
  "../../../../../../../specs/wasi/0.2.12/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.2.12/random/insecure.wit"
  "../../../../../../../specs/wasi/0.2.12/random/random.wit"

wit_kcert KC.rand2 body from unversioned all [KF.v2.rand.insecure_seed, KF.v2.rand.insecure, KF.v2.rand.random]
  "../../../../../../../specs/wasi/0.2.12/random/insecure-seed.wit"
  "../../../../../../../specs/wasi/0.2.12/random/insecure.wit"
  "../../../../../../../specs/wasi/0.2.12/random/random.wit"

end Silmaril.Wasi.Versions.WitImport

module

public import Silmaril.Wasm.Wac.Bridge.DecodeNamed.Defs

/-!
# WAC bridge: type items that name a resource by `ref`

In the named fragment `DecodeNamed.EsOk`, an alias type item of a resource `a` is
written `type n = own<a>` (`EsOk.tyOwn`), the form the decoder reads back. The
elaborator may also write it `type n = a`, that is `.type (.value (.ref a))`
with `a` a resource; the encoder writes both the same way (`(type (eq i))` of `a`'s
index), and the decoder reads it back as `own<a>`.

`fixR Γ es` rewrites, in the items `es` (not inside instances and components), every
type item `type n = ref a` whose `a` is a resource in the context (`Γ` extended by the
earlier items) to `type n = own<a>`. The theorems of `Bridge.DecodeRefRes.Thms` state
that the encoder writes `es` as it writes `fixR Γ es`, so `decodePkg` reads `es` back as
`dks (fixR Γ es)`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary

namespace DecodeRefRes

open DecodeNamed (Ctx extend)

/-- One item: a type item `ref a` of a resource `a` becomes `own<a>`. -/
def fixItem (Γ : Ctx) : String × Kind → String × Kind
  | (n, .type (.value (.ref r))) =>
    match Γ.lookup r.name with
    | some .res => (n, .type (.value (.own r)))
    | _ => (n, .type (.value (.ref r)))
  | x => x

/-- The items, each fixed in the context of the earlier (fixed) ones. -/
def fixR : Ctx → Externs → Externs
  | _, [] => []
  | Γ, x :: es => fixItem Γ x :: fixR (extend Γ [fixItem Γ x]) es

end DecodeRefRes

end Silmaril.Wasm.Wac.Bridge

module

public import Silmaril.Wasm.Wac.Bridge.DecodeNamed.Defs

/-!
# WAC bridge: value items

The named fragment `DecodeNamed.EsOk` has no value items (`(value …)` imports and
exports, `Kind.value t`). `EsOkV` is that fragment with value items over value types of
the fragment (`TyOk`), at every level: a package, an instance and a component may
import or export values. A value item declares no type name, so it leaves the context
unchanged, as a function does.

The theorems are in `Bridge.DecodeValue.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)

namespace DecodeValue

open DecodeNamed (Ctx TyOk SigOk NomOk Plain extend)

/-- **Items of the named fragment with value items.** -/
inductive EsOkV (N : NomTable) : Ctx → Externs → Prop
  | nil {Γ : Ctx} : EsOkV N Γ []
  | value {Γ : Ctx} {n : String} {t : Silmaril.Wasm.Wit.Binary.Ty} {es : Externs} :
      TyOk Γ t → EsOkV N Γ es → EsOkV N Γ ((n, .value t) :: es)
  | func {Γ : Ctx} {n : String} {s : Sig} {es : Externs} :
      SigOk Γ s → EsOkV N Γ es → EsOkV N Γ ((n, .func s) :: es)
  | inst {Γ : Ctx} {n : String} {i : Option String} {fs es : Externs} :
      EsOkV N [] fs → EsOkV N Γ es → EsOkV N Γ ((n, .inst i fs) :: es)
  | comp {Γ : Ctx} {n : String} {i : Option String} {is fs es : Externs} :
      EsOkV N [] is → EsOkV N (extend [] is) fs → EsOkV N Γ es → EsOkV N Γ ((n, .comp i is fs) :: es)
  | res {Γ : Ctx} {n : String} {es : Externs} :
      EsOkV N (Γ ++ [(n, .res)]) es → EsOkV N Γ ((n, .type (.resource n)) :: es)
  | tyOwn {Γ : Ctx} {n a : String} {es : Externs} : Γ.lookup a = some .res →
      EsOkV N (Γ ++ [(n, .ali a)]) es → EsOkV N Γ ((n, .type (.value (.own ⟨.local, a⟩))) :: es)
  | tyRef {Γ : Ctx} {n a : String} {es : Externs} : Γ.lookup a = some .val →
      EsOkV N (Γ ++ [(n, .val)]) es → EsOkV N Γ ((n, .type (.value (.ref ⟨.local, a⟩))) :: es)
  | tyNom {Γ : Ctx} {n : String} {d : Nominal} {es : Externs} : Γ.lookup n = none →
      N.lookup n = some d → NomOk Γ d →
      EsOkV N (Γ ++ [(n, .val)]) es → EsOkV N Γ ((n, .type (.value (.ref ⟨.local, n⟩))) :: es)
  | tyVal {Γ : Ctx} {n : String} {t : Silmaril.Wasm.Wit.Binary.Ty} {es : Externs} : Plain t → TyOk Γ t →
      EsOkV N (Γ ++ [(n, .val)]) es → EsOkV N Γ ((n, .type (.value t)) :: es)
  | tyFunc {Γ : Ctx} {n : String} {s : Sig} {es : Externs} : SigOk Γ s →
      EsOkV N (Γ ++ [(n, .other)]) es → EsOkV N Γ ((n, .type (.func s)) :: es)
  | tyInst {Γ : Ctx} {n : String} {i : Option String} {fs es : Externs} : EsOkV N [] fs →
      EsOkV N (Γ ++ [(n, .other)]) es → EsOkV N Γ ((n, .type (.inst i fs)) :: es)
  | tyComp {Γ : Ctx} {n : String} {i : Option String} {is fs es : Externs} : EsOkV N [] is →
      EsOkV N (extend [] is) fs → EsOkV N (Γ ++ [(n, .other)]) es →
      EsOkV N Γ ((n, .type (.comp i is fs)) :: es)

end DecodeValue

end Silmaril.Wasm.Wac.Bridge

module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.RuntimeBridge.Values

/-!
# The runtime bridge, layer 1: the closed types

`Wasm.Validation.DefType` and its siblings are `Ty k`, a dependent family
mirroring `deftype`/`rectype`/`subtype`/`comptype`/`typeuse`/`heaptype`/….

**The encoding already existed.**  `Equiv/Validation.lean` has `tyV` and
`tyV_inj` — the whole `Ty : TKind → Type` family encoded into `Sem.Value`, one
case per constructor, with the single induction proving injectivity.  So layer
1 is not a new recursion: it is `tyV` at `deftype` and `reftype`, plus the two
closed *external* types `CGlobalType` and `CTableType`, whose components are
source types that `Equiv/BinaryTypes.lean` already encodes.  `Ty.idx` is no
obstruction either — the pinned `typeuse` has its own `_IDX typeidx` case, so
open and closed type uses land in the same IL sort.

Layers 2 and 3 never inspect a type — the instance records only carry one
through — so they are written against the `ClosedTypes` interface below rather
than against this encoding.  That is what lets this file be built
independently, and it is what makes every downstream theorem say explicitly
whether its content depends on the type encoding.  For the `Step`/`Step_read`
rules that never look at a type, the answer is "not at all".
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.RuntimeBridge

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core

/-! ## Layer 1 — the closed types, as an interface

`Wasm.Validation.DefType` and its siblings are `Ty k`, a dependent family mirroring
`deftype`/`rectype`/`subtype`/`comptype`/`typeuse`/`heaptype`/….  Encoding it
is the largest single piece of this bridge, and **nothing in layers 2 and 3
inspects it** — the instance records only carry a type field through.

So layers 2 and 3 are written against an *interface*: a `ClosedTypes`
structure supplying the four encodings they need, with the round-trip laws.
That has two payoffs.  It lets layer 1 be built independently.  And it makes
every downstream theorem say explicitly which of its content depends on the
type encoding — for the `Step`/`Step_read` rules that never look at a type,
the answer is "none", exactly as `Equiv/Execution.lean` quantified over an
arbitrary `blocktype` in the rules that do not inspect one. -/

/-- The encodings of the closed types that the runtime records carry.  Layer 1
provides an instance of this; layers 2 and 3 only use it. -/
structure ClosedTypes where
  /-- `deftype`, carried by `taginst`, `funcinst`, `structinst`, `arrayinst`. -/
  defType : Wasm.Validation.DefType → Value
  /-- `globaltype`, carried by `globalinst`. -/
  globalType : Wasm.Validation.CGlobalType → Value
  /-- `tabletype`, carried by `tableinst`. -/
  tableType : Wasm.Validation.CTableType → Value
  /-- `elemtype`, carried by `eleminst`; the IL aliases it to `reftype`. -/
  elemType : Wasm.Validation.CRefType → Value
  /-- Each is injective, which is all layers 2–3 need of them. -/
  defType_inj : Function.Injective defType
  globalType_inj : Function.Injective globalType
  tableType_inj : Function.Injective tableType
  elemType_inj : Function.Injective elemType

/-! ## Layer 1 — discharging the obligation

The dependent family `Ty k` is *already* encoded, and already proved injective:
`Equiv/Validation.lean`'s `tyV` sends every sort of
`Silmaril/Wasm/Validation/DefTypes.lean` to the value of the matching pinned
sort, and `tyV_inj` is the single induction saying that the value determines
the type.  So layer 1 is not a new encoding — it is `tyV` at the two sorts the
runtime carries bare (`deftype` and `reftype`), plus the two closed *external*
types, which the pinned stream builds out of them with one injection each.

Reading the pinned stream (`specs/spectec/wasm-3.0.ast`) for the four sorts:

```
(typ "deftype"    (inst (variant (case "_DEF" (tup (bind "rectype" (var "rectype"))
                                                   (bind "n" (var "n")))))))
(typ "reftype"    (inst (variant (case "REF"  (tup (bind "null?" (iter (var "null") opt))
                                                   (bind "heaptype" (var "heaptype")))))))
(typ "elemtype"   (inst (alias (var "reftype"))))
(typ "globaltype" (inst (variant (case "%%"   (tup (bind "mut?" (iter (var "mut") opt))
                                                   (bind "valtype" (var "valtype")))))))
(typ "tabletype"  (inst (variant (case "%%%"  (tup (bind "addrtype" (var "addrtype"))
                                                   (bind "limits" (var "limits"))
                                                   (bind "reftype" (var "reftype")))))))
```

`deftype` and `elemtype` are therefore `tyV` verbatim — `elemtype` is a bare
alias of `reftype`, so the `eleminst` field carries a `reftype` value and
nothing wraps it.  `globaltype` and `tabletype` are the two `%`-mixop records,
whose *components* are the source sorts `mut?`, `addrtype` and `limits`, for
which `Equiv/BinaryTypes.lean` already has `Encode` instances; only the last
component of each is a closed type and so goes through `tyV`.

Note that `globaltype`/`tabletype` here have exactly the injections the *source*
`Wasm.GlobalType`/`Wasm.TableType` get in `Equiv/BinaryTypes.lean`
(`instEncodeGlobalType`, `instEncodeTableType`): the closed and the open
external types differ only in the sort of their last component, which is what
`CGlobalType`/`CTableType` were defined to express.

Nothing here has to be restricted.  In particular `Ty.idx`, the free type
index, is *not* an obstruction: the pinned `typeuse` has a `_IDX typeidx` case
of its own (it is the `typevar` subsort), so open and closed type uses alike
land in the same IL sort, and `tyV (.idx x) = (case "_IDX" (idxV x))`. -/

/-- `globaltype = mut? valtype` over *semantic* value types: the pinned `%%`
injection, with `tyV` on the value type. -/
def cGlobalTypeV (g : Wasm.Validation.CGlobalType) : Value :=
  .case "%%" (.tuple [Encode.toValue g.mutability, Equiv.Validation.tyV g.type])

/-- `tabletype = addrtype limits reftype` over *semantic* reference types: the
pinned `%%%` injection, with `tyV` on the element type. -/
def cTableTypeV (tt : Wasm.Validation.CTableType) : Value :=
  .case "%%%" (.tuple [Encode.toValue tt.address, Encode.toValue tt.limits,
    Equiv.Validation.tyV tt.element])

/-- The closed `globaltype` encoding is injective: `mut?` is injective because
it is an `Encode`, and the value type because of `tyV_inj`. -/
theorem cGlobalTypeV_inj : Function.Injective cGlobalTypeV := by
  rintro ⟨m₁, t₁⟩ ⟨m₂, t₂⟩ h
  simp only [cGlobalTypeV] at h
  injection h with _ h
  injection h with h
  injection h with hm h
  injection h with ht _
  rw [Encode.toValue_injective hm, Equiv.Validation.tyV_inj _ _ ht]

/-- The closed `tabletype` encoding is injective. -/
theorem cTableTypeV_inj : Function.Injective cTableTypeV := by
  rintro ⟨a₁, l₁, e₁⟩ ⟨a₂, l₂, e₂⟩ h
  simp only [cTableTypeV] at h
  injection h with _ h
  injection h with h
  injection h with ha h
  injection h with hl h
  injection h with he _
  rw [Encode.toValue_injective ha, Encode.toValue_injective hl,
    Equiv.Validation.tyV_inj _ _ he]

/-- **Layer 1's obligation, discharged.**  The pinned closed types do have such
an encoding: `Equiv/Validation.lean`'s `tyV` at `deftype` and `reftype`, and
the two external-type injections above. -/
def closedTypes : ClosedTypes where
  defType := Equiv.Validation.tyV
  globalType := cGlobalTypeV
  tableType := cTableTypeV
  elemType := Equiv.Validation.tyV
  defType_inj := by intro a b h; exact Equiv.Validation.tyV_inj a b h
  globalType_inj := cGlobalTypeV_inj
  tableType_inj := cTableTypeV_inj
  elemType_inj := by intro a b h; exact Equiv.Validation.tyV_inj a b h

@[simp] theorem closedTypes_defType (d : Wasm.Validation.DefType) :
    closedTypes.defType d = Equiv.Validation.tyV d := rfl

@[simp] theorem closedTypes_elemType (r : Wasm.Validation.CRefType) :
    closedTypes.elemType r = Equiv.Validation.tyV r := rfl

@[simp] theorem closedTypes_globalType (g : Wasm.Validation.CGlobalType) :
    closedTypes.globalType g = cGlobalTypeV g := rfl

@[simp] theorem closedTypes_tableType (tt : Wasm.Validation.CTableType) :
    closedTypes.tableType tt = cTableTypeV tt := rfl

end Silmaril.SpecTec.Equiv.RuntimeBridge

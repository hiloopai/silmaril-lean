module

public import Silmaril.Wasi.Versions.WitImport.Defs

@[expose] public section

/-!
# WIT typing with named types resolved

`tyOk` (`Silmaril.Wasi.Versions.WitImport`) accepts every value for a named type
(`Binary.Ty.ref`). This module resolves named types against the type definitions the importer
reads:

* `TyEnv`: for each interface (`Binary.IfaceName`) the kinds of its named types. It holds the
  interfaces of the imported package and those of its dependencies (the second component of
  `Elab.elaborate`).
* `RTable`: a signature table whose entries also name the interface of the function, so that
  a `.local` reference can be resolved. `strip R` forgets the interfaces; for the imported
  tables, `strip R` is the table of `Silmaril.Wasi.Versions.WitImport.Tables`
  (`Silmaril.Wasi.Versions.WitImport.RTables`).
* `findTy E cur r`: the definition of `r`, seen from the interface `cur`. A `.local` reference
  names a type of `cur`, an `.iface j` reference a type of `j`. A `use j.{t}` is the local kind
  `.type (.ref ⟨.iface j, t⟩)` and resolves further in `j`.
* `tyOkR E n cur t v`: `v` has the type `t`, with at most `n` nested constructors or named
  types (`n` is fuel; `fuel = 32` is used everywhere, far above the depth of the WASI types).
  The value encoding of named kinds:
  - a `record` is `.record` of its fields' values, in order;
  - a `variant` is `.variant i p` for an existing case `i` with the case's payload;
  - an `enum` is `.variant i none` for an existing case `i`;
  - `flags` with `k` labels is `.record` of `k` booleans (a Silmaril choice: the value encoding of
    `Silmaril.Wasi.Theory` has no flags);
  - a `resource` used as a value is a handle (`.u32`);
  - `type x = t` is the type `t`, resolved in the interface of `x`.
  An unknown name, or running out of fuel, is not well typed.
* `witROk P`, `witRTrapOk P`: `witOk`, `witTrapOk` with the resolved typing.

`tyOkR` refines `tyOk` (`tyOkR_tyOk`, in `Silmaril.Wasi.Versions.WitImport.Resolve`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component (Val)

/-- The named types of each interface. -/
abbrev TyEnv := List (Binary.IfaceName × List (String × Binary.TyDefKind))

/-- A signature table whose entries name the interface of their function. -/
abbrev RTable := List (FnName × Binary.IfaceName × Binary.Sig)

/-- An imported package with its type environment. -/
abbrev RPkg := RTable × TyEnv

/-- The signature table of a resolved table. -/
def strip (R : RTable) : Table := R.map fun x => (x.1, x.2.2)

/-- The interface a reference points into, seen from `cur`. -/
def ownerOf (cur : Binary.IfaceName) : Binary.Owner → Binary.IfaceName
  | .local => cur
  | .iface j => j

/-- The definition of a named type, with the interface it is defined in. -/
def findTy (E : TyEnv) (cur : Binary.IfaceName) (r : Binary.TyRef) :
    Option (Binary.IfaceName × Binary.TyDefKind) :=
  let j := ownerOf cur r.owner
  (E.lookup j).bind fun ts => (ts.lookup r.name).map fun k => (j, k)

/-- A boolean. -/
def isBool : Val → Bool
  | .bool _ => true
  | _ => false

/-- An optional payload of an optional type, for a value check `ok`. -/
def optOk (ok : Binary.Ty → Val → Bool) : Option Binary.Ty → Option Val → Bool
  | none, none => true
  | some t, some v => ok t v
  | _, _ => false

/-- The values have the types, one by one, for a value check `ok`. -/
def zipOk (ok : Binary.Ty → Val → Bool) : List Binary.Ty → List Val → Bool
  | [], [] => true
  | t :: ts, v :: vs => ok t v && zipOk ok ts vs
  | _, _ => false

/-- A map entry `(k, w)`, for a value check `ok`. -/
def pairOk (ok : Binary.Ty → Val → Bool) (k w : Binary.Ty) : Val → Bool
  | .record [a, b] => ok k a && ok w b
  | _ => false

/-- A handle. -/
def isU32 : Val → Bool
  | .u32 _ => true
  | _ => false

/-- A `list`: a record of values accepted by `ok`. -/
def recV (ok : Val → Bool) : Val → Bool
  | .record vs => vs.all ok
  | _ => false

/-- An `option`: case `0` without payload or case `1` with a payload accepted by `ok`. -/
def optV (ok : Val → Bool) : Val → Bool
  | .variant 0 none => true
  | .variant 1 (some v) => ok v
  | _ => false

/-- A `result<a, b>`, for a value check `ok`. -/
def resV (ok : Binary.Ty → Val → Bool) (a b : Option Binary.Ty) : Val → Bool
  | .variant 0 p => optOk ok a p
  | .variant 1 p => optOk ok b p
  | _ => false

/-- A value of a named type of kind `k` defined in the interface `j`, for a value check `ok`. -/
def kindOk (ok : Binary.IfaceName → Binary.Ty → Val → Bool) (j : Binary.IfaceName) :
    Binary.TyDefKind → Val → Bool
  | .record fs, .record vs => zipOk (ok j) (fs.map (·.ty)) vs
  | .variant cs, .variant i p =>
    match cs[i]? with
    | some c => optOk (ok j) c.ty p
    | none => false
  | .enum cs, .variant i none => decide (i < cs.length)
  | .flags fs, .record bs => bs.length == fs.length && bs.all isBool
  | .resource, .u32 _ => true
  | .type t, v => ok j t v
  | _, _ => false

/-- **Resolved WIT typing**: `v` has the type `t` seen from the interface `cur`, with fuel `n`. -/
def tyOkR (E : TyEnv) : Nat → Binary.IfaceName → Binary.Ty → Val → Bool
  | 0, _, _, _ => false
  | n + 1, cur, t, v =>
    match t with
    | .prim p => primOk p v
    | .ref r =>
      match findTy E cur r with
      | some (j, k) => kindOk (tyOkR E n) j k v
      | none => false
    | .list t => recV (tyOkR E n cur t) v
    | .fixedList t k =>
      match v with
      | .record vs => vs.length == k && vs.all (tyOkR E n cur t)
      | _ => false
    | .map k w => recV (pairOk (tyOkR E n cur) k w) v
    | .option t => optV (tyOkR E n cur t) v
    | .result a b => resV (tyOkR E n cur) a b v
    | .tuple ts =>
      match v with
      | .record vs => zipOk (tyOkR E n cur) ts vs
      | _ => false
    | .own _ | .borrow _ | .future _ | .stream _ => isU32 v

/-- The fuel of the resolved typing. -/
def fuel : Nat := 32

/-- The arguments of a call have the resolved parameter types. -/
def argsOkR (E : TyEnv) (cur : Binary.IfaceName) (s : Binary.Sig) (a : List Val) : Bool :=
  zipOk (tyOkR E fuel cur) (s.params.map Prod.snd) a

/-- The answer of a call has the resolved result type (a trap is not well typed). -/
def resOkR (E : TyEnv) (cur : Binary.IfaceName) (s : Binary.Sig) : Option (List Val) → Bool
  | some vs => match s.result with
    | none => vs.isEmpty
    | some t => match vs with
      | [v] => tyOkR E fuel cur t v
      | _ => false
  | none => false

/-- **Resolved WIT typing of import answers** for the functions of a package. -/
def witROk (P : RPkg) : WEv → Bool
  | .imp f a r => match P.1.lookup f with
    | some (i, s) => !argsOkR P.2 i s a || resOkR P.2 i s r
    | none => true
  | _ => true

/-- **Resolved WIT typing of import answers, traps admitted.** -/
def witRTrapOk (P : RPkg) : WEv → Bool
  | .imp f a r => match P.1.lookup f with
    | some (i, s) => !argsOkR P.2 i s a || r.isNone || resOkR P.2 i s r
    | none => true
  | _ => true

/-- The resolved WIT typing theory of a package. -/
def witRTh (P : RPkg) : Silmaril.Wasm.Resource.Protocol Unit WEv := pointwise (witROk P)

/-- The resolved WIT typing theory of a package, traps admitted. -/
def witRTrapTh (P : RPkg) : Silmaril.Wasm.Resource.Protocol Unit WEv := pointwise (witRTrapOk P)

/-- The entries of `P` for the functions `L` (the environment is kept). -/
def rrestrict (P : RPkg) (L : List FnName) : RPkg := (P.1.filter fun x => decide (x.1 ∈ L), P.2)

/-- Two packages side by side: the tables and the environments appended. -/
def rappend (P Q : RPkg) : RPkg := (P.1 ++ Q.1, P.2 ++ Q.2)

end Silmaril.Wasi.Versions.WitImport

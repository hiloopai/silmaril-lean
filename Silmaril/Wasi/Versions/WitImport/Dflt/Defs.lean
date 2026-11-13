module

public import Silmaril.Wasi.Versions.WitImport.Resolve.Defs
public import Silmaril.Wasi.Host.Defs

@[expose] public section

/-!
# The default host of a resolved WIT package

A concrete host (`Silmaril.Wasi.Host.Impl`) for **every** function of a resolved package
(`RPkg`, `Silmaril.Wasi.Versions.WitImport.Resolve`): it answers each call with a fixed value of
the function's resolved result type, computed from the type environment.

* `dfltPrim p`: a value of a primitive type (`false`, `0`, `'a'`, the empty string).
* `dfltV E n cur t`: a value of the type `t` seen from the interface `cur`, with fuel `n`
  (as `tyOkR`): an empty `list`/`map`, `none` for an `option`, the `ok` case of a `result`, the
  first case of a variant or enum, all flags off, handle `0` for a resource or handle, and
  `none` (no value) when a name does not resolve or the fuel runs out.
* `dfltAns E i s`: the answer of a call of the signature `s` of interface `i`.
* `dfltImpl P`: the host. A call of a function of `P` gets `dfltAns`, any other call traps.
* `Defaults P`: every function of `P` has a default answer of its resolved result type. It is
  decided by the kernel per package (`Silmaril.Wasi.Versions.WitImport.Dflt.Thms`).

The host is deliberately trivial: it is a witness that the generic typing theory `witRTh P` of
an imported package has a concrete model (so it is consistent and every function of the
package is answerable), not a model of any behaviour. Handles are all `0`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Binary (PrimValType)

/-- A value of a primitive WIT type. -/
def dfltPrim : PrimValType → Val
  | .bool => .bool false
  | .s8 => .s8 0
  | .u8 => .u8 0
  | .s16 => .s16 0
  | .u16 => .u16 0
  | .s32 => .s32 0
  | .u32 => .u32 0
  | .s64 => .s64 0
  | .u64 => .u64 0
  | .f32 => .f32 0
  | .f64 => .f64 0
  | .char => .char 'a'
  | .string => .record []
  | .errorContext => .u32 0

/-- A value of a named type of kind `k` defined in `j`, for a value generator `d`. -/
def dfltKind (d : Binary.IfaceName → Binary.Ty → Option Val) (j : Binary.IfaceName) :
    Binary.TyDefKind → Option Val
  | .record fs => (fs.mapM fun f => d j f.ty).map .record
  | .variant cs =>
    match cs with
    | [] => none
    | c :: _ =>
      match c.ty with
      | none => some (.variant 0 none)
      | some t => (d j t).map fun v => .variant 0 (some v)
  | .enum cs => if cs.isEmpty then none else some (.variant 0 none)
  | .flags fs => some (.record (fs.map fun _ => .bool false))
  | .resource => some (.u32 0)
  | .type t => d j t

/-- **A default value of the type `t`**, seen from the interface `cur`, with fuel `n`. -/
def dfltV (E : TyEnv) : Nat → Binary.IfaceName → Binary.Ty → Option Val
  | 0, _, _ => none
  | n + 1, cur, t =>
    match t with
    | .prim p => some (dfltPrim p)
    | .ref r =>
      match findTy E cur r with
      | some (j, k) => dfltKind (dfltV E n) j k
      | none => none
    | .list _ => some (.record [])
    | .fixedList t k => (dfltV E n cur t).map fun v => .record (List.replicate k v)
    | .map _ _ => some (.record [])
    | .option _ => some (.variant 0 none)
    | .result a _ =>
      match a with
      | none => some (.variant 0 none)
      | some t => (dfltV E n cur t).map fun v => .variant 0 (some v)
    | .tuple ts => (ts.mapM (dfltV E n cur)).map .record
    | .own _ | .borrow _ | .future _ | .stream _ => some (.u32 0)

/-- The default answer of a call of the signature `s` of the interface `i`. -/
def dfltAns (E : TyEnv) (i : Binary.IfaceName) (s : Binary.Sig) : Option (List Val) :=
  match s.result with
  | none => some []
  | some t => (dfltV E fuel i t).map fun v => [v]

/-- **The default host of a package**: every call of a function of `P` gets its default
answer; any other call traps. -/
def dfltImpl (P : RPkg) : Impl := fun _ f _ =>
  match P.1.lookup f with
  | some (i, s) => dfltAns P.2 i s
  | none => none

/-- Every function of `P` has a default answer of its resolved result type. -/
def Defaults (P : RPkg) : Bool :=
  P.1.all fun x => resOkR P.2 x.2.1 x.2.2 (dfltAns P.2 x.2.1 x.2.2)

end Silmaril.Wasi.Versions.WitImport

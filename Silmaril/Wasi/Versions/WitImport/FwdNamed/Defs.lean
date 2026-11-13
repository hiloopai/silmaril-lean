module

public import Silmaril.Wasi.Versions.WitImport.Fwd.Defs

@[expose] public section

/-!
# Forwarding across named types

`Silmaril.Wasi.Versions.WitImport.Fwd` forwards a call to the function of the same name in the
other version when both signatures are free of named types and equal. Most WASI signatures name
types (`instant`, `mark`, `duration`, `field-name`, `error-code`, resources), and the two
versions define them in different interfaces (`wasi:clocks/monotonic-clock` vs
`wasi:clocks/monotonic-clock@0.3.2`), sometimes under other names (`instant` vs `mark`).

`tyEq E E' k n n' c c' t t'`: the type `t` seen from `c` in the environment `E` at fuel `n` and
`t'` seen from `c'` in `E'` at fuel `n'` have the same resolved typing
(`FwdNamed.Thms.tyOkR_tyEq`). It unfolds aliases (`type x = u`) on either side, and otherwise
compares the shapes, resolving named types on both sides and comparing their definitions:
records by their field types (names are not checked by the typing), variants by their payloads
(case by case, the same number of cases), enums and flags by their number of cases, resources
as handles. It is a sufficient check, not a complete one.

* `sigEqR E E' i i' s s'`: the parameter types and result types are pairwise `tyEq` at the fuel
  of `tyOkR`.
* `fwdPairsN P Q`, `FwdOkN P Q M`: as `fwdPairs`/`FwdOk`, with `sigEqR` in the environments of
  the two packages instead of free, equal signatures.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit

/-- Pairwise, by a check `f`. -/
def listEq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => f x y && listEq f xs ys
  | _, _ => false

/-- Both absent, or both present and related by `f`. -/
def optEq {α : Type} (f : α → α → Bool) : Option α → Option α → Bool
  | none, none => true
  | some x, some y => f x y
  | _, _ => false

/-- Two kinds of named types are equivalent, for a type check `eq` (with the interfaces they are
defined in). -/
def kindEq (eq : Binary.IfaceName → Binary.IfaceName → Binary.Ty → Binary.Ty → Bool)
    (j j' : Binary.IfaceName) : Binary.TyDefKind → Binary.TyDefKind → Bool
  | .record fs, .record fs' => listEq (eq j j') (fs.map (·.ty)) (fs'.map (·.ty))
  | .variant cs, .variant cs' => listEq (optEq (eq j j')) (cs.map (·.ty)) (cs'.map (·.ty))
  | .enum cs, .enum cs' => cs.length == cs'.length
  | .flags fs, .flags fs' => fs.length == fs'.length
  | .resource, .resource => true
  | .type t, .type t' => eq j j' t t'
  | _, _ => false

/-- Handles (resources, futures, streams) are all checked as `u32`s. -/
def isHandleTy : Binary.Ty → Bool
  | .own _ | .borrow _ | .future _ | .stream _ => true
  | _ => false

/-- The target of an alias `type x = u`, with the interface it is defined in. -/
def aliasOf (E : TyEnv) (c : Binary.IfaceName) : Binary.Ty → Option (Binary.IfaceName × Binary.Ty)
  | .ref r =>
    match findTy E c r with
    | some (j, .type u) => some (j, u)
    | _ => none
  | _ => none

/-- The same outermost shape, for a check `eq` of the parts (named types: equivalent kinds). -/
def shapeEq (E E' : TyEnv) (eq : Binary.IfaceName → Binary.IfaceName → Binary.Ty → Binary.Ty → Bool)
    (c c' : Binary.IfaceName) : Binary.Ty → Binary.Ty → Bool
  | .prim p, .prim p' => decide (p = p')
  | .ref r, .ref r' =>
    match findTy E c r, findTy E' c' r' with
    | some (j, k), some (j', k') => kindEq eq j j' k k'
    | none, none => true
    | _, _ => false
  | .list t, .list t' => eq c c' t t'
  | .fixedList t k, .fixedList t' k' => k == k' && eq c c' t t'
  | .map k w, .map k' w' => eq c c' k k' && eq c c' w w'
  | .option t, .option t' => eq c c' t t'
  | .result a b, .result a' b' => optEq (eq c c') a a' && optEq (eq c c') b b'
  | .tuple ts, .tuple ts' => listEq (eq c c') ts ts'
  | t, t' => isHandleTy t && isHandleTy t'

/-- **Equivalent types for the resolved typing**: `t` at fuel `n` in `E` and `t'` at fuel `n'`
in `E'`; `k` bounds the steps (one side's fuel decreases at each). An alias is unfolded on
either side (using one unit of that side's fuel), otherwise the shapes are compared. -/
def tyEq (E E' : TyEnv) : Nat → Nat → Nat → Binary.IfaceName → Binary.IfaceName → Binary.Ty →
    Binary.Ty → Bool
  | _, 0, 0, _, _, _, _ => true
  | k + 1, n + 1, n' + 1, c, c', t, t' =>
    match aliasOf E c t, aliasOf E' c' t' with
    | some (j, u), _ => tyEq E E' k n (n' + 1) j c' u t'
    | none, some (j', u') => tyEq E E' k (n + 1) n' c j' t u'
    | none, none => shapeEq E E' (tyEq E E' k n n') c c' t t'
  | _, _, _, _, _, _, _ => false

/-- Two signatures have the same resolved typing (parameters and result). -/
def sigEqR (E E' : TyEnv) (i i' : Binary.IfaceName) (s s' : Binary.Sig) : Bool :=
  listEq (tyEq E E' (2 * fuel) fuel fuel i i') (s.params.map Prod.snd) (s'.params.map Prod.snd) &&
    optEq (tyEq E E' (2 * fuel) fuel fuel i i') s.result s'.result

/-- The two functions match across named types: same name and interface (version dropped),
equivalent signatures in the environments `EQ` (of the export) and `EP` (of the import). -/
def fwdMatchN (EQ EP : TyEnv) (x y : FnName × Binary.IfaceName × Binary.Sig) : Bool :=
  x.1.fn == y.1.fn && unver x.1.iface == unver y.1.iface && sigEqR EQ EP x.2.1 y.2.1 x.2.2 y.2.2

/-- **The forwarding pairs across named types** from the functions of `Q` to those of `P`. -/
def fwdPairsN (P Q : RPkg) : FwdMap :=
  (Q.1.filter fun x => unver x.1.iface != "wasi:cli/run").filterMap fun x =>
    (P.1.find? (fwdMatchN Q.2 P.2 x)).map fun y => (x.1, y.1)

/-- The pairs have equivalent signatures. -/
def FwdOkN (P Q : RPkg) (M : FwdMap) : Bool :=
  M.all fun fg =>
    match Q.1.lookup fg.1, P.1.lookup fg.2 with
    | some (i, s), some (i', s') => sigEqR Q.2 P.2 i i' s s'
    | _, _ => false

end Silmaril.Wasi.Versions.WitImport

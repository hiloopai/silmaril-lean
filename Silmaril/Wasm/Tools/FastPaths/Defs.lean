module

public import Silmaril.Wasm.Tools.FastFrame.Defs
public import Silmaril.Wasm.Tools.Strip.Defs
public import Silmaril.Wasm.Tools.Objdump.Defs
public import Silmaril.Wasm.Tools.Validate.Defs

/-!
# `ByteArray` fast paths of `validate`, `strip` and `objdump`

The specification functions `Validate.check` (its encoding gates), `Strip.strip` and
`Objdump.objdump` read the input as a `List UInt8`. These versions read it in place through the
views of `Silmaril.Wasm.Tools.FastFrame`, copying only the sections whose contents they inspect
(type, table and element sections for the gates; start, data count and code sections for the
parser's checks) and, for `strip`, the kept sections into the output.

`Thms`: `checkFast_eq : checkFast F b = Validate.check F b`,
`stripFast_eq : (stripFast rm b).map (·.data.toList) = Strip.strip rm b.data.toList`,
`objdumpFast_eq : objdumpFast b = Objdump.objdump b.data.toList`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.FastPaths

open Silmaril.Wasm.Tools.Framing Silmaril.Wasm.Tools.FastFrame Silmaril.Wasm.Tools.Features

/-! ## `validate`: the encoding gates -/

/-- `Validate.binGates` on the array. -/
def binGatesAt (F : WFeatures) (b : ByteArray) : Bool :=
  let bulk := F.hasFlag "bulk-memory"
  let exn := F.hasFlag "exceptions"
  let gc := F.hasFlag "gc"
  let fref := F.hasFlag "function-references"
  if bulk && exn && gc && fref then true else
  match splitAt b b.size (b.size - 8) 8 with
  | none => true
  | some vs => vs.all fun v =>
    (v.id != 12 || bulk) && (v.id != 13 || exn) &&
    (v.id != 1 || gc || !Validate.typeSecUsesGc (winC b v.cstart v.cend)) &&
    (v.id != 4 || fref || !Validate.tableSecHasInit (winC b v.cstart v.cend)) &&
    (v.id != 9 || fref || !Validate.elemSecNonNull (winC b v.cstart v.cend))

/-- **`Validate.check` with the gates read in place.** -/
def checkFast (F : WFeatures) (b : ByteArray) : Except Validate.Error Unit :=
  if !binGatesAt F b then .error .encodingFeature else
  match Validate.decodeW F b with
  | .error e => .error (.malformed e)
  | .ok m =>
    match Silmaril.Wasm.Validation.validate? m with
    | none => .error .invalid
    | some _ => if Validate.inFeatWB F m then .ok () else .error .feature

/-! ## `strip` -/

/-- `nestedEnc` from a section id. -/
def nestedEncV (e : Enc) (v : View) : Option Enc := nestedEnc e ⟨v.id, [], []⟩

/-- `Strip.keepSec` on a view. -/
def keepAt (b : ByteArray) (rm : String → Bool) (v : View) : Bool :=
  if v.id = 0 then
    match customNameAt b v.cstart v.cend with
    | .ok (n, _) => !rm n
    | .error _ => true
  else true

/-- A section with a minimal size field (`RawSec.canon`). -/
def secBytes (id : UInt8) (content : ByteArray) : ByteArray :=
  ⟨#[id]⟩ ++ ⟨(encUN content.size).toArray⟩ ++ content

/-- `Strip.stripF` on views, giving the bytes of the kept sections. -/
def stripAt (b : ByteArray) (rm : String → Bool) : Nat → Enc → List View → Except String ByteArray
  | _, _, [] => .ok ByteArray.empty
  | fuel, e, v :: vs => do
    let rest ← stripAt b rm fuel e vs
    if !keepAt b rm v then return rest
    match nestedEncV e v, fuel with
    | some e', fuel' + 1 =>
      let (_, inner) ← frameAt b (some e') v.cstart v.cend
      let inner' ← stripAt b rm fuel' e' inner
      return secBytes v.id (⟨e'.header.toArray⟩ ++ inner') ++ rest
    | some _, 0 => .error "nesting too deep"
    | none, _ => return secBytes v.id (b.extract v.cstart v.cend) ++ rest
termination_by fuel _ vs => (fuel, vs.length)

/-- **`Strip.strip` on the array.** -/
def stripFast (rm : String → Bool) (b : ByteArray) : Except String ByteArray := do
  let (e, vs) ← frameAt b none 0 b.size
  let out ← stripAt b rm b.size e vs
  return ⟨e.header.toArray⟩ ++ out

/-! ## `objdump` -/

open Silmaril.Wasm.Tools.Objdump in
/-- `Objdump.count` on a view. -/
def countAt (b : ByteArray) (e : Enc) (v : View) : Nat :=
  let id := v.id.toNat
  let limited := match e with
    | .module => moduleLimited id || id = 10
    | .component => componentLimited id
  if limited then
    match readUNAt b v.cend 32 v.cstart with
    | some (n, _) => n
    | none => 0
  else 1

open Silmaril.Wasm.Tools.Objdump in
/-- `Objdump.lines.go` on views (a view's content starts at `cstart`, absolute). -/
def linesAt (b : ByteArray) : Nat → Enc → List View → Printer →
    Except String (List String × Printer)
  | _, _, [], p => .ok ([], p)
  | fuel, e, v :: rest, p => do
    let o := v.cstart
    let stop := o + (v.cend - v.cstart)
    let (here, p) ← (do
      if v.id = 0 then
        let (n, d) ← customNameAt b v.cstart v.cend
        return ([fmtLine (header p) ("custom " ++ debugStr n) (o + d) stop 1], p)
      match secName e v.id.toNat with
      | none => return ([], p)
      | some name =>
        let l := fmtLine (header p) name o stop (countAt b e v)
        match nestedEncV e v, fuel with
        | some e', fuel' + 1 =>
          let (_, inner) ← frameAt b (some e') v.cstart v.cend
          let p := if e' = .component then {} :: p else p
          let (p, sl) := start p e'
          let (ls, p) ← linesAt b fuel' e' inner p
          let (p, el) := «end» p
          return ([l, sl] ++ ls ++ el.toList, p)
        | some _, 0 => .error "nesting too deep"
        | none, _ => return ([l], p) : Except String (List String × Printer))
    let (more, p) ← linesAt b fuel e rest p
    return (here ++ more, p)
termination_by fuel _ vs => (fuel, vs.length)

/-- **`Objdump.objdump` on the array.** -/
def objdumpFast (b : ByteArray) : Except String (List String) := do
  let (e, vs) ← frameAt b none 0 b.size
  let (ls, _) ← linesAt b b.size e vs [{}]
  return ls

end Silmaril.Wasm.Tools.FastPaths

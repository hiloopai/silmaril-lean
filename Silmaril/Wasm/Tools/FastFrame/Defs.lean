module

public import Silmaril.Wasm.Tools.Framing.Defs

/-!
# Framing on `ByteArray` windows (fast paths)

The specification functions of `Silmaril.Wasm.Tools.Framing` run on `List UInt8`; on a
multi-megabyte binary converting the input to a list and copying section contents with
`take`/`drop` dominates. This module reads the same grammar directly from a `ByteArray`,
between two indices, without building lists for the bytes it skips:

* `win b i e`: the window `[i, e)` of `b` as a list (the specification's view; never computed
  by the fast paths);
* `readUNAt b e N i`: `readUN N` on the window, giving the value and the index after it;
* `splitAt b e fuel i`: the sections of the window as `View`s (offsets of the size field and
  of the content);
* `customNameAt`, `secCountAt`, `readHeaderAt`, `checkSecsAt`, `frameAt`: the parser's checks
  and the preamble, on views.

`Thms` proves each equal to its specification function on the window (`readUN_win`,
`splitSecsF_win`, `customName_win`, `readHeader_win`, `frame_win`, …).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.FastFrame

open Silmaril.Wasm.Binary (Bytes)
open Silmaril.Wasm.Tools.Framing

/-- **The window `[i, e)` of `b`** (specification only). -/
def win (b : ByteArray) (i e : Nat) : Bytes := (b.data.toList.take e).drop i

/-- The window `[i, e)` of `b`, computed by copying just those bytes. -/
def winC (b : ByteArray) (i e : Nat) : Bytes := (b.extract i e).data.toList

/-- `readUN N` on the window `[i, e)` of `b`: the value and the index after the number. -/
def readUNAt (b : ByteArray) (e : Nat) (N i : Nat) : Option (Nat × Nat) :=
  if h : i < e ∧ i < b.size then
    let n := b[i]
    if n.toNat < 2 ^ 7 then (if n.toNat < 2 ^ N then some (n.toNat, i + 1) else none)
    else if 7 < N then
      match readUNAt b e (N - 7) (i + 1) with
      | some (m, j) => some (2 ^ 7 * m + (n.toNat - 2 ^ 7), j)
      | none => none
    else none
  else none
termination_by e - i

/-- A section of a window: its id, where it starts, where its content starts and ends. -/
structure View where
  id : UInt8
  start : Nat
  cstart : Nat
  cend : Nat
  deriving Repr, DecidableEq

/-- A view lies in the window: size field, then content, ending by `e` (specification only). -/
def View.ok (e : Nat) (v : View) : Prop := v.start < v.cstart ∧ v.cstart ≤ v.cend ∧ v.cend ≤ e

/-- Views whose contents lie inside the array (specification only). -/
def Inside (b : ByteArray) (vs : List View) : Prop := ∀ v ∈ vs, v.cstart ≤ v.cend ∧ v.cend ≤ b.size

/-- The section a view denotes (specification only). -/
def View.raw (b : ByteArray) (v : View) : RawSec :=
  ⟨v.id, win b (v.start + 1) v.cstart, win b v.cstart v.cend⟩

/-- The sections of the window `[i, e)` (`splitSecsF` on views). -/
def splitAt (b : ByteArray) (e : Nat) : Nat → Nat → Option (List View)
  | fuel, i =>
    if h : i < e ∧ i < b.size then
      match fuel with
      | 0 => none
      | fuel + 1 =>
        match readUNAt b e 32 (i + 1) with
        | none => none
        | some (len, j) =>
          if j + len ≤ e then (splitAt b e fuel (j + len)).map (⟨b[i], i, j, j + len⟩ :: ·)
          else none
    else some []

/-- `customName` of the content `[i, e)`. -/
def customNameAt (b : ByteArray) (i e : Nat) : Except String (String × Nat) :=
  match readUNAt b e 32 i with
  | none => .error "unexpected end-of-file"
  | some (len, j) =>
    if len > 100000 then .error "string size out of bounds"
    else if ¬ j + len ≤ e then .error "unexpected end-of-file"
    else
      match String.fromUTF8? (b.extract j (j + len)) with
      | some s => .ok (s, j + len - i)
      | none => .error "malformed UTF-8 encoding"

/-- `secCount` of the content `[i, e)`. -/
def secCountAt (b : ByteArray) (i e : Nat) : Except String Nat :=
  match readUNAt b e 32 i with
  | some (n, _) => .ok n
  | none => .error "unexpected end-of-file"

/-- One section of a module through the parser's checks (`ModState.step`): the name and count
are read in place, the start, data count and code sections are copied. -/
def stepAt (b : ByteArray) (st : ModState) (v : View) : Except String ModState := do
  let id := v.id.toNat
  if id = 0 then
    let _ ← customNameAt b v.cstart v.cend
    return st
  match orderRank id with
  | none => return st
  | some k =>
    if k ≤ st.last then .error "section out of order"
    let st := { st with last := k }
    if moduleLimited id then
      let n ← secCountAt b v.cstart v.cend
      if id = 3 then return { st with funcs := some n }
      if id = 11 then
        let st := { st with datas := some n }
        st.checkData
        return st
      return st
    if id = 8 then
      let _ ← singleItem "start" (winC b v.cstart v.cend)
      return st
    if id = 12 then
      let n ← singleItem "data count" (winC b v.cstart v.cend)
      return { st with dataCount := some n }
    let n ← codeEntries (winC b v.cstart v.cend)
    let st := { st with codes := some n }
    st.checkCode
    return st

/-- `checkModule` on views. -/
def checkModuleAt (b : ByteArray) (vs : List View) : Except String Unit := do
  let st ← vs.foldlM (stepAt b) {}
  st.checkCode
  st.checkData

/-- `checkComponentSec` on a view. -/
def checkComponentSecAt (b : ByteArray) (v : View) : Except String Unit := do
  let id := v.id.toNat
  if id = 0 then
    let _ ← customNameAt b v.cstart v.cend
    return ()
  if componentLimited id then
    let _ ← secCountAt b v.cstart v.cend
    return ()
  if id = 9 then componentStart (winC b v.cstart v.cend)
  if (id = 1 ∨ id = 4) ∧ v.cend - v.cstart > 1024 * 1024 * 1024 then
    .error (if id = 1 then "module section is too large" else "component section is too large")
  return ()

/-- `checkComponent` on views. -/
def checkComponentAt (b : ByteArray) (vs : List View) : Except String Unit := do
  for v in vs do checkComponentSecAt b v
  if (vs.filter (·.id == 9)).length > 1 then
    .error "component cannot have more than one start function"

/-- `checkIds` on views. -/
def checkIdsAt (b : ByteArray) (vs : List View) : Except String Unit := do
  for v in vs do
    if v.id.toNat ≥ 0x80 then .error "malformed section id"
    if v.id = 0 && winC b (v.start + 1) v.cstart = [0x61] &&
        winC b v.cstart (min (v.cstart + 2) v.cend) = [0x73, 0x6D] then
      .error "expected section, got wasm magic number"

/-- `checkSecs` on views. -/
def checkSecsAt (b : ByteArray) (e : Enc) (vs : List View) : Except String Unit := do
  checkIdsAt b vs
  match e with
  | .module => checkModuleAt b vs
  | .component => checkComponentAt b vs

/-- `readHeader` on the window `[i, e)`: the encoding and the index after the preamble. -/
def readHeaderAt (b : ByteArray) (expect : Option Enc) (i e : Nat) : Except String (Enc × Nat) :=
  match readHeader expect (winC b i (min (i + 8) e)) with
  | .ok (enc, _) => .ok (enc, i + 8)
  | .error m => .error m

/-- **`frame` on the window `[i, e)`**. -/
def frameAt (b : ByteArray) (expect : Option Enc) (i e : Nat) :
    Except String (Enc × List View) := do
  let (enc, j) ← readHeaderAt b expect i e
  match splitAt b e (e - j) j with
  | some vs =>
    checkSecsAt b enc vs
    return (enc, vs)
  | none => .error "unexpected end-of-file"

end Silmaril.Wasm.Tools.FastFrame

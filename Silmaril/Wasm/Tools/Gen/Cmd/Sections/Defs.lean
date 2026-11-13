module

public import Silmaril.Wasm.Tools.Gen.Core.Defs

/-!
# Custom sections kept across `mutate` and `shrink`

silmaril's `Module` has no custom sections, so the decoder drops them and the encoder writes
none. `wasm-tools mutate` and `shrink` keep them, as upstream does (wasm-mutate and
wasm-shrink copy custom sections they do not touch). The mutated module is encoded, its
section list is read back (`split`), and the input's custom sections are put back
(`splice`), each before the first section of the output whose rank in the binary format's
section order (`rank`) is above the rank of the non-custom section that preceded it in the
input (`anchors`); custom sections at the start stay at the start.

`Thms`: `splice` keeps every custom section, in order (`customs_splice`), and every
non-custom section of the encoder's output, in order (`nonCustom_splice`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Sections

/-- A section: its id and payload (a slice of the module's bytes). -/
structure Sec where
  id : UInt8
  payload : ByteArray
  deriving Inhabited

/-- Is the section a custom section (id 0)? -/
def Sec.isCustom (s : Sec) : Bool := s.id == 0

/-- The rank of a section id in the order of the binary format (Wasm 3.0, section 5.5.2):
type, import, function, table, memory, tag, global, export, start, element, data count,
code, data. Custom sections rank 0. -/
def rank : UInt8 → Nat
  | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 13 => 6 | 6 => 7 | 7 => 8 | 8 => 9
  | 9 => 10 | 12 => 11 | 10 => 12 | 11 => 13 | _ => 0

/-- An unsigned LEB128 number at `pos` (at most `fuel` bytes): its value and the position
after it. -/
def readLeb (b : ByteArray) : Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _ => none
  | fuel + 1, pos, acc, sh =>
    if pos < b.size then
      let x := b[pos]!.toNat
      let acc := acc + x % 128 * 2 ^ sh
      if x < 128 then some (acc, pos + 1) else readLeb b fuel (pos + 1) acc (sh + 7)
    else none

/-- The minimal unsigned LEB128 encoding of `n` (`fuel` bounds the bytes). -/
def encLeb : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n => if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: encLeb fuel (n / 128)

/-- The sections from `pos` on (each takes at least one byte, so `fuel` = the size bounds
them). -/
def splitFrom (b : ByteArray) : Nat → Nat → Option (List Sec)
  | 0, pos => if b.size ≤ pos then some [] else none
  | fuel + 1, pos =>
    if b.size ≤ pos then some [] else do
      let (n, p) ← readLeb b 5 (pos + 1) 0 0
      if b.size < p + n then none
      let tail ← splitFrom b fuel (p + n)
      return ⟨b[pos]!, b.extract p (p + n)⟩ :: tail

/-- The sections of a binary module, `none` when the bytes are not a sequence of sections
after a header. -/
def split (b : ByteArray) : Option (List Sec) :=
  if b.size < 8 then none else splitFrom b b.size 8

/-- The bytes of sections after `header`. -/
def join (header : ByteArray) (secs : List Sec) : ByteArray :=
  secs.foldl (fun acc s => (acc.push s.id ++ ⟨(encLeb 5 s.payload.size).toArray⟩) ++ s.payload)
    header

/-- The custom sections of a section list, each with the rank of the last non-custom section
before it (`0` at the start). -/
def anchorsFrom : Nat → List Sec → List (Nat × Sec)
  | _, [] => []
  | r, s :: ss => if s.isCustom then (r, s) :: anchorsFrom r ss else anchorsFrom (rank s.id) ss

def anchors (secs : List Sec) : List (Nat × Sec) := anchorsFrom 0 secs

/-- **Put anchored custom sections back** into a section list: each before the first section
whose rank is above its anchor; the rest at the end. -/
def splice : List (Nat × Sec) → List Sec → List Sec
  | cs, [] => cs.map (·.2)
  | cs, s :: ss =>
    let p := cs.span (·.1 < rank s.id)
    p.1.map (·.2) ++ s :: splice p.2 ss

/-- **The bytes with the custom sections `cs` put back**: the encoder's output `enc` when it
does not split into sections (never the case for silmaril's encoder). -/
def restore (cs : List (Nat × Sec)) (enc : ByteArray) : ByteArray :=
  if cs.isEmpty then enc else
  match split enc with
  | some secs => join (enc.extract 0 8) (splice cs (secs.filter (!·.isCustom)))
  | none => enc

/-- The anchored custom sections of a binary input (none for text or unreadable bytes). -/
def customsOf (b : ByteArray) : List (Nat × Sec) :=
  match split b with
  | some secs => anchors secs
  | none => []

/-- The anchors wasmprinter prints `(after …)` with: as `anchorsFrom`, except that the data
count section (id 12), which has no name in the text format, does not move the anchor. -/
def printAnchorsFrom : Nat → List Sec → List (Nat × List UInt8)
  | _, [] => []
  | r, s :: ss =>
    if s.isCustom then (r, s.payload.data.toList) :: printAnchorsFrom r ss
    else printAnchorsFrom (if s.id == 12 then r else rank s.id) ss

/-- The custom sections of a binary with the anchors of their text form. -/
def printAnchors (b : ByteArray) : List (Nat × List UInt8) :=
  match split b with
  | some secs => printAnchorsFrom 0 secs
  | none => []

end Silmaril.Wasm.Tools.Gen.Cmd.Sections

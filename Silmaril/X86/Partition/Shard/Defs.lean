module

public import Silmaril.X86.Partition.Defs
public meta import Lean.Elab.Term

/-!
# Sharded partition checking

`Partition.check2` is one kernel `decide` over the whole region. It decodes the region front
to back, finds each instruction's slot by a linear search over the layout, filters the whole
listing once per function, and tests jump targets by `List` membership. Its kernel cost grows
faster than linearly: for a `.text` of some tens of kilobytes, one `decide` takes minutes and
gigabytes.

This module splits the same check into independent pieces. Each piece is a small kernel
`decide`, and the pieces can live in different modules, which `lake` builds in parallel.
`Shard/Thms.lean` proves that together they imply `check2 r p fuel = none`
(`check2_of_shards`), so every soundness theorem of `Partition/Thms.lean` applies unchanged.

## The certificate (`Cert`)

An untrusted certificate written by the proposer:

* `pieces`: byte ranges `[start, stop)` that tile the region in order. Each piece lies inside
  one layout slot (`slot`, an index into `p.layout`) and carries its own bytes (written `(bytesNat! "…").map (BitVec.ofNat 8)`). A large slot is
  cut into several pieces at instruction boundaries; a small slot is one piece. The bytes are
  given per piece so that a piece's check reads its bytes from
  `pieces[j]` without walking the bytes before it; the decoder's lookahead past the piece
  end (at most `maxInstrLength` bytes) is read from the following pieces (`pieceBytes`). One kernel comparison, separate from
  the piece checks, ties them to the region (`r.bytes = (pieces.map bytes).flatten`).
* `bits`: for each function, the set of its instruction addresses as a bitmap (bit
  `a - base` for address `a`).

## The checks

* `checkGlobal base len p c` (no decoding): the layout tiles `[base, base + len)`, owners
  exist, exported functions carry an ABI, the pieces tile the region and each lies inside its
  slot, there is one bitmap per function, each function's entry is in its bitmap, and each
  bitmap only has bits inside the function's own slots (`coverOf`).
* `checkPiece base p c j` (one decoding): piece `j` has as many bytes as it is long and decodes
  exactly to its end (`decodeSpan`). In a padding slot every instruction is a NOP. In a code
  slot of function `i`, the piece's instruction addresses are exactly the bits of `i`'s bitmap
  inside the piece (`restrict`), and every edge of every instruction passes the `check2` rule
  with `i`'s bitmap as the function's address set (`instrOk`).

The fall-through rule needs no successor: an instruction of `i` falls through to `t` only if
`t = addr + size` and `t` is in `i`'s bitmap. The bitmap check makes `t` the address of an
instruction of `i`; since listed addresses are contiguous and distinct, that instruction is the
next listed one, which is what `check2` asks for.
-/

@[expose] public section

namespace Silmaril.X86.Partition.Shard

open Silmaril.X86 (Byte)
open Silmaril.X86.Decompile (Edge)

/-! ## Bytes -/

/-- `bytesNat! "4889e5"`: the list `[0x48, 0x89, 0xe5] : List Nat`, written as a hex string.
The elaborator builds the list term directly (`List.cons` of raw numerals), which is about
twenty times cheaper to elaborate than a list literal of the same length and cheaper for the
kernel to reduce. Nothing depends on it being right: a certificate's bytes are compared with
the region's bytes by a kernel `decide`. -/
syntax (name := bytesNatLit) "bytesNat! " str : term

/-- The value of a hex digit (`none` for anything else). -/
meta def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

open Lean Elab Term in
/-- Elaborate `bytesNat! "…"`. -/
@[term_elab bytesNatLit] meta def elabBytesNatLit : TermElab := fun stx _ => do
  let some s := stx[1].isStrLit? | throwUnsupportedSyntax
  let cs := s.toList.toArray
  if cs.size % 2 ≠ 0 then throwError "bytesNat!: odd number of hex digits"
  let mut ns : Array Nat := #[]
  for k in [0:cs.size / 2] do
    match hexDigit cs[2 * k]!, hexDigit cs[2 * k + 1]! with
    | some hi, some lo => ns := ns.push (hi * 16 + lo)
    | _, _ => throwError "bytesNat!: not a hex digit at {2 * k}"
  let nat := Lean.mkConst ``Nat
  return ns.foldr (fun n acc => mkApp3 (Lean.mkConst ``List.cons [0]) nat (mkRawNatLit n) acc)
    (mkApp (Lean.mkConst ``List.nil [0]) nat)

/-! ## Decoding one piece -/

/-- Decode `bytes`, placed at `addr`, up to exactly `stop`. The same steps as
`Partition.decodeFrom`, which instead runs to the end of the bytes. -/
def decodeSpan (un : List (Nat × Nat)) (stop : Nat) : Nat → Nat → List Byte → Except Reject (List D8)
  | 0, addr, _ => if addr = stop then .ok [] else .error .outOfFuel
  | _ + 1, addr, [] => if addr = stop then .ok [] else .error (.undecodable addr)
  | fuel + 1, addr, b :: t =>
    if addr = stop then .ok []
    else
      match un.lookup addr with
      | some n =>
        if n = 0 ∨ ((b :: t).take n).length < n then .error (.badUnmodelled addr)
        else if (decodeAt (b :: t)).isSome then .error (.unmodelledDecodes addr)
        else (decodeSpan un stop fuel (addr + n) ((b :: t).drop n)).map (⟨addr, .unmodelled, n⟩ :: ·)
      | none =>
        match decodeAt (b :: t) with
        | none => .error (.undecodable addr)
        | some (i, n) =>
          if n = 0 then .error (.undecodable addr)
          else (decodeSpan un stop fuel (addr + n) ((b :: t).drop n)).map (⟨addr, i, n⟩ :: ·)

/-! ## Address sets as bitmaps -/

/-- The addresses of `ds`, as a bitmap relative to `base`. -/
def addrBits (base : Nat) (ds : List D8) : Nat :=
  ds.foldl (fun acc d => acc ||| 2 ^ (d.addr - base)) 0

/-- `t` is in the bitmap `bits` relative to `base`. -/
def inBits (base bits t : Nat) : Bool := decide (base ≤ t) && bits.testBit (t - base)

/-- The bits of `bits` at positions `[a, b)`, in place. -/
def restrict (bits a b : Nat) : Nat := ((bits >>> a) % 2 ^ (b - a)) <<< a

/-! ## The certificate -/

/-- A piece of the region: `[start, stop)`, inside layout slot number `slot`, with its bytes. -/
structure Piece where
  /-- The index of the layout slot that contains the piece. -/
  slot : Nat
  /-- The first address. -/
  start : Nat
  /-- The first address past the piece. -/
  stop : Nat
  /-- The bytes of `[start, stop)`. -/
  bytes : List Byte

/-- A sharding certificate. Untrusted: `checkGlobal` and `checkPiece` verify it. -/
structure Cert where
  /-- Pieces that tile the region, in address order. -/
  pieces : List Piece
  /-- For each function, its instruction addresses as a bitmap relative to the base. -/
  bits : List Nat

/-- The bytes from the start of piece `j` to the end of the region. -/
def restBytes (c : Cert) (j : Nat) : List Byte := ((c.pieces.drop j).map Piece.bytes).flatten

/-- What the check of piece `P`, number `j`, decodes: its bytes, then at most
`maxInstrLength` bytes of lookahead. The bound matters for the kernel: the decoder never
needs more, and without it some reduction step walks the whole rest of the region. -/
def pieceBytes (c : Cert) (j : Nat) (P : Piece) : List Byte :=
  P.bytes ++ (restBytes c (j + 1)).take Silmaril.X86.maxInstrLength

/-- The bitmap of function `i` (empty if there is none). -/
def Cert.bitsOf (c : Cert) (i : Nat) : Nat := (c.bits[i]?).getD 0

/-! ## Checking one piece -/

/-- The instruction `d` is a call to a function declared `noreturn` (`Ctx.callsNoreturn`). -/
def callsNoreturn (p : Proposal) (d : D8) : Bool := Ctx.callsNoreturn ⟨p, []⟩ d

/-- A jump or branch target of `d` in function `i` (`Ctx.checkJump`, with the function's
addresses as a bitmap). -/
def jumpOk (base : Nat) (p : Proposal) (i bits : Nat) (d : D8) (t : Nat) : Option Reject :=
  if inBits base bits t then none
  else if d.addr ∈ p.tailCalls then
    match p.entryOf t with
    | some j => if p.noret i && !p.noret j then some (.badTailCall d.addr t) else none
    | none => some (.badTailCall d.addr t)
  else some (.escapingEdge d.addr t)

/-- One edge of the instruction `d` of function `i` (`Ctx.checkEdge`). A fall-through must
reach `addr + size`, and that address must be in the function's bitmap. -/
def edgeOk (base : Nat) (p : Proposal) (i bits : Nat) (d : D8) : Edge → Option Reject
  | .fallthrough t =>
    if callsNoreturn p d then none
    else if t = d.addr + d.size ∧ inBits base bits t = true then none
    else some (.fallsOut d.addr t)
  | .jump t => jumpOk base p i bits d t
  | .branch t => jumpOk base p i bits d t
  | .call t => if (p.entryOf t).isSome then none else some (.callToNonEntry d.addr t)
  | .ret => if p.noret i then some (.retInNoreturn d.addr) else none
  | .halt => none

/-- Every check of `Ctx.walk` on one instruction of function `i`. -/
def instrOk (base : Nat) (p : Proposal) (i bits : Nat) (d : D8) : Option Reject :=
  if d.item = .unmodelled ∧ p.noret i = true then some (.unmodelledInNoreturn d.addr)
  else d.edges.findSome? (edgeOk base p i bits d)

/-- A listed instruction is a NOP. -/
def isNop (d : D8) : Bool :=
  match d.item with
  | .base (.nop _) => true
  | _ => false

/-- **The check of piece `j`.** Decode it from its bytes; in padding, only NOPs; in a code
slot of function `i`, its addresses are exactly `i`'s bits inside the piece and every
instruction passes `instrOk`. -/
def checkPiece (base : Nat) (p : Proposal) (c : Cert) (j : Nat) : Option Reject :=
  match c.pieces[j]? with
  | none => some .outOfFuel
  | some P =>
    if P.bytes.length ≠ P.stop - P.start then some (.badSlot P.start P.stop)
    else
      match decodeSpan p.unmodelled P.stop (P.stop - P.start) P.start (pieceBytes c j P) with
      | .error e => some e
      | .ok ds =>
        match p.layout[P.slot]? with
        | none => some (.badSlot P.start P.stop)
        | some (.padding _ _) =>
          match ds.find? fun d => !isNop d with
          | some d => some (.paddingNotNop d.addr)
          | none => none
        | some (.code i _ _) =>
          let bits := c.bitsOf i
          if addrBits base ds = restrict bits (P.start - base) (P.stop - base) then
            ds.findSome? (instrOk base p i bits)
          else some (.badEntry s!"piece {j}: bitmap")

/-! ## The global check -/

/-- The pieces tile `[cursor, limit)`: each non-empty, starting where the previous one stopped,
and the last stopping at `limit`. -/
def piecesTile (limit : Nat) : Nat → List Piece → Bool
  | cursor, [] => cursor = limit
  | cursor, P :: rest => P.start = cursor && P.start < P.stop && piecesTile limit P.stop rest

/-- The piece lies inside its layout slot. -/
def inSlot (p : Proposal) (P : Piece) : Bool :=
  match p.layout[P.slot]? with
  | some s => s.start ≤ P.start && P.stop ≤ s.stop
  | none => false

/-- The bits of `bits` that lie in the slots of function `i`. -/
def coverOf (base : Nat) (p : Proposal) (i bits : Nat) : Nat :=
  p.layout.foldl (fun acc s =>
    if s.owner = some i then acc ||| restrict bits (s.start - base) (s.stop - base) else acc) 0

/-- Function `i`'s entry is in its bitmap, and its bitmap has no bit outside its slots. -/
def fnOk (base : Nat) (p : Proposal) (c : Cert) (i : Nat) : Bool :=
  match p.funcs[i]? with
  | some f => inBits base (c.bitsOf i) f.entry && coverOf base p i (c.bitsOf i) == c.bitsOf i
  | none => false

/-- **The global check.** No decoding. -/
def checkGlobal (base len : Nat) (p : Proposal) (c : Cert) : Option Reject :=
  match tiling (base + len) base p.layout with
  | some rej => some rej
  | none =>
    match p.layout.find? fun s => (s.owner.map fun o => decide (p.funcs.length ≤ o)).getD false with
    | some s => some (.noOwner ((s.owner).getD 0))
    | none =>
      match p.funcs.find? fun f => f.exported && !f.conv.isAbi with
      | some f => some (.exportedInferred f.name)
      | none =>
        if !piecesTile (base + len) base c.pieces then some (.uncovered base (base + len))
        else
          match c.pieces.find? fun P => !inSlot p P with
          | some P => some (.straddlesSlot P.start)
          | none =>
            if c.bits.length ≠ p.funcs.length then some (.badEntry "bitmaps")
            else
              match (List.range p.funcs.length).find? fun i => !fnOk base p c i with
              | some i => some (.badEntry ((p.funcs[i]?.map Fn.name).getD ""))
              | none => none

/-- `P 0 ∧ … ∧ P (n - 1)`, as nested conjunctions, so that each conjunct can be a separate
theorem. -/
def Below (P : Nat → Prop) : Nat → Prop
  | 0 => True
  | n + 1 => Below P n ∧ P n

end Silmaril.X86.Partition.Shard

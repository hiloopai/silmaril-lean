module

public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Binaryen.Exe.PadLEB

@[expose] public section

/-! # The hint-guided padded encoder

`encodeModuleP? hint m` writes the same module as `encodeModule? m`, except that the
LEB128 immediates of the code section (indices, constants, memory offsets) take the
width of the LEB128 found at the same output position of `hint` (`lebLen`, capped at
the grammar's maximum, never below the minimal width). The round-trip check (`checkRoundTrip`) passes the custom-stripped
input as the hint: linker output with padded relocation LEBs (`80 80 84 80 00` for
`65536`) then re-encodes byte for byte.

The hint is untrusted: `encodeModuleP?_sound` (`EncodePaddedSound.lean`) holds for
every hint, as every padded width derives the same value in the grammar. When an
earlier difference shifts the positions, the output simply differs from the input.

The data count section is optional when the code mentions no data index: it is
written when the hint has one at its position, or when the code needs it
(`usesDataIdx`). Linker output without one (data in section 11 only) then re-encodes
byte for byte; `encodeModule?` always writes one when there are segments.

Section sizes, section vector counts and code-entry sizes also take the hint's width
(`encU32P`), and a vector section that is empty is still written when the hint has
that section id at its position (`encVecSectionP`). A size is written after its
contents, which are positioned as if the size had the hint's width there.

Three formats beyond widths follow the hint as well: the local declarations take the
hint's group counts when those groups stand for exactly the function's locals
(`localGroupsP`: linkers split runs, `1 i32, 1 i32`), else the run-length groups; the
`call_indirect` type index takes the hint's width; an `if` with an empty else arm
keeps an explicit `else` (`05 0B`) where the hint has one. Nested type vectors, the
table, element and data entries, the block types and the alignment exponents are
written as by `encodeModule?` (minimal).
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm

/-- A memory argument whose offset takes the hint's width at its position `pos + 1`
or later (after the alignment exponent). -/
def encMemArgP (hint : ByteArray) (pos : Nat) (x : MemIdx) (a : MemArg) :
    Except String (List UInt8) :=
  if x.toNat = 0 ∧ a.align.val < 64 ∧ a.offset.val < 2 ^ 32 then
    let al := encU a.align.val
    pure (al ++ padU32 hint (pos + al.length) a.offset.val)
  else throw "encoder: only memory 0, alignment exponents below 64 and 32-bit offsets"

mutual
/-- `encInstr` with the immediates padded to the widths of `hint` at output position
`pos` (the position of the opcode). -/
def encInstrP (hint : ByteArray) (pos : Nat) : Instr → Except String (List UInt8)
  | .block bt body => do
      let bt' ← encBlockType bt
      let b ← encInstrsP hint (pos + 1 + bt'.length) body
      pure ([0x02] ++ bt' ++ b ++ [0x0B])
  | .loop bt body => do
      let bt' ← encBlockType bt
      let b ← encInstrsP hint (pos + 1 + bt'.length) body
      pure ([0x03] ++ bt' ++ b ++ [0x0B])
  | .if_ bt t e => do
      let bt' ← encBlockType bt
      let t' ← encInstrsP hint (pos + 1 + bt'.length) t
      let e' ← encInstrsP hint (pos + 1 + bt'.length + t'.length + 1) e
      if e.isEmpty && hint[pos + 1 + bt'.length + t'.length]? != some 0x05 then
        pure ([0x04] ++ bt' ++ t' ++ [0x0B])
      else pure ([0x04] ++ bt' ++ t' ++ [0x05] ++ e' ++ [0x0B])
  | .br l => pure ([0x0C] ++ padIdx hint (pos + 1) l)
  | .throw x => pure ([0x08] ++ padIdx hint (pos + 1) x)
  | .brIf l => pure ([0x0D] ++ padIdx hint (pos + 1) l)
  | .call f => pure ([0x10] ++ padIdx hint (pos + 1) f)
  | .callIndirect x y => do pure ([0x11] ++ padIdx hint (pos + 1) y ++ (← encTableIdx x))
  | .localGet x => pure ([0x20] ++ padIdx hint (pos + 1) x)
  | .localSet x => pure ([0x21] ++ padIdx hint (pos + 1) x)
  | .localTee x => pure ([0x22] ++ padIdx hint (pos + 1) x)
  | .globalGet x => pure ([0x23] ++ padIdx hint (pos + 1) x)
  | .globalSet x => pure ([0x24] ++ padIdx hint (pos + 1) x)
  | .intLoad t p x a => do
      pure ([← intLoadOpcode t p] ++ (← encMemArgP hint (pos + 1) x a))
  | .intStore t p x a => do
      pure ([← intStoreOpcode t p] ++ (← encMemArgP hint (pos + 1) x a))
  | .intConst .i32 b => pure ([0x41] ++ padIN hint (pos + 1) 32 b.toInt)
  | .intConst .i64 b => pure ([0x42] ++ padIN hint (pos + 1) 64 b.toInt)
  | i => encInstr i
/-- `encInstrP` on a list starting at output position `pos`. -/
def encInstrsP (hint : ByteArray) (pos : Nat) : List Instr → Except String (List UInt8)
  | [] => pure []
  | i :: is => do
      let a ← encInstrP hint pos i
      pure (a ++ (← encInstrsP hint (pos + a.length) is))
end

/-- An expression at position `pos`: its instructions, then `end`. -/
def encExprP (hint : ByteArray) (pos : Nat) (e : Expr) : Except String (List UInt8) := do
  pure ((← encInstrsP hint pos e) ++ [0x0B])

/-- A checked `u32` padded to the hint's width. -/
def encU32P (hint : ByteArray) (pos n : Nat) : Except String (List UInt8) :=
  if n < 2 ^ 32 then pure (padU32 hint pos n)
  else throw s!"encoder: {n} does not fit in u32"

/-- The concatenated encodings of a list's elements, the first at position `pos`. -/
def encListP {α : Type} (f : Nat → α → Except String (List UInt8)) (pos : Nat) :
    List α → Except String (List UInt8)
  | [] => pure []
  | x :: xs => do
      let a ← f pos x
      pure (a ++ (← encListP f (pos + a.length) xs))

/-- A vector at position `pos`: its hint-padded length, then its elements. -/
def encVecP {α : Type} (hint : ByteArray) (f : Nat → α → Except String (List UInt8)) (pos : Nat)
    (xs : List α) : Except String (List UInt8) := do
  let n ← encU32P hint pos xs.length
  pure (n ++ (← encListP f (pos + n.length) xs))

/-- The value of the LEB128 at `pos` of `b` (at most 5 bytes, as a `u32`). -/
def lebVal (b : ByteArray) (pos : Nat) : Nat :=
  ((List.range (min (lebLen b pos) 5)).map fun k => (b[pos + k]!.toNat % 128) * 128 ^ k).sum

/-- The local groups of `ls` with the group counts of `hint` at `pos` (the vector
length, then per group a count and a type). Each group takes its type from `ls`; the
result is checked by `localGroupsP` and only shapes the output. -/
def hintGroups (hint : ByteArray) (pos : Nat) (ls : List ValType) :
    Option (List (Nat × ValType)) :=
  go (lebVal hint pos) (pos + min (lebLen hint pos) 5) ls
where
  go : Nat → Nat → List ValType → Option (List (Nat × ValType))
    | 0, _, [] => some []
    | 0, _, _ :: _ => none
    | _ + 1, _, [] => none
    | k + 1, p, t :: ts =>
      let c := lebVal hint p
      if c = 0 then none else
      match encValType t with
      | .ok tb => (go k (p + min (lebLen hint p) 5 + tb.length) (ts.drop (c - 1))).map ((c, t) :: ·)
      | .error _ => none

/-- The local groups of a code entry: those of the hint when they stand for exactly
`ls` (split runs, as linkers write them), else the run-length groups. -/
def localGroupsP (hint : ByteArray) (pos : Nat) (ls : List ValType) : List (Nat × ValType) :=
  match hintGroups hint pos ls with
  | some gs => if (gs.map fun p => List.replicate p.1 p.2).flatten = ls then gs else groupLocals ls
  | none => groupLocals ls

/-- The local declarations at position `pos`, grouped by `localGroupsP`, with the
hint's widths for the vector length and the group counts. -/
def encLocalsP (hint : ByteArray) (pos : Nat) (ls : List ValType) :
    Except String (List UInt8) :=
  encVecP hint (fun p (g : Nat × ValType) => do
      pure ((← encU32P hint p g.1) ++ (← encValType g.2)))
    pos (localGroupsP hint pos ls)

/-- A code entry at position `pos`: its size, then the compressed locals and the body. -/
def encCodeP (hint : ByteArray) (pos : Nat) (f : Func) : Except String (List UInt8) :=
  if f.locals.length < 2 ^ 32 then do
    let l ← encLocalsP hint (pos + min (lebLen hint pos) 5) f.locals
    let e ← encExprP hint (pos + min (lebLen hint pos) 5 + l.length) f.body
    let n ← encU32P hint pos (l ++ e).length
    pure (n ++ (l ++ e))
  else throw "encoder: a function has 2^32 or more locals"

/-- A section with id `n` at position `pos`; a section with no entries is omitted. The body is built at its position (after the id and the
size) by `body`. -/
def encSectionP (hint : ByteArray) (pos : Nat) (n : UInt8) (count : Nat)
    (body : Nat → Except String (List UInt8)) : Except String (List UInt8) :=
  if count = 0 then pure [] else do
    let c ← body (pos + 1 + min (lebLen hint (pos + 1)) 5)
    pure ([n] ++ (← encU32P hint (pos + 1) c.length) ++ c)

/-- A vector section, retaining an explicit empty section when it occurs at this
position in the hint. The hint controls representation only. -/
def encVecSectionP {α : Type} (hint : ByteArray) (pos : Nat) (n : UInt8)
    (f : Nat → α → Except String (List UInt8)) (xs : List α) :
    Except String (List UInt8) :=
  encSectionP hint pos n (if xs.isEmpty && hint[pos]? != some n then 0 else 1)
    fun p => encVecP hint f p xs

/-- **The padded encoder.** Section sizes, vector counts, code-entry sizes and
instruction immediates take the widths of `hint`, where their positions line up;
explicit empty vector sections and the data count section appear where `hint` has
them (the data count also when the code needs it). -/
def encodeModuleP? (hint : ByteArray) (m : Module) : Except String (List UInt8) := do
    let p1 := header.length
    let s1 ← encVecSectionP hint p1 1 (fun _ => encRecType) m.types
    let p2 := p1 + s1.length
    let s2 ← encVecSectionP hint p2 2 (fun _ => encImport) m.imports
    let p3 := p2 + s2.length
    let s3 ← encVecSectionP hint p3 3 (fun _ f => pure (encIdx f.type)) m.funcs
    let p4 := p3 + s3.length
    let s4 ← encVecSectionP hint p4 4 (fun _ => encTableWith encExpr) m.tables
    let p5 := p4 + s4.length
    let s5 ← encVecSectionP hint p5 5 (fun _ => encMemory) m.memories
    let p13 := p5 + s5.length
    let s13 ← encVecSectionP hint p13 13 (fun _ t => pure (encTagType t)) m.tags
    let p6 := p13 + s13.length
    let s6 ← encVecSectionP hint p6 6 (fun _ => encGlobal) m.globals
    let p7 := p6 + s6.length
    let s7 ← encVecSectionP hint p7 7 (fun _ => encExport) m.exports
    let p8 := p7 + s7.length
    let s8 ← encSectionP hint p8 8 (if m.start.isSome then 1 else 0) fun _ =>
      pure (encStart m.start)
    let p9 := p8 + s8.length
    let s9 ← encVecSectionP hint p9 9 (fun _ => encElem) m.elems
    let p12 := p9 + s9.length
    let s12 ← encSectionP hint p12 12
      (if hint[p12]? == some 12 || usesDataIdx m then 1 else 0) fun p =>
        encU32P hint p m.data.length
    let p10 := p12 + s12.length
    let s10 ← encVecSectionP hint p10 10 (encCodeP hint) m.funcs
    let p11 := p10 + s10.length
    let s11 ← encVecSectionP hint p11 11 (fun _ => encData) m.data
    pure (header ++ s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s13 ++ s6 ++ s7 ++ s8 ++ s9 ++ s12 ++ s10 ++ s11)

end Silmaril.Wasm.Binaryen.Exe

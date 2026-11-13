module

public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Data.IncludeBytes.Types
public import Silmaril.Wasm.Binary.Core.Decode
public meta import Silmaril.Data.IncludeBytes

/-!
# Chunked decode certificates: slices of an included file

A file included with `include_bytes` is the term `decode 4096 n [c₀, c₁, …]`, one 4 KiB
literal per chunk. Kernel decode certificates for files of hundreds of KB to MB cannot
evaluate a decoder on the whole byte list in one goal. Two costs grow with the file:
* walking the list to a position, or to its end;
* the cursor readers' `bs[i]`, linear in `i` on a list-backed array.

This module cuts the file into **slices** at offsets a generator chooses (component
sections, core sections, code entries), so each certificate evaluates one slice only:

* `slice l a b`: the bytes `a` to `b` of `l`; adjacent slices concatenate
  (`slice_append`), and the slices between consecutive cut points flatten to the list
  (`flatten_pieces`);
* `window c n cs a b`: the same slice of `decode c n cs`, computed from the chunk literals
  that overlap it (`slice_decode`), so the kernel decodes at most `b - a + 2c` bytes;
* `runAll p l`: a silmaril core reader run on exactly the bytes `l`. With the reader's
  `Sound` lemma it yields the grammar production on `l` (`runAll_sound`, in `Thms`).

The composition theorems are in `Silmaril.Wasm.Component.Chunked.Thms`:
* per-section certificates of a component give its parse (`parse_of_pieces`);
* raw frames give the framing of any component, async built-ins included
  (`frames_of_pieces`);
* per-function certificates of a code section give the section's grammar
  (`codeSec_of_pieces`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Chunked

open Silmaril.IncludeBytes

/-- The bytes `a` (inclusive) to `b` (exclusive) of `l`. -/
def slice (l : List UInt8) (a b : Nat) : List UInt8 := (l.drop a).take (b - a)

/-- The slices of `l` between consecutive cut points, from `a` to each point of `bs` in turn. -/
def pieces (l : List UInt8) : Nat → List Nat → List (List UInt8)
  | _, [] => []
  | a, b :: bs => slice l a b :: pieces l b bs

/-- The cut points are non-decreasing from `a`. -/
def sorted : Nat → List Nat → Bool
  | _, [] => true
  | a, b :: bs => decide (a ≤ b) && sorted b bs

/-- Every element of the list satisfies `P` (a conjunction that unfolds on a list literal). -/
def allP {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => P x ∧ allP P xs

/-- The last cut point (`a` when there is none). -/
def lastCut : Nat → List Nat → Nat
  | a, [] => a
  | _, b :: bs => lastCut b bs

/-- The pairs of consecutive cut points, from `a`. -/
def spans : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | a, b :: bs => (a, b) :: spans b bs

/-- The slice `a` to `b` of the file `decode c n cs`, from the chunks that overlap it: the
chunks before `a / c` are dropped as literals, without decoding them. -/
def window (c n : Nat) (cs : List Nat) (a b : Nat) : List UInt8 :=
  ((bytesChunks c (n - c * (a / c)) (cs.drop (a / c))).drop (a % c)).take (b - a)

/-! ## Silmaril core readers on a slice -/

open Silmaril.Wasm.Binary.Core.Decode (DecodeM Cursor)

/-- The array of a list, built with its constructors (no pushes). -/
def arr (l : List UInt8) : ByteArray := ⟨⟨l⟩⟩

/-- Run the reader `p` on exactly the bytes `l`: its value when it succeeds and consumes all
of them. -/
def runAll {α : Type} (p : DecodeM α) (l : List UInt8) : Option α :=
  match p.run ⟨arr l, 0⟩ with
  | .ok (a, c) => if c.pos = l.length then some a else none
  | .error _ => none

/-- The value of `runAll`, or `d` when it fails. -/
def runAllD {α : Type} (d : α) (p : DecodeM α) (l : List UInt8) : α := (runAll p l).getD d

/-! ## Raw component framing -/

/-- A component section as framed: its id and its body (any contents, known or not). -/
abbrev RawSection := UInt8 × List UInt8

open Silmaril.Parse.ByteParse (Bytes)

/-- The framing of one section: `id size:u32 body`, with a minimal LEB128 size. -/
def frameEnc (s : RawSection) : Option Bytes := (s.1 :: ·) <$> Silmaril.Parse.ByteParse.Enc.sized s.2

/-- The framings of the sections, concatenated (`none` when a body has `2 ^ 32` bytes or more). -/
def framesEnc : List RawSection → Option Bytes
  | [] => some []
  | s :: ss => do
    let a ← frameEnc s
    let b ← framesEnc ss
    pure (a ++ b)

/-- **A component framing**: the preamble, then the framed sections. -/
def framing (ss : List RawSection) : Option Bytes :=
  (Silmaril.Wasm.Component.Binary.preambleBytes ++ ·) <$> framesEnc ss

/-! ## Including a file as its chunk literals -/

open Lean Elab Term in
/-- `include_chunks c "path"`: the list `[c₀, c₁, …]` of the file's chunk literals for chunks of
`c` bytes, so that `bytesChunks c size [c₀, c₁, …]` is the file (`include_bytes "path"`
elaborates to `decode 4096 size [c₀, …]`, built by the same `Silmaril.IncludeBytes.includeExpr`
with `c = 4096`). Naming the list lets certificates refer to the file's slices through `window`
without restating the literals. A window decodes whole chunks, dividing a chunk literal by
`256` once per byte, so its cost grows with the square of the chunk size: certificates use
`c = 256` (a window costs milliseconds; 4 KiB chunks cost about a quarter of a second). -/
elab (name := includeChunks) "include_chunks " c:num path:str : term => do
  let b ← Silmaril.IncludeBytes.readRelative path.getString
  return (Silmaril.IncludeBytes.includeExpr b c.getNat).appArg!

/-- A silmaril core reader for the instructions of a slice: instructions (each an opcode and
`readInstr`) until the input ends. -/
def readInstrs : Nat → DecodeM (List Silmaril.Wasm.Instr)
  | 0 => pure []
  | fuel + 1 => do
    if (← Silmaril.Wasm.Binary.Core.Decode.remaining) = 0 then pure []
    else
      let b ← Silmaril.Wasm.Binary.Core.Decode.readByte
      let i ← Silmaril.Wasm.Binary.Core.Decode.readInstr fuel b.toNat
      let is ← readInstrs fuel
      pure (i :: is)

/-- Elements of `f` until the input ends (at most `fuel`). -/
def readAllOf {α : Type} (f : DecodeM α) : Nat → DecodeM (List α)
  | 0 => pure []
  | fuel + 1 => do
    if (← Silmaril.Wasm.Binary.Core.Decode.remaining) = 0 then pure []
    else
      let x ← f
      let xs ← readAllOf f fuel
      pure (x :: xs)

/-- One locals group, expanded (`readCode`'s group reader, then `List.replicate`). -/
def readLocalsGroup : DecodeM (List Silmaril.Wasm.ValType) := do
  let n ← Silmaril.Wasm.Binary.Core.Decode.readU 32
  let t ← Silmaril.Wasm.Binary.Core.Decode.readValType
  pure (List.replicate n t)

/-! ## Checkers driven by plans

A **plan** gives the lengths of the pieces of a byte range; a checker walks the bytes once,
decoding each piece with a silmaril reader on that piece alone (`runAll`), so the cursor
readers never see more than one piece. Every checker returns the decoded value and the rest of
the bytes; its soundness theorem (`Thms`) gives the grammar production on the bytes it consumed. -/

open Silmaril.Wasm in
/-- A plan for an instruction sequence (a sequence with a continuation, so the type is not
nested):
* `leaf k p`: `k` bytes of whole instructions, decoded by `readInstrs`, then `p`;
* `block k body p`: an instruction `op bt body 0x0B` with `op` `block`, `loop` or `if`
  (no `else`) and `k` bytes of `op bt`, then `p`;
* `ifElse k thn els p`: `0x04 bt thn 0x05 els 0x0B`, then `p`. -/
inductive IPlan where
  | nil
  | leaf (k : Nat) (p : IPlan)
  | block (k : Nat) (body : IPlan) (p : IPlan)
  | ifElse (k : Nat) (thn els : IPlan) (p : IPlan)
  deriving Repr, Inhabited

open Silmaril.Wasm Silmaril.Wasm.Binary.Core.Decode in
/-- The structured instruction `op bt body 0x0B` of a `block` plan. -/
def blockInstr (op : UInt8) (bt : BlockType) (body : List Instr) : Option Instr :=
  if op = 0x02 then some (.block bt body)
  else if op = 0x03 then some (.loop bt body)
  else if op = 0x04 then some (.if_ bt body [])
  else none

open Silmaril.Wasm Silmaril.Wasm.Binary.Core.Decode in
/-- **The instruction checker**: the instructions of `p` from the front of `r`, and the rest. -/
def chkI : IPlan → List UInt8 → Option (List Instr × List UInt8)
  | .nil, r => some ([], r)
  | .leaf k p, r =>
    match runAll (readInstrs (k + 1)) (r.take k) with
    | some is => (chkI p (r.drop k)).map fun q => (is ++ q.1, q.2)
    | none => none
  | .block k body p, r =>
    match r with
    | op :: r₁ =>
      match runAll readBlockType (r₁.take (k - 1)), chkI body (r₁.drop (k - 1)) with
      | some bt, some (is, 0x0B :: r₂) =>
        match blockInstr op bt is with
        | some i => (chkI p r₂).map fun q => (i :: q.1, q.2)
        | none => none
      | _, _ => none
    | [] => none
  | .ifElse k thn els p, r =>
    match r with
    | op :: r₁ =>
      if op = 0x04 then
        match runAll readBlockType (r₁.take (k - 1)), chkI thn (r₁.drop (k - 1)) with
        | some bt, some (is₁, 0x05 :: r₂) =>
          match chkI els r₂ with
          | some (is₂, 0x0B :: r₃) => (chkI p r₃).map fun q => (.if_ bt is₁ is₂ :: q.1, q.2)
          | _ => none
        | _, _ => none
      else none
    | [] => none

/-- A plan for a code entry: the bytes of its size, of its locals vector, and its body
(the expression without its final `0x0B`). -/
structure CPlan where
  kSize : Nat
  kLocals : Nat
  body : IPlan
  deriving Repr, Inhabited

open Silmaril.Wasm Silmaril.Wasm.Binary.Core.Decode in
/-- **The code entry checker**: `len:u32` then exactly `len` bytes of locals, body and `0x0B`. -/
def chkCode (p : CPlan) (r : List UInt8) : Option ((List ValType × Expr) × List UInt8) :=
  match runAll (readU 32) (r.take p.kSize) with
  | some len =>
    let c := (r.drop p.kSize).take len
    if c.length = len then
      match runAll (readVec readLocalsGroup) (c.take p.kLocals), chkI p.body (c.drop p.kLocals) with
      | some lss, some (is, [0x0B]) =>
        if lss.flatten.length < 2 ^ 32 then some ((lss.flatten, is), (r.drop p.kSize).drop len)
        else none
      | _, _ => none
    else none
  | none => none

open Silmaril.Wasm in
/-- Code entries, one plan each. -/
def chkCodes : List CPlan → List UInt8 → Option (List (List ValType × Expr) × List UInt8)
  | [], r => some ([], r)
  | p :: ps, r =>
    match chkCode p r with
    | some (c, r₁) => (chkCodes ps r₁).map fun q => (c :: q.1, q.2)
    | none => none

open Silmaril.Wasm in
/-- The code entries of the bytes `r` under the plans `ps`, when they consume all of `r`. -/
def codesOf (ps : List CPlan) (r : List UInt8) : List (List ValType × Expr) :=
  match chkCodes ps r with
  | some (cs, []) => cs
  | _ => []

/-- The check behind `codesOf`, as a `Bool` for `decide`: the entries consume all of `r` and
mention no data index (the module rule's side condition when there is no data count
section). -/
def codesOk (ps : List CPlan) (r : List UInt8) : Bool :=
  match chkCodes ps r with
  | some (cs, []) => Silmaril.Wasm.Binary.Core.codesDataIdxs cs = []
  | _ => false

/-- Elements of `f`, in pieces of the given lengths, each piece decoded alone. -/
def chkSeq {α : Type} (f : DecodeM α) : List Nat → List UInt8 → Option (List α × List UInt8)
  | [], r => some ([], r)
  | k :: ks, r =>
    match runAll (readAllOf f (k + 1)) (r.take k) with
    | some xs => (chkSeq f ks (r.drop k)).map fun q => (xs ++ q.1, q.2)
    | none => none

/-- A vector `n:u32 el*` whose count takes `kCount` bytes and whose elements come in pieces
of lengths `ks`: the elements, when they consume all of `r` and there are `n` of them. -/
def chkVec {α : Type} (f : DecodeM α) (kCount : Nat) (ks : List Nat) (r : List UInt8) :
    Option (List α) :=
  match runAll (Silmaril.Wasm.Binary.Core.Decode.readU 32) (r.take kCount),
      chkSeq f ks (r.drop kCount) with
  | some n, some (xs, []) => if xs.length = n then some xs else none
  | _, _ => none

/-- A section `N size:u32 contents` whose size takes `kSize` bytes, with contents checked by
`inner`. -/
def chkSection {α : Type} (N : UInt8) (kSize : Nat) (inner : List UInt8 → Option α)
    (r : List UInt8) : Option α :=
  match r with
  | id :: r₁ =>
    if id = N then
      match runAll (Silmaril.Wasm.Binary.Core.Decode.readU 32) (r₁.take kSize) with
      | some len => if (r₁.drop kSize).length = len then inner (r₁.drop kSize) else none
      | none => none
    else none
  | [] => none

open Silmaril.Wasm Silmaril.Wasm.Binary.Core in
/-- An active data segment for memory 0 (kind `0`): `kKind`, `kExpr` and `kLen` bytes of its
kind, offset expression and length, then its bytes, which are kept, not read. -/
def chkData0 (kKind kExpr kLen : Nat) (r : List UInt8) : Option (Data × List UInt8) :=
  match runAll (Decode.readU 32) (r.take kKind),
      runAll Decode.readExpr ((r.drop kKind).take kExpr),
      runAll (Decode.readU 32) (((r.drop kKind).drop kExpr).take kLen) with
  | some 0, some e, some n =>
    let bs := (((r.drop kKind).drop kExpr).drop kLen).take n
    if bs.length = n then
      some (⟨dataBytes bs, .active ⟨0⟩ e⟩, (((r.drop kKind).drop kExpr).drop kLen).drop n)
    else none
  | _, _, _ => none

open Silmaril.Wasm in
/-- Kind-`0` data segments, one `(kKind, kExpr, kLen)` triple each. -/
def chkDatas : List (Nat × Nat × Nat) → List UInt8 → Option (List Data × List UInt8)
  | [], r => some ([], r)
  | (a, b, c) :: ps, r =>
    match chkData0 a b c r with
    | some (d, r₁) => (chkDatas ps r₁).map fun q => (d :: q.1, q.2)
    | none => none

open Silmaril.Wasm in
/-- A data section's contents: `n:u32` (in `kCount` bytes), then `n` kind-`0` segments. -/
def chkDataVec (kCount : Nat) (ps : List (Nat × Nat × Nat)) (r : List UInt8) : Option (List Data) :=
  match runAll (Silmaril.Wasm.Binary.Core.Decode.readU 32) (r.take kCount),
      chkDatas ps (r.drop kCount) with
  | some n, some (ds, []) => if ds.length = n then some ds else none
  | _, _ => none

/-- A custom section `0 size:u32 name bytes` whose size and name take `kSize` and `kName`
bytes (the rest of its contents is not read). -/
def chkCustom (kSize kName : Nat) (r : List UInt8) : Bool :=
  (chkSection 0 kSize (fun c => runAll Silmaril.Wasm.Binary.Core.Decode.readName (c.take kName))
    r).isSome

end Silmaril.Wasm.Component.Chunked

end

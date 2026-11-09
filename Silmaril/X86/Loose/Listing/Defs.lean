module

public import Silmaril.X86.Loose.Decode.Defs
public import Silmaril.X86.Str9.Defs

/-!
# Image listings and their loose decode tables

The loose machine (`X86Loose`) reads an image through an address-free decode table
`DTable Φ`. This module builds such a table from a **listing**: the image's instructions,
written as indices into a sorted list of distinct byte strings, and states the decidable
checks that tie the listing to the image's bytes. The theorems are in `Listing/Thms.lean`;
nothing here is trusted, since every fact a consumer uses is a `decide` over these
definitions.

* `LForm`: the form index of a listing. It extends the loose form index `Form`
  (`int Ext9.Instr | xmm Sse9.Instr | float Float.Instr`) by the string forms of `Str9`
  (`movsb`, `rep movsq`, `rep stosq`) and by `unmodelled` for listed bytes that no decoder
  reads (`syscall`, `hlt`). `X86Loose` is parametric in `Φ`, so any `Sigma LForm` can be
  used; an `unmodelled` entry is meant to be unspecified (`none`), which allows every outcome
  there.
* `classify b`: **the form is computed from the bytes** by the decoders, in the order
  `Ext9.decode`, `Sse9.decodeL`, `Str9.decodeL`, `Float.decode`, each only at the full length
  of `b`. So `table bs` is functional by construction, and its `loose` part passes `okExt9`,
  `okSse9` and `okFloat` without a `decide` (`Listing/Thms.lean`).
* `table bs`: one entry per byte string of `bs`. `loosePart` keeps the `Form` entries;
  `str9Part` keeps the integer and string entries over `Str9.Instr`, the form index of
  `Σ v1` (`Loose.Sv1`) and `Σexact` (`Exact.Sig.exact`), so a listing's table is a signature
  of the x86 institution (`Exact.str9Model` applies once `DTable.decodes Str9.isa` of it is
  decided).
* `tableOk bs`: every byte string is non-empty with byte values below 256, and `bs` is
  strictly increasing in the lexicographic order `lexLt` with no element a prefix of its
  successor (`sortedAdj`). This linear check implies `prefixFree`, a quadratic check that is
  too slow in the kernel for tables of a few thousand strings.
* `FnListing`: a function's instructions from its start address, as `(bucket, position)`
  indices into the byte strings given in buckets (`bs.flatten` is the table's list);
  `FnListing.check` walks the image bytes once and compares each instruction's bytes;
  `FnListing.items` gives each instruction's `(address, bytes)`.
-/

@[expose] public section

namespace Silmaril.X86.Loose.Listing

open Silmaril.X86 (Byte)

/-- The form index of an image listing: a loose form, a `Str9` string form, or bytes that
no decoder reads. -/
inductive LForm where
  | loose (f : Form)
  | str (s : Silmaril.X86.Str9.Str)
  | unmodelled
  deriving DecidableEq

/-- A decoder's result, kept only when it consumed exactly `n` bytes. -/
def full {α : Type} (n : Nat) : Option (α × Nat) → Option α
  | some (a, k) => if k = n then some a else none
  | none => none

/-- **The form of a byte string**, read by the decoders at its full length: `Ext9`, then the
`Sse9` listing decoder, then a `Str9` string form, then `Silmaril.X86.Float`. -/
def classify (b : List Byte) : LForm :=
  match full b.length (Silmaril.X86.Ext9.decode b) with
  | some i => .loose (.int i)
  | none =>
    match full b.length (Silmaril.X86.Sse9.decodeL b) with
    | some i => .loose (.xmm i)
    | none =>
      match full b.length (Silmaril.X86.Str9.decodeL b) with
      | some s => .str s
      | none =>
        match full b.length (Silmaril.X86.Float.decode b) with
        | some i => .loose (.float i)
        | none => .unmodelled

/-- Byte values as bytes. -/
def toBytes (b : List Nat) : List Byte := b.map (BitVec.ofNat 8)

/-- The table entry of a byte string: its bytes and their form. -/
def entryOf (b : List Nat) : DEntry LForm := ⟨toBytes b, classify (toBytes b)⟩

/-- **The decode table of a listing**: one entry per byte string. -/
def table (bs : List (List Nat)) : DTable LForm := bs.map entryOf

/-- The `loose` part of a table, as a table over the loose form index `Form`. -/
def loosePart (D : DTable LForm) : DTable Form :=
  D.filterMap fun e => match e.form with
    | .loose f => some ⟨e.bytes, f⟩
    | _ => none

/-- **The `Str9` part of a table**: the integer and string entries, over `Str9.Instr` (the
form index of `Σ v1` and `Σexact`). SSE, floating-point and unmodelled entries are dropped,
so the loose machine of this part is unconstrained there (`X86Loose.antitone_D`). -/
def str9Part (D : DTable LForm) : DTable Silmaril.X86.Str9.Instr :=
  D.filterMap fun e => match e.form with
    | .loose (.int i) => some ⟨e.bytes, .ext9 i⟩
    | .str s => some ⟨e.bytes, .str s⟩
    | _ => none

/-! ## The table check -/

/-- Strict lexicographic order on byte strings (a proper prefix comes first). -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a < b) || (decide (a = b) && lexLt as bs)

/-- Strictly increasing, and no element is a prefix of its successor. -/
def sortedAdj : List (List Nat) → Bool
  | x :: y :: rest => lexLt x y && !x.isPrefixOf y && sortedAdj (y :: rest)
  | _ => true

/-- **The table check**: non-empty strings of byte values, sorted, adjacent strings not
prefixes. Linear in the table. -/
def tableOk (bs : List (List Nat)) : Bool :=
  bs.all (fun b => !b.isEmpty && b.all (· < 256)) && sortedAdj bs

/-! ## Function listings

The byte strings are given in **buckets** (`List (List (List Nat))`, the table being their
`flatten`), and an instruction names its string by `(bucket, position)`: the kernel then
walks two short lists per instruction instead of one long one. -/

/-- The byte string at `(i, j)` (empty when out of range). -/
def at2 (bs : List (List (List Nat))) (ij : Nat × Nat) : List Nat :=
  (bs.getD ij.1 []).getD ij.2 []

/-- A function's listing: its name, the address of its first instruction, and its
instructions in address order as `(bucket, position)` indices into the byte strings. -/
structure FnListing where
  name : String
  start : Nat
  instrs : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- `rest` with the prefix `p` removed, if `p` is a prefix of it. Written by structural
recursion on both lists, so that the kernel never builds nested `drop`s. -/
def stripPrefix : List Nat → List Nat → Option (List Nat)
  | [], rest => some rest
  | _ :: _, [] => none
  | a :: as, b :: bs => if a = b then stripPrefix as bs else none

/-- Walk the image bytes from an instruction start: each index names a byte string of `bs`
that is the next bytes of the image. -/
def walk (bs : List (List (List Nat))) : List Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | rest, ij :: ks =>
    decide (ij.1 < bs.length) && decide (ij.2 < (bs.getD ij.1 []).length) &&
      match stripPrefix (at2 bs ij) rest with
      | some rest' => walk bs rest' ks
      | none => false

/-- The listing of `f` is the image `img` (placed at `base`) from `f.start` on. -/
def FnListing.check (img : List Nat) (base : Nat) (bs : List (List (List Nat)))
    (f : FnListing) : Bool :=
  decide (base ≤ f.start) && walk bs (img.drop (f.start - base)) f.instrs

/-- `walk` that also returns the bytes left and the number consumed. -/
def walkR (bs : List (List (List Nat))) : List Nat → List (Nat × Nat) → Option (List Nat × Nat)
  | rest, [] => some (rest, 0)
  | rest, ij :: ks =>
    if ij.1 < bs.length ∧ ij.2 < (bs.getD ij.1 []).length then
      match stripPrefix (at2 bs ij) rest with
      | some rest' => (walkR bs rest' ks).map fun p => (p.1, (at2 bs ij).length + p.2)
      | none => none
    else none

/-- Check listings in address order in **one pass** over the image: `cur` is the address of
`rest`, the image from there on. Equivalent to `FnListing.check` on each listing
(`checkAll_sound`), without walking the image from its start once per listing. -/
def checkFrom (bs : List (List (List Nat))) : Nat → List Nat → List FnListing → Bool
  | _, _, [] => true
  | cur, rest, f :: fs =>
    decide (cur ≤ f.start) &&
      match walkR bs (rest.drop (f.start - cur)) f.instrs with
      | some (rest', n) => checkFrom bs (f.start + n) rest' fs
      | none => false

/-- Check every listing of `fns` (in address order) against the image `img` at `base`. -/
def checkAll (bs : List (List (List Nat))) (img : List Nat) (base : Nat) (fns : List FnListing) :
    Bool :=
  checkFrom bs base img fns

/-- The `(address, bytes)` of each instruction, from address `a`. -/
def itemsFrom (bs : List (List (List Nat))) : Nat → List (Nat × Nat) → List (Nat × List Nat)
  | _, [] => []
  | a, ij :: ks => (a, at2 bs ij) :: itemsFrom bs (a + (at2 bs ij).length) ks

/-- The `(address, bytes)` of each instruction of `f`. -/
def FnListing.items (bs : List (List (List Nat))) (f : FnListing) : List (Nat × List Nat) :=
  itemsFrom bs f.start f.instrs

/-- The instruction addresses of `f`. -/
def FnListing.addrs (bs : List (List (List Nat))) (f : FnListing) : List Nat :=
  (f.items bs).map Prod.fst

end Silmaril.X86.Loose.Listing

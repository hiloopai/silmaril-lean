module

/-!
# Reading DWARF sections

A little-endian byte reader over a section (a `ByteArray`) as gimli 0.34's `EndianSlice`
reads it: fixed-size integers, LEB128 (`read_uleb128`, `read_sleb128`: at most 64 bits, gimli's
`BadUnsignedLeb128`/`BadSignedLeb128` beyond), null-terminated strings, initial lengths
(32-bit, or `0xffffffff` and a 64-bit length: the 64-bit DWARF format), addresses of 1, 2, 4 or
8 bytes, and sub-readers (`split`).

Errors carry gimli's `Display` text (`Error::description`).

Tested through `addr2line` (`tools/wasm-tools/tests/addr2line/differential.sh`), not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Dwarf

/-- gimli's error texts. -/
def errEof : String := "Hit the end of input before it was expected"
def errLeb : String := "An error parsing an unsigned LEB128 value"
def errSLeb : String := "An error parsing a signed LEB128 value"

/-- A reader: the bytes, the end of the readable range, and the position (a state). -/
abbrev DR := ReaderT (ByteArray × Nat) (StateT Nat (Except String))

def DR.run' {α : Type} (m : DR α) (d : ByteArray) (pos lim : Nat) : Except String (α × Nat) :=
  (m.run (d, lim)).run pos

def pos : DR Nat := get
def lim : DR Nat := do pure (← read).2
def left : DR Nat := do pure ((← lim) - (← pos))
def isEmpty : DR Bool := do pure ((← left) == 0)

/-- Skip `n` bytes. -/
def skip (n : Nat) : DR Unit := do
  if (← left) < n then throw errEof
  modify (· + n)

/-- One byte. -/
def u8 : DR Nat := do
  let p ← pos
  if (← lim) ≤ p then throw errEof
  set (p + 1)
  pure ((← read).1.get! p).toNat

/-- A little-endian unsigned integer of `n` bytes. -/
def uN (n : Nat) : DR Nat := do
  let p ← pos
  if (← lim) < p + n then throw errEof
  set (p + n)
  let d := (← read).1
  pure ((List.range n).foldr (fun i acc => acc * 256 + (d.get! (p + i)).toNat) 0)

def u16 : DR Nat := uN 2
def u32 : DR Nat := uN 4
def u64 : DR Nat := uN 8

/-- `read_uleb128`. -/
def uleb : DR Nat := do
  let mut r := 0
  let mut shift := 0
  for _ in [0:(← left) + 1] do
    let b ← u8
    if shift == 63 && b != 0 && b != 1 then throw errLeb
    r := r + (b % 128) * 2 ^ shift
    shift := shift + 7
    if b < 128 then return r % 2 ^ 64
  throw errEof

/-- `read_sleb128`: a two's-complement value as an `Int`. -/
def sleb : DR Int := do
  let mut r := 0
  let mut shift := 0
  for _ in [0:(← left) + 1] do
    let b ← u8
    if shift == 63 && b != 0 && b != 0x7f then throw errSLeb
    r := r + (b % 128) * 2 ^ shift
    shift := shift + 7
    if b < 128 then
      if shift < 64 && b / 64 % 2 == 1 then return Int.ofNat r - Int.ofNat (2 ^ shift)
      else return Int.ofNat (r % 2 ^ 64) - (if r % 2 ^ 64 ≥ 2 ^ 63 then 2 ^ 64 else 0)
  throw errEof

/-- A signed byte. -/
def i8 : DR Int := do let b ← u8; pure (if b < 128 then b else Int.ofNat b - 256)

/-- A null-terminated string: its bytes (without the terminator). -/
def cstr : DR ByteArray := do
  let p ← pos
  let l ← lim
  let d := (← read).1
  let mut i := p
  for _ in [0:l - p + 1] do
    if l ≤ i then throw errEof
    if d.get! i == 0 then break
    i := i + 1
  set (i + 1)
  pure (d.extract p i)

/-- `read_initial_length`: the length and whether the format is 64-bit. -/
def initialLength : DR (Nat × Bool) := do
  let n ← u32
  if n == 0xffffffff then pure (← u64, true)
  else if n ≥ 0xfffffff0 then throw "Found an unknown reserved length value"
  else pure (n, false)

/-- An offset of the format's size. -/
def offset (dwarf64 : Bool) : DR Nat := if dwarf64 then u64 else u32

/-- An address of `size` bytes. -/
def address (size : Nat) : DR Nat := do
  if size ∈ [1, 2, 4, 8] then uN size else throw "The specified address size is not supported"

/-- Run `m` on the next `n` bytes and continue after them (`split`). -/
def sub {α : Type} (n : Nat) (m : DR α) : DR α := do
  let p ← pos
  if (← left) < n then throw errEof
  let d := (← read).1
  match (m.run (d, p + n)).run p with
  | .ok (a, _) => set (p + n); pure a
  | .error e => throw e

/-- The all-ones value of an address size (`ones_sized`). -/
def onesSized (size : Nat) : Nat := 2 ^ (8 * size) - 1

/-- `wrapping_add_sized`. -/
def addSized (a b size : Nat) : Nat := (a + b) % 2 ^ (8 * size)

/-- `min_tombstone`: the all-ones address minus one. -/
def minTombstone (size : Nat) : Nat := onesSized size - 1

/-- The loop of `binarySearch`: at most `k` halvings of the window `[base, base + size)`,
stopping at size 1. -/
def bsLoop {α : Type} [Inhabited α] (xs : Array α) (cmp : α → Ordering) : Nat → Nat → Nat → Nat × Nat
  | 0, base, size => (base, size)
  | k + 1, base, size =>
    if size ≤ 1 then (base, size) else
    let half := size / 2
    let mid := base + half
    bsLoop xs cmp k (if cmp xs[mid]! == .gt then base else mid) (size - half)

/-- Rust's `slice::binary_search_by` (the branch-free loop of Rust 1.80 and later, at most 64
halvings), on a comparison returning less, equal, greater: `ok i` or `error i`. Its
specification is `binarySearch_spec` (`Silmaril.Wasm.Tools.Dwarf.Line.Thms`). -/
def binarySearch {α : Type} [Inhabited α] (xs : Array α) (cmp : α → Ordering) : Except Nat Nat :=
  if xs.size == 0 then .error 0 else
  let base := (bsLoop xs cmp 64 0 xs.size).1
  let c := cmp xs[base]!
  if c == .eq then .ok base else .error (base + (if c == .lt then 1 else 0))

end Silmaril.Wasm.Tools.Dwarf

end

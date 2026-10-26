module

public import Silmaril.Data.IncludeBytes
public import Silmaril.Formats.ELF.Reader
public meta import Lean.Elab.Command

/-! # Pinned binary images

`binary_image foo from "path" sha256 "…"` is the Lean analogue of LPS's `elf-snapshot` plus
`rocq-read-file`: it reads a file at elaboration time, checks its SHA-256 against the pin, and
defines

```
noncomputable def foo : Silmaril.BinaryImage := { chunk := 4096, size := N, chunks := […], sha256 := "…" }
theorem foo.wf : foo.WF
theorem foo.bytes_size_eq : foo.bytes.size = N
```

where `chunks` holds one `Nat` literal per 4 KiB of the file (`Silmaril.IncludeBytes`, the
encoding measured cheapest there). With the `elf` flag the command also proposes, and proves in
the kernel, the ELF64 header, program headers, section headers and section names
(`Silmaril.BinaryImage.Elf`).

## What the kernel sees

The formal object is the structure literal: its `Nat` literals *are* the bytes. Every theorem
about `foo` is a theorem about those literals. Three views connect them to the rest of
Silmaril:

* `foo.bytes : ByteArray` and `foo.bits : Silmaril.Formats.ELF.Bytes` (`Array (BitVec 8)`, the
  type of the ELF readers and the RV64 loader) decode the literals with `IncludeBytes.decode`.
  They are definitions, so statements can use them, but reducing them in the kernel walks the
  file from the start.
* `foo.byte i` reads byte `i` directly: the `i / 4096`-th literal shifted right by
  `8 * (i % 4096)` bits, modulo 256. The kernel accelerates `Nat.shiftRight` and `Nat.mod` on
  literals with GMP, so this costs one walk of the chunk list (at most 256 cells per MiB) and
  two big-number operations, wherever `i` is in the file.
* The bridge lemmas `getElem?_bits`, `size_bits`, `readLE_bits` and `slice_bits` rewrite the
  `bits` view into `byte` reads (`simp only [Formats.ELF.readHeader, foo.readLE_bits …]`
  followed by `decide +kernel` is how the ELF facts are proved).

## Trust

Reading the file at elaboration time is the same step as Rocq's `rocq-read-file`: the elaborator
is trusted to put the file's bytes in the literal. The pin makes that step checkable *outside*
Lean: anyone can recompute the SHA-256 of the file named in the source and compare it with the
pin, and the elaborator refuses to build if they differ. What the elaborator does not do is
prove, in the kernel, that the literal hashes to the pin; `foo.sha256` is recorded data. For a
small file the kernel can check it (`BinaryImage.sha256Hex` against
`Silmaril.Crypto.SHA256.digest`); see the measurements in
`/srv/scratch/campaigns/research/low-hanging/embed.md` and `Silmaril.Data.BinaryImageExamples`.

The SHA-256 used at elaboration time (`sha256Meta`) is a separate `ByteArray` implementation,
because the list-based specification takes about 50 s per MiB in the interpreter. It is not
trusted for any theorem: a wrong implementation could only accept a wrong pin, never change the
literal or a theorem about it.

## Lake dependency tracking

As for `include_bytes`, Lake does not see the file; touch the including module after changing
the file (the pin then forces an update of the source anyway).
-/

@[expose] public section

namespace Silmaril

/-- A file's bytes as `chunk`-byte little-endian `Nat` literals (`IncludeBytes.decode`), with
the file size and the SHA-256 pin it was built against (recorded, not checked by the kernel). -/
structure BinaryImage where
  chunk : Nat
  size : Nat
  chunks : List Nat
  sha256 : String

namespace BinaryImage

open Silmaril.IncludeBytes

/-- The literals cover the file. -/
def WF (img : BinaryImage) : Prop := 0 < img.chunk ∧ img.size ≤ img.chunk * img.chunks.length

instance (img : BinaryImage) : Decidable img.WF := inferInstanceAs (Decidable (_ ∧ _))

/-- The file's bytes. -/
def bytes (img : BinaryImage) : ByteArray := decode img.chunk img.size img.chunks

/-- The file's bytes in the representation of `Silmaril.Formats.ELF`. -/
def bits (img : BinaryImage) : Formats.ELF.Bytes := ⟨img.bytes.data.toList.map UInt8.toBitVec⟩

/-- Byte `i`, read directly from its chunk literal (kernel cost independent of `i`, up to the
chunk-list walk). Meaningful for `i < img.size`. -/
def byte (img : BinaryImage) (i : Nat) : Nat :=
  (img.chunks.getD (i / img.chunk) 0 >>> (8 * (i % img.chunk))) % 256

/-- Byte `i`, if it is in the file. -/
def byte? (img : BinaryImage) (i : Nat) : Option Nat :=
  if i < img.size then some (img.byte i) else none

/-- `Formats.ELF.readLE` against `byte?`. -/
def readLE (img : BinaryImage) (offset : Nat) : Nat → Option Nat
  | 0 => some 0
  | width + 1 => do
    let b ← img.byte? offset
    let rest ← img.readLE (offset + 1) width
    pure (b + 256 * rest)

/-- The `n` bytes from `offset`, as the `BitVec 8` list a transcription records. -/
def window (img : BinaryImage) (offset n : Nat) : List (BitVec 8) :=
  (List.range n).map fun k => BitVec.ofNat 8 (img.byte (offset + k))

/-- The NUL-terminated string at `offset` (at most `fuel` bytes, without the NUL). -/
def cstr (img : BinaryImage) (offset : Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 =>
    match img.byte? offset with
    | some 0 | none => []
    | some b => b :: img.cstr (offset + 1) fuel

/-! ## Decoding lemmas -/

theorem getElem?_bytesLE : ∀ (k n i : Nat), i < k →
    (bytesLE k n)[i]? = some (UInt8.ofNat (n / 256 ^ i))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, 0, _ => by simp [bytesLE_succ]
  | k + 1, n, i + 1, h => by
    rw [bytesLE_succ, List.getElem?_cons_succ, getElem?_bytesLE k (n / 256) i (by omega),
      Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ i) 256]

theorem length_bytesChunks (chunk : Nat) : ∀ (len : Nat) (cs : List Nat),
    (bytesChunks chunk len cs).length = min len (chunk * cs.length)
  | len, [] => by simp [bytesChunks_nil]
  | len, c :: cs => by
    rw [bytesChunks_cons, List.length_append, length_bytesLE, length_bytesChunks chunk _ cs,
      List.length_cons, Nat.mul_succ]
    omega

theorem getElem?_bytesChunks {chunk : Nat} (hc : 0 < chunk) : ∀ (len : Nat) (cs : List Nat)
    (i : Nat), i < len → i < chunk * cs.length →
    (bytesChunks chunk len cs)[i]? =
      some (UInt8.ofNat (cs.getD (i / chunk) 0 / 256 ^ (i % chunk)))
  | len, [], i, _, h => by simp at h
  | len, c :: cs, i, hl, h => by
    rw [bytesChunks_cons]
    by_cases hi : i < chunk
    · rw [List.getElem?_append_left (by rw [length_bytesLE]; omega),
        getElem?_bytesLE _ _ _ (by omega), Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      rfl
    · have hmin : min chunk len = chunk := by omega
      rw [List.getElem?_append_right (by rw [length_bytesLE]; omega), length_bytesLE, hmin,
        getElem?_bytesChunks hc (len - chunk) cs (i - chunk) (by omega)
          (by rw [List.length_cons, Nat.mul_succ] at h; omega)]
      have hi' : i = (i - chunk) + chunk := by omega
      conv => rhs; rw [hi', Nat.add_div_right _ hc, Nat.add_mod_right]
      rfl

theorem ofNat_div_pow (n j : Nat) :
    UInt8.ofNat (n / 256 ^ j) = UInt8.ofNat ((n >>> (8 * j)) % 256) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]
  show _ = UInt8.ofNat (n / (2 ^ 8) ^ j % 2 ^ 8)
  rw [UInt8.ofNat_mod_size]
  rfl

theorem byte_lt (img : BinaryImage) (i : Nat) : img.byte i < 256 := Nat.mod_lt _ (by decide)

variable {img : BinaryImage}

theorem size_data (h : img.WF) : img.bytes.data.toList.length = img.size := by
  show (bytesChunks img.chunk img.size img.chunks).length = img.size
  rw [length_bytesChunks]
  exact Nat.min_eq_left h.2

/-- `bytes` has the recorded size. -/
theorem size_bytes (h : img.WF) : img.bytes.size = img.size := by
  rw [ByteArray.size, ← Array.length_toList]
  exact size_data h

/-- Byte `i` of `bytes` is `byte i`. -/
theorem getElem?_data (h : img.WF) (i : Nat) :
    img.bytes.data.toList[i]? = (img.byte? i).map UInt8.ofNat := by
  unfold byte?
  split
  · rename_i hi
    show (bytesChunks img.chunk img.size img.chunks)[i]? = _
    rw [getElem?_bytesChunks h.1 _ _ _ hi (Nat.lt_of_lt_of_le hi h.2), ofNat_div_pow]
    rfl
  · rename_i hi
    rw [List.getElem?_eq_none (by rw [size_data h]; omega)]
    rfl

theorem size_bits (h : img.WF) : img.bits.size = img.size := by
  rw [bits, Array.size, List.length_map]
  exact size_data h

theorem getElem?_bits (h : img.WF) (i : Nat) :
    img.bits.toList[i]? = (img.byte? i).map (BitVec.ofNat 8) := by
  show (img.bytes.data.toList.map UInt8.toBitVec)[i]? = _
  rw [List.getElem?_map, getElem?_data h, Option.map_map]
  rfl

theorem toNat_ofNat_byte (i : Nat) : (BitVec.ofNat 8 (img.byte i)).toNat = img.byte i := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (img.byte_lt i)

/-- The ELF readers' `readLE` on `bits` is `readLE` on the chunk literals. -/
theorem readLE_bits (h : img.WF) : ∀ (offset width : Nat),
    Formats.ELF.readLE img.bits offset width = img.readLE offset width
  | _, 0 => rfl
  | offset, width + 1 => by
    simp only [Formats.ELF.readLE, readLE, getElem?_bits h, readLE_bits h (offset + 1) width]
    unfold byte?
    split <;> simp [Nat.mod_eq_of_lt (img.byte_lt offset)]

/-- A file-backed slice of `bits` is a `window` of byte reads. -/
theorem slice_bits (h : img.WF) (offset n : Nat) :
    Formats.ELF.slice img.bits offset n =
      if offset + n ≤ img.size then some ⟨img.window offset n⟩ else none := by
  simp only [Formats.ELF.slice, size_bits h]
  by_cases hs : offset + n ≤ img.size
  · simp only [hs, ite_true, guard]
    show some (⟨(img.bits.toList.drop offset).take n⟩ : Formats.ELF.Bytes) = _
    refine congrArg some (congrArg Array.mk ?_)
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_take, List.getElem?_drop, window, List.getElem?_map]
    by_cases hk : k < n
    · rw [ite_eq_left hk, getElem?_bits h, List.getElem?_range hk]
      unfold byte?
      rw [ite_eq_left (by omega)]
      rfl
    · rw [ite_eq_right hk, List.getElem?_eq_none (by simp; omega)]
      rfl
  · simp [hs]

/-- The window of `bits` from `offset`, as a list. -/
theorem window_eq (h : img.WF) (offset n : Nat) (hs : offset + n ≤ img.size) :
    ((img.bits.toList.drop offset).take n) = img.window offset n := by
  have := slice_bits h offset n
  simp only [Formats.ELF.slice, size_bits h, hs, ite_true, guard] at this
  exact Array.mk.inj (Option.some.inj this)

/-! ## Elaboration -/

/-- SHA-256 on a `ByteArray`, for checking pins at elaboration time only (no theorem depends
on it). -/
meta def sha256Meta (data : ByteArray) : ByteArray := Id.run do
  let k : Array UInt32 := #[
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]
  let rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
  -- Padding (FIPS 180-4 §5.1.1).
  let bitLen := data.size * 8
  let mut msg := data.push 0x80
  while msg.size % 64 != 56 do
    msg := msg.push 0
  for i in [0:8] do
    msg := msg.push (UInt8.ofNat (bitLen >>> (8 * (7 - i))))
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  let mut w : Array UInt32 := Array.replicate 64 0
  for blk in [0:msg.size / 64] do
    let base := blk * 64
    for t in [0:16] do
      let o := base + 4 * t
      w := w.set! t ((msg.get! o).toUInt32 <<< 24 ||| (msg.get! (o+1)).toUInt32 <<< 16 |||
        (msg.get! (o+2)).toUInt32 <<< 8 ||| (msg.get! (o+3)).toUInt32)
    for t in [16:64] do
      let x := w[t-15]!
      let y := w[t-2]!
      let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
      let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
      w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut hh := h[7]!
    for t in [0:64] do
      let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
      let ch := (e &&& f) ^^^ ((~~~e) &&& g)
      let t1 := hh + S1 + ch + k[t]! + w[t]!
      let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
      let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := S0 + mj
      hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g,
      h[7]! + hh]
  let mut out := ByteArray.empty
  for x in h do
    out := out.push (x >>> 24).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 8).toUInt8
      |>.push x.toUInt8
  return out

/-- Lower-case hex. -/
meta def hexOf (b : ByteArray) : String :=
  let digit (n : Nat) : Char := "0123456789abcdef".toList[n]!
  String.ofList (b.data.toList.flatMap fun x => [digit (x.toNat / 16), digit (x.toNat % 16)])

/-- The chunk literals of `b` (`IncludeBytes.encode`, computed by divide and conquer). -/
meta def chunkList (b : ByteArray) (chunk : Nat) : List Nat :=
  (List.range ((b.size + chunk - 1) / chunk)).map fun i =>
    encodeRange b (i * chunk) (min b.size ((i + 1) * chunk))

open Lean in
/-- The term `{ chunk, size, chunks := [c₀, …], sha256 }`. -/
meta def imageExpr (b : ByteArray) (chunk : Nat) (pin : String) : Expr :=
  let nat := mkConst ``Nat
  let cs := (chunkList b chunk).foldr (init := mkApp (mkConst ``List.nil [Level.zero]) nat)
    fun lit acc => mkApp3 (mkConst ``List.cons [Level.zero]) nat (mkNatLit lit) acc
  mkApp4 (mkConst ``BinaryImage.mk) (mkNatLit chunk) (mkNatLit b.size) cs (mkStrLit pin)

/-- SHA-256 of `b` in lower-case hex: by `sha256sum` when it is on the `PATH` (the interpreted
`sha256Meta` takes about 14 s per MiB), else by `sha256Meta`. Either way only the pin check
depends on it. -/
meta def sha256Hex (b : ByteArray) : IO String := do
  let viaTool : IO (Option String) := do
    let child ← IO.Process.spawn
      { cmd := "sha256sum", stdin := .piped, stdout := .piped, stderr := .null }
    let (stdin, child) ← child.takeStdin
    stdin.write b
    stdin.flush
    let out ← child.stdout.readToEnd
    let rc ← child.wait
    let digest := (out.splitOn " ").headD ""
    return if rc == 0 && digest.length == 64 then some digest else none
  match ← (try viaTool catch _ => pure none) with
  | some digest => return digest
  | none => return hexOf (sha256Meta b)

open Lean Elab Term in
/-- Read `path` (relative to the current file) and check its SHA-256 against `pin`. -/
meta def readPinned (path pin : String) : TermElabM ByteArray := do
  let b ← readRelative path
  let got ← sha256Hex b
  unless got == pin.toLower do
    throwError "binary_image: `{path}` has SHA-256 {got}, but the pin is {pin}"
  return b

open Lean Elab Term in
/-- `binary_image% "path" sha256 "hex"`: the pinned file as a `BinaryImage` literal. -/
syntax (name := binaryImageTerm) "binary_image% " str " sha256 " str (&"chunk" num)? : term

open Lean Elab Term in
elab_rules : term
  | `(binary_image% $path sha256 $pin $[chunk $n?]?) => do
  let c := match n? with
    | some n => n.getNat
    | none => IncludeBytes.chunkSize
  unless 0 < c do throwError "binary_image%: the chunk size must be positive"
  return imageExpr (← readPinned path.getString pin.getString) c pin.getString.toLower

open Lean Meta in
meta unsafe def evalBytesUnsafe (e : Expr) : MetaM Formats.ELF.Bytes :=
  evalExpr Formats.ELF.Bytes (mkConst ``Formats.ELF.Bytes) e

open Lean Meta in
/-- Evaluate a closed `Formats.ELF.Bytes` term at elaboration time. -/
@[implemented_by evalBytesUnsafe]
meta opaque evalBytes (e : Expr) : MetaM Formats.ELF.Bytes

/-- `binary_image_of% src sha256 "hex"`: the bytes of the closed term `src` (an existing
`Formats.ELF.Bytes` literal, e.g. one generated by `scripts/elf_extract.py`), evaluated at
elaboration time, checked against the pin and re-encoded as a `BinaryImage` literal. -/
syntax (name := binaryImageOfTerm) "binary_image_of% " term:max " sha256 " str : term

open Lean Elab Term in
elab_rules : term
  | `(binary_image_of% $src sha256 $pin) => do
  let e ← instantiateMVars (← elabTermEnsuringType src (mkConst ``Formats.ELF.Bytes))
  let arr ← evalBytes e
  let b : ByteArray := ⟨arr.map (·.toNat.toUInt8)⟩
  let got ← sha256Hex b
  unless got == pin.getString.toLower do
    throwError "binary_image_of%: the bytes have SHA-256 {got}, but the pin is {pin.getString}"
  return imageExpr b IncludeBytes.chunkSize pin.getString.toLower

/-- The `Nat` literal of `e`, if it is one (possibly behind `OfNat.ofNat`). -/
meta partial def natLit? (e : Lean.Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ => if e.isAppOfArity ``OfNat.ofNat 3 then natLit? e.appFn!.appArg! else none

open Lean in
/-- The image literal behind the constant `name`: chunk size, file size and chunk literals. -/
meta def imageLiterals (env : Environment) (name : Name) : Option (Nat × Nat × List Nat) := do
  let some (.defnInfo info) := env.find? name | none
  let args := info.value.getAppArgs
  guard (info.value.isAppOfArity ``BinaryImage.mk 4)
  let chunk ← natLit? args[0]!
  let size ← natLit? args[1]!
  let rec lits (e : Expr) (fuel : Nat) : Option (List Nat) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if e.isAppOfArity ``List.nil 1 then some []
      else if e.isAppOfArity ``List.cons 3 then do
        let n ← natLit? e.appFn!.appArg!
        let rest ← lits e.appArg! fuel
        pure (n :: rest)
      else none
  let cs ← lits args[2]! (size / chunk + 2)
  pure (chunk, size, cs)

/-- The `len` little-endian base-256 digits of `n` (divide and conquer). -/
meta partial def digitsLE (n len : Nat) (acc : ByteArray) : ByteArray :=
  if len ≤ 64 then Id.run do
    let mut acc := acc
    let mut n := n
    for _ in [0:len] do
      acc := acc.push (UInt8.ofNat n)
      n := n >>> 8
    return acc
  else
    let lo := len / 2
    digitsLE (n >>> (8 * lo)) (len - lo) (digitsLE (n % (1 <<< (8 * lo))) lo acc)

/-- Decode image literals at elaboration time (the meta counterpart of `bytes`). -/
meta def decodeLiterals (chunk size : Nat) (cs : List Nat) : ByteArray := Id.run do
  let mut acc := ByteArray.emptyWithCapacity size
  let mut left := size
  for c in cs do
    acc := digitsLE c (min chunk left) acc
    left := left - chunk
  return acc

open Lean Elab Command in
/--
`binary_image foo from "path" sha256 "hex"` reads `path` (relative to the current file) at
elaboration time, fails unless its SHA-256 is `hex`, and defines

* `foo : Silmaril.BinaryImage`, the file as 4 KiB chunk literals (`chunk N` sets another
  chunk size; `chunk` at least the file size gives a single `Nat` literal) (noncomputable: it is meant
  for proofs; `#eval` needs a computable copy);
* `foo.wf : foo.WF`, so the bridge lemmas apply;
* `foo.bytes_size_eq : foo.bytes.size = N` and `foo.bits_size_eq : foo.bits.size = N`.

Put it in an `@[expose] public section` so importing modules can reduce `foo`.
-/
syntax (name := binaryImageCmd)
  "binary_image " ident " from " str " sha256 " str (&"chunk" num)? : command

open Lean Elab Command in
elab_rules : command
  | `(binary_image $id from $path sha256 $pin $[chunk $n?]?) => do
  let value ← match n? with
    | some n => `(binary_image% $path sha256 $pin chunk $n)
    | none => `(binary_image% $path sha256 $pin)
  elabCommand (← `(set_option maxRecDepth 100000 in
    noncomputable def $id : Silmaril.BinaryImage := $value))
  let some (_, size, _) := imageLiterals (← getEnv) ((← getCurrNamespace) ++ id.getId)
    | throwError "binary_image: cannot read back `{id.getId}`"
  let sub (s : Name) := mkIdentFrom id (id.getId ++ s)
  let n := Syntax.mkNumLit (toString size)
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $(sub `wf) : ($id).WF := by decide))
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $(sub `bytes_size_eq) : ($id).bytes.size = $n :=
    Silmaril.BinaryImage.size_bytes $(sub `wf)))
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $(sub `bits_size_eq) : ($id).bits.size = $n :=
    Silmaril.BinaryImage.size_bits $(sub `wf)))

/--
`binary_image foo of src sha256 "hex"` is the file-free variant of `binary_image`: `src` is a
closed `Formats.ELF.Bytes` term already in the environment (for example the `raw` literal of a
module generated by `scripts/elf_extract.py`). It is evaluated at elaboration time, checked
against the pin and re-encoded; besides `foo`, `foo.wf` and the size theorems, the kernel proves
`foo.bits_eq_source : foo.bits = src`, so nothing about the re-encoding is trusted. In a
`module`, the module defining `src` must also be imported with `meta import`.
-/
syntax (name := binaryImageOfCmd) "binary_image " ident " of " term:max " sha256 " str : command

open Lean Elab Command in
elab_rules : command
  | `(binary_image $id of $src sha256 $pin) => do
  elabCommand (← `(set_option maxRecDepth 100000 in
    noncomputable def $id : Silmaril.BinaryImage := binary_image_of% $src sha256 $pin))
  let some (_, size, _) := imageLiterals (← getEnv) ((← getCurrNamespace) ++ id.getId)
    | throwError "binary_image: cannot read back `{id.getId}`"
  let sub (s : Name) := mkIdentFrom id (id.getId ++ s)
  let n := Syntax.mkNumLit (toString size)
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $(sub `wf) : ($id).WF := by decide))
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $(sub `bytes_size_eq) : ($id).bytes.size = $n :=
      Silmaril.BinaryImage.size_bytes $(sub `wf)))
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $(sub `bits_size_eq) : ($id).bits.size = $n :=
      Silmaril.BinaryImage.size_bits $(sub `wf)))
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $(sub `bits_eq_source) : ($id).bits = $src :=
      Array.toList_inj.mp (by decide +kernel)))

end BinaryImage

end Silmaril

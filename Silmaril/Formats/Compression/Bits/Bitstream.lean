module

public import Silmaril.Data.ByteArray
public import Silmaril.Formats.Compression.Bits.Bit

@[expose] public section

namespace Silmaril.Formats.Compression

structure LSBWriter where
  buffer : Nat
  count : Nat
  bytes : ByteArray
  totalBits : Nat
deriving Repr

def LSBWriter.empty : LSBWriter :=
  { buffer := 0, count := 0, bytes := ByteArray.empty, totalBits := 0 }

def LSBWriter.writeBit (w : LSBWriter) (b : Bool) : LSBWriter :=
  let newBuf := w.buffer + (if b then 1 <<< w.count else 0)
  let newCount := w.count + 1
  if _ : newCount < 8 then
    { w with buffer := newBuf, count := newCount, totalBits := w.totalBits + 1 }
  else
    let byte := UInt8.ofNat (newBuf % 256)
    { buffer := newBuf >>> 8, count := newCount - 8,
      bytes := w.bytes.push byte, totalBits := w.totalBits + 1 }

def LSBWriter.writeBits (w : LSBWriter) (bits : List Bool) : LSBWriter :=
  bits.foldl (λ w' b => w'.writeBit b) w

def LSBWriter.writeVal (w : LSBWriter) (val : Nat) (n : Nat) : LSBWriter :=
  match n with
  | 0 => w
  | n' + 1 =>
    writeVal (w.writeBit (val % 2 = 1)) (val / 2) n'

def LSBWriter.writeByte (w : LSBWriter) (x : UInt8) : LSBWriter :=
  w.writeVal x.toNat 8

/-- Write the low `n` bits of `code`, most-significant bit first. DEFLATE packs
Huffman codes this way (RFC 1951 §3.1.1), unlike every other field. -/
def LSBWriter.writeCodeMSB (w : LSBWriter) (code : Nat) : Nat → LSBWriter
  | 0 => w
  | n + 1 => (w.writeBit (code.testBit n)).writeCodeMSB code n

/-- Pad with zero bits up to the next byte boundary. -/
def LSBWriter.alignToByte (w : LSBWriter) : LSBWriter :=
  if w.count = 0 then w
  else
    { buffer := 0, count := 0, bytes := w.bytes.push (UInt8.ofNat (w.buffer % 256)),
      totalBits := w.totalBits + (8 - w.count) }

def LSBWriter.toByteArray (w : LSBWriter) : ByteArray :=
  if w.count = 0 then w.bytes
  else
    let byte := UInt8.ofNat (w.buffer % 256)
    w.bytes.push byte

structure LSBReader where
  buffer : Nat
  count : Nat
  input : List UInt8
  totalRead : Nat
deriving Repr

def LSBReader.ofByteArray (bs : ByteArray) : LSBReader :=
  { buffer := 0, count := 0, input := bs.toList, totalRead := 0 }

def LSBReader.refill (r : LSBReader) : LSBReader :=
  match r.input with
  | [] => r
  | byte :: rest =>
    { buffer := byte.toNat, count := 8, input := rest, totalRead := r.totalRead }

def LSBReader.readBit (r : LSBReader) : Option (Bool × LSBReader) :=
  if r.count = 0 then
    let r' := r.refill
    if r'.count = 0 then none
    else
      let b : Bool := r'.buffer % 2 = 1
      let buf' := r'.buffer >>> 1
      let cnt' := r'.count - 1
      let tr' := r'.totalRead + 1
      some (b, { buffer := buf', count := cnt', input := r'.input, totalRead := tr' })
  else
    let b : Bool := r.buffer % 2 = 1
    let buf' := r.buffer >>> 1
    let cnt' := r.count - 1
    let tr' := r.totalRead + 1
    some (b, { buffer := buf', count := cnt', input := r.input, totalRead := tr' })

/-- Number of unread bits. -/
def LSBReader.bitsLeft (r : LSBReader) : Nat := r.count + 8 * r.input.length

/-- Read an `n`-bit value, least-significant bit first (the order `LSBWriter.writeVal`
writes, and the order RFC 1951 uses for everything except Huffman codes). -/
def LSBReader.readBits (r : LSBReader) (n : Nat) : Option (Nat × LSBReader) :=
  match n with
  | 0 => some (0, r)
  | n' + 1 =>
    match r.readBit with
    | none => none
    | some (b, r') =>
      match readBits r' n' with
      | none => none
      | some (val, r'') => some ((if b then 1 else 0) + 2 * val, r'')

/-- Skip the remaining bits of the current byte. -/
def LSBReader.alignToByte (r : LSBReader) : LSBReader :=
  { r with buffer := 0, count := 0, totalRead := r.totalRead + r.count }

def LSBReader.readByte (r : LSBReader) : Option (UInt8 × LSBReader) :=
  match r.readBits 8 with
  | none => none
  | some (val, r') => some (UInt8.ofNat val, r')

structure MSBWriter where
  buffer : Nat
  count : Nat
  bytes : ByteArray
  totalBits : Nat
deriving Repr

def MSBWriter.empty : MSBWriter :=
  { buffer := 0, count := 0, bytes := ByteArray.empty, totalBits := 0 }

def MSBWriter.writeBit (w : MSBWriter) (b : Bool) : MSBWriter :=
  let newBuf := w.buffer * 2 + (if b then 1 else 0)
  let newCount := w.count + 1
  if _ : newCount < 8 then
    { w with buffer := newBuf, count := newCount, totalBits := w.totalBits + 1 }
  else
    let byte := UInt8.ofNat newBuf
    { buffer := 0, count := 0, bytes := w.bytes.push byte,
      totalBits := w.totalBits + 1 }

def MSBWriter.writeBits (w : MSBWriter) (bits : List Bool) : MSBWriter :=
  bits.foldl (λ w' b => w'.writeBit b) w

def MSBWriter.writeVal (w : MSBWriter) (val : Nat) (n : Nat) : MSBWriter :=
  match n with
  | 0 => w
  | n' + 1 =>
    let b : Bool := (val >>> n') % 2 = 1
    writeVal (w.writeBit b) (val % (1 <<< n')) n'

def MSBWriter.writeByte (w : MSBWriter) (x : UInt8) : MSBWriter :=
  w.writeVal x.toNat 8

def MSBWriter.toByteArray (w : MSBWriter) : ByteArray :=
  if w.count = 0 then w.bytes
  else
    let byte := UInt8.ofNat (w.buffer <<< (8 - w.count))
    w.bytes.push byte

structure MSBReader where
  buffer : Nat
  count : Nat
  input : List UInt8
  totalRead : Nat
deriving Repr

def MSBReader.ofByteArray (bs : ByteArray) : MSBReader :=
  { buffer := 0, count := 0, input := bs.toList, totalRead := 0 }

def MSBReader.refill (r : MSBReader) : MSBReader :=
  match r.input with
  | [] => r
  | byte :: rest =>
    { buffer := byte.toNat, count := 8, input := rest, totalRead := r.totalRead }

def MSBReader.readBit (r : MSBReader) : Option (Bool × MSBReader) :=
  if r.count = 0 then
    let r' := r.refill
    if r'.count = 0 then none
    else
      let b : Bool := (r'.buffer >>> 7) % 2 = 1
      let buf' := (r'.buffer <<< 1) % 256
      let cnt' := r'.count - 1
      let tr' := r'.totalRead + 1
      some (b, { buffer := buf', count := cnt', input := r'.input, totalRead := tr' })
  else
    let b : Bool := (r.buffer >>> 7) % 2 = 1
    let buf' := (r.buffer <<< 1) % 256
    let cnt' := r.count - 1
    let tr' := r.totalRead + 1
    some (b, { buffer := buf', count := cnt', input := r.input, totalRead := tr' })

/-- Read an `n`-bit value, most-significant bit first: the first bit read is
worth `2 ^ (n - 1)`. -/
def MSBReader.readBits (r : MSBReader) (n : Nat) : Option (Nat × MSBReader) :=
  match n with
  | 0 => some (0, r)
  | n' + 1 =>
    match r.readBit with
    | none => none
    | some (b, r') =>
      match readBits r' n' with
      | none => none
      | some (val, r'') => some ((if b then 2 ^ n' else 0) + val, r'')

def MSBReader.readByte (r : MSBReader) : Option (UInt8 × MSBReader) :=
  match r.readBits 8 with
  | none => none
  | some (val, r') => some (UInt8.ofNat val, r')

end Silmaril.Formats.Compression

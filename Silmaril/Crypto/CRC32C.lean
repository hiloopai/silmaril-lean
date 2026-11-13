module

/-!
# CRC32C (Castagnoli)

CRC32C uses the Castagnoli polynomial `0x1EDC6F41` (reflected form `0x82F63B78`).
Table-driven, byte-at-a-time, reflected input and output, initial value
`0xFFFFFFFF`, final XOR `0xFFFFFFFF`.

`crc32cInit` and `crc32cUpdateByte` are exported, so a caller that must hash a
stream can thread the uncomplemented running state itself and apply `~~~` once
at the end.

## References
- RFC 3720 Appendix B.4 (iSCSI CRC32C)

## Test vectors (all proved as theorems below)
- `crc32cList []` -> 0x00000000
- `crc32cList "123456789"` -> 0xE3069283  (CRC catalogue check value)
- RFC 3720 B.4: 32 zero bytes -> 0x8A9136AA, 32 `0xFF` bytes -> 0x62A8AB43,
  `00..1F` -> 0x46DD794E, `1F..00` -> 0x113FDB5C, and the 48-byte
  iSCSI SCSI Read(10) command PDU -> 0xD9963A56
-/

set_option maxRecDepth 10000000

@[expose] public section

namespace Silmaril.Crypto

/-- The reflected CRC32C polynomial `0x82F63B78`. -/
def crc32cPoly : UInt32 := 0x82F63B78

/-- Compute one entry of the CRC32C lookup table. -/
def crc32cTableEntry (n : Nat) : UInt32 :=
  let rec go (crc : UInt32) : Nat → UInt32
    | 0 => crc
    | k + 1 =>
      if (crc &&& 1) = 0 then go (crc >>> 1) k
      else go ((crc >>> 1) ^^^ crc32cPoly) k
  go (UInt32.ofNat n) 8

/-- The full CRC32C lookup table (256 entries).

An `Array`, not a `List`: `crc32cUpdateByte` indexes it once per input byte, and
a `List.getD` lookup would walk ~128 cons cells per byte at run time. -/
def crc32cTable : Array UInt32 :=
  Array.ofFn (n := 256) (fun i => crc32cTableEntry i.val)

/-- CRC32C initial value (all ones). -/
def crc32cInit : UInt32 := 0xFFFFFFFF

/-- Update a CRC32C value with a single byte.  The state is the *uncomplemented*
running CRC, so this composes for streaming; apply `~~~` once at the end. -/
def crc32cUpdateByte (crc : UInt32) (byte : UInt8) : UInt32 :=
  let idx := ((crc ^^^ byte.toUInt32) &&& 0xFF).toNat
  let entry := crc32cTable.getD idx 0
  (crc >>> 8) ^^^ entry

/-- Compute the CRC32C of a `ByteArray`, returning the complemented value. -/
def crc32c (data : ByteArray) : UInt32 :=
  ~~~(data.toList.foldl crc32cUpdateByte crc32cInit)

/-- Compute CRC32C of a `List UInt8`. -/
def crc32cList (data : List UInt8) : UInt32 :=
  ~~~(data.foldl crc32cUpdateByte crc32cInit)

/-! ## Theorems — structure -/

/-- The lookup table really has 256 entries, so the `&&& 0xFF` mask in
`crc32cUpdateByte` always indexes in range and the `getD` default is never
taken. -/
theorem crc32cTable_size : crc32cTable.size = 256 := by
  decide +kernel

/-- The `ByteArray` entry point is the list entry point.  This transports every
vector below to the public API. -/
theorem crc32c_eq_list (b : ByteArray) : crc32c b = crc32cList b.toList := rfl

/-! ## Theorems — test vectors -/

/-- CRC32C of empty input is `0`. -/
theorem crc32c_empty : crc32cList [] = 0 := by
  unfold crc32cList; decide

/-- CRC32C of `ByteArray.empty` is `0`. -/
theorem crc32c_bytes_empty : crc32c ByteArray.empty = 0 := by
  unfold crc32c
  simp [ByteArray.toList_empty, crc32cInit]

/-- CRC32C of "123456789" → 0xE3069283 (the CRC catalogue check value). -/
theorem crc32c_123456789 :
    crc32cList [0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39] = 0xE3069283 := by
  decide +kernel

/-- The same vector through the public `ByteArray` entry point. -/
theorem crc32c_bytes_123456789 :
    crc32c (ByteArray.mk #[0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39])
      = 0xE3069283 := by
  decide +kernel

/-! ### RFC 3720 Appendix B.4 -/

/-- RFC 3720 B.4: 32 bytes of zeroes → 0x8A9136AA. -/
theorem crc32c_zeros32 : crc32cList (List.replicate 32 0) = 0x8A9136AA := by
  decide +kernel

/-- RFC 3720 B.4: 32 bytes of ones → 0x62A8AB43. -/
theorem crc32c_ones32 : crc32cList (List.replicate 32 0xFF) = 0x62A8AB43 := by
  decide +kernel

/-- RFC 3720 B.4: 32 incrementing bytes `00..1F` → 0x46DD794E. -/
theorem crc32c_incr32 :
    crc32cList ((List.range 32).map UInt8.ofNat) = 0x46DD794E := by
  decide +kernel

/-- RFC 3720 B.4: 32 decrementing bytes `1F..00` → 0x113FDB5C. -/
theorem crc32c_decr32 :
    crc32cList ((List.range 32).reverse.map UInt8.ofNat) = 0x113FDB5C := by
  decide +kernel

/-- RFC 3720 B.4: the 48-byte iSCSI SCSI Read(10) command PDU → 0xD9963A56. -/
theorem crc32c_iscsi_read10 :
    crc32cList
      [0x01,0xC0,0x00,0x00,0x00,0x00,0x00,0x00,
       0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
       0x14,0x00,0x00,0x00,0x00,0x00,0x04,0x00,
       0x00,0x00,0x00,0x14,0x00,0x00,0x00,0x18,
       0x28,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
       0x02,0x00,0x00,0x00,0x00,0x00,0x00,0x00] = 0xD9963A56 := by
  decide +kernel

end Silmaril.Crypto

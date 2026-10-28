module

public import Silmaril.RiscV.LPS.Sem
public import Silmaril.RiscV.LPS.DecodeC
public import Silmaril.Process.Memory

/-!
# LPS user-mode RISC-V step over Linux virtual memory

Hand translation of `theories/LinuxProcessSem/RiscvSemantics.v`, with the pieces of
`theories/LinuxProcessSem/BvBase.v` and `theories/LinuxProcessSem/MemImageType.v` it uses
(LPS commit `f1006fe8`, MIT). Upstream marks these files as part of its trusted
specification.

This layer does two things.

1. **ISA wrapping.** Fetch the instruction from the executable segments, intercept `ecall`
   before decoding (the syscall model takes over), otherwise decode with `decodeAny`
   (32-bit or compressed), build the effect tree with `exec` and interpret it
   (`interpEff`). Fetch is length-correct (`fetchTail`): a 2-byte instruction at the end of
   a segment fetches only those two bytes. LR/SC reservations, F/D and `fcsr` are modeled.
2. **Virtual memory.** Loaded ELF segments are a read-only backing (`rom`, read gated on
   'r'); a writable overlay (`mem`) holds everything the process stores, and a store must
   land on memory the process has mapped writable (`storeOk`, via `wview`); instruction
   fetch is gated on 'x'. Immutable code (x, not w) is fetched from the static image; w+x
   code through the overlay.

Each step either succeeds, faults (the program did something fatal and the model says so
faithfully: misaligned pc, fetch from unmapped or non-executable memory, a load from
unmapped memory, a store outside the writable view, `ebreak`, a misaligned atomic, or an
encoding the ISA defines to be illegal), or is unmodeled (the model gives up: an
undecodable word, an `illegal` node, or a fetch declined for a modeling reason). The
classification is fail-closed.

`ecall` (exactly `0x00000073`) records a7 (x17) in `svcPending` and leaves pc unchanged;
the trace semantics (upstream `Run.v`, not translated here) dispatches it.

Upstream's `Section WithMemImage` variable `mi_loaded_segments` is an explicit first
argument `segs` here. Segment images are byte arrays (see `Segment`).
-/

@[expose] public section

namespace Silmaril.RiscV.LPS

/-- `byte` (BvBase.v). -/
abbrev Byte := BitVec 8

/-! ## Little-endian helpers (BvBase.v) -/

/-- `le2`: little-endian assembly, the first argument is the high byte. -/
def le2 (b1 b0 : Byte) : BitVec 16 := b1 ++ b0
/-- `le4`. -/
def le4 (b3 b2 b1 b0 : Byte) : BitVec 32 := le2 b3 b2 ++ le2 b1 b0

/-- The exact value of a little-endian byte list (`bytes_le_to_Z`). -/
def bytesLeToNat : List Byte → Nat
  | [] => 0
  | b :: rest => b.toNat ||| (bytesLeToNat rest <<< 8)

/-- The same value truncated to 64 bits (`le_bytes_to_word`). -/
def leBytesToWord (bs : List Byte) : Word := BitVec.ofNat 64 (bytesLeToNat bs)

/-- The `n` little-endian bytes of `z` (`Z_to_le_bytes`). -/
def natToLeBytes : Nat → Nat → List Byte
  | 0, _ => []
  | n + 1, z => BitVec.ofNat 8 z :: natToLeBytes n (z >>> 8)

/-- `word_to_nat` (BvBase.v). -/
def wordToNat (w : Word) : Nat := w.toNat

/-- `nat_to_word` (BvBase.v). -/
def natToWord (n : Nat) : Word := BitVec.ofNat 64 n

/-- Unsigned `≤` (`bv_leu`, BvBase.v). -/
def leU {n : Nat} (a b : BitVec n) : Bool := decide (a.toNat ≤ b.toNat)

/-- A list length as a word (`len_word`, BvBase.v). -/
def lenWord {α : Type} (l : List α) : Word := BitVec.ofNat 64 l.length

/-- `le8` (BvBase.v). -/
def le8 (b7 b6 b5 b4 b3 b2 b1 b0 : Byte) : Word := le4 b7 b6 b5 b4 ++ le4 b3 b2 b1 b0

/-- The 8 little-endian bytes of a word (`word_le8`, BvBase.v). -/
def wordLe8 (v : Word) : List Byte := natToLeBytes 8 v.toNat

/-- The 4 little-endian bytes of a word's low half (`word_le4`, BvBase.v). -/
def wordLe4 (v : Word) : List Byte := natToLeBytes 4 v.toNat

/-- The 2 little-endian bytes of a word's low quarter (`word_le2`, BvBase.v). -/
def wordLe2 (v : Word) : List Byte := natToLeBytes 2 v.toNat

/-- `length_Z_to_le_bytes` (BvBase.v). -/
theorem length_natToLeBytes (n z : Nat) : (natToLeBytes n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [natToLeBytes, ih]

/-! ## Memory images (MemImageType.v) -/

/-- A loaded ELF segment (`Segment`): base, size, page permissions and the image bytes.

Upstream stores the permissions as an `"rwx"` string (with `-` for an unset bit) and the
image as lowercase hex chunks (an extraction convenience; chunk boundaries have no memory
meaning). Here they are `Process.Permissions` and an `Array (Option Byte)`, so that
fetches and loads reduce in the kernel. A `none` entry is a byte the image does not
supply: upstream's hex digit pair that `hex_byte_at` cannot read. `Segment.ofHex` builds a
segment from upstream's representation byte by byte (`segmentByteAt_ofHex`), so a bad
digit is a hole at exactly that byte, as upstream, and every later byte stays readable;
upstream's "snapshot hex the decoder cannot read" decline (one of the reasons
`fetchFailure` answers unmodeled) is then the same decline here. -/
structure Segment where
  /-- `seg_base`. -/
  base : Nat
  /-- `seg_size`. -/
  size : Nat
  /-- `seg_perms`. -/
  perms : Process.Permissions
  /-- `seg_bytes`, decoded per byte; `none` where the image supplies no byte. -/
  data : Array (Option Byte)

namespace Segment

/-- `seg_readable`. -/
def readable (seg : Segment) : Bool := seg.perms.read
/-- `seg_writable`. -/
def writable (seg : Segment) : Bool := seg.perms.write
/-- `seg_executable`. -/
def executable (seg : Segment) : Bool := seg.perms.execute

end Segment

/-- Where the program header table lands (`PhdrInfo`, MemImageType.v): `AT_PHDR`,
`AT_PHENT` and `AT_PHNUM`. -/
structure PhdrInfo where
  /-- `ph_addr`. -/
  addr : Nat
  /-- `ph_ent`. -/
  ent : Nat
  /-- `ph_num`. -/
  num : Nat
  deriving DecidableEq, Repr

/-- The data one binary contributes to the model (`Image`, MemImageType.v; it also stands
for upstream's module type `MemImage`). -/
structure Image where
  /-- `img_segments`. -/
  segments : List Segment
  /-- `img_init_pc`. -/
  initPc : Nat
  /-- `img_phdrs`. -/
  phdrs : PhdrInfo

/-! ## Machine state -/

/-- The machine state (`machine_state`): register files in the same representation as
`Core`, pc, a pending-ecall slot, the reservation, fcsr, the writable overlay and the
read-only backing. -/
structure MachineState where
  /-- `ms_regs`. -/
  regs : BvMap 5 Word
  /-- `ms_fregs`. -/
  fregs : BvMap 5 Word
  /-- `ms_pc_val`. -/
  pcVal : Word
  /-- `ms_svc_pending`. -/
  svcPending : Option Word
  /-- `ms_resv`. -/
  resv : Option Word
  /-- `ms_fcsr`. -/
  fcsr : BitVec 32
  /-- `ms_mem`: the writable overlay. -/
  mem : Word → Option Byte
  /-- `ms_rom`: the read-only backing, as seen by syscall buffers. -/
  rom : Word → Option Byte

namespace MachineState

/-- `ms_pc`. -/
def pc (st : MachineState) : Word := st.pcVal
/-- `ms_sp`. -/
def sp (st : MachineState) : Word := regGet st.regs 2
/-- The `i`-th syscall argument register a0..a5 (`ms_gpr`). -/
def gpr (st : MachineState) (i : Nat) : Word := regGet st.regs (BitVec.ofNat 5 (10 + i))
/-- A register by number, x0 reading as 0 (`ms_reg`). -/
def reg (st : MachineState) (r : Reg) : Word := if eqB r 0 then 0 else regGet st.regs r
/-- Update a register; x0 writes are discarded (`set_reg`). -/
def setReg (st : MachineState) (r : Reg) (v : Word) : MachineState :=
  if eqB r 0 then st else { st with regs := BvMap.set r v st.regs }
/-- Set a0 (`set_gpr0`). -/
def setGpr0 (st : MachineState) (ret : Word) : MachineState := st.setReg 10 ret

end MachineState

/-- Write `data` byte by byte into `mem` starting at `addr` (`write_to_mem`). -/
def writeToMem (mem : Word → Option Byte) (addr : Word) : List Byte → Word → Option Byte
  | [] => mem
  | b :: rest => writeToMem (fun a => if eqB a addr then some b else mem a) (addr + 1) rest

/-- Set a0 and write a buffer (`set_gpr0_write_buf`). -/
def MachineState.setGpr0WriteBuf (st : MachineState) (ret : Word) (bufAddr : Word)
    (data : List Byte) : MachineState :=
  let st' := st.setReg 10 ret
  { st' with mem := writeToMem st'.mem bufAddr data }

/-! ## Machine step result -/

/-- `machine_result`: success, a fault the model claims faithfully, or the model giving
up. -/
inductive MachineResult (α : Type) where
  | ok (result : α)
  | fault
  | unmodeled

/-- The shape of a machine result. -/
inductive ResultKind where
  | ok | fault | unmodeled
  deriving DecidableEq, Repr

/-- The shape of a machine result, without its value. -/
def MachineResult.kind {α : Type} : MachineResult α → ResultKind
  | .ok _ => .ok
  | .fault => .fault
  | .unmodeled => .unmodeled

/-! ## Unified memory read helpers -/

/-- The writable overlay first, then the read-only backing (`ms_read_byte`). -/
def MachineState.readByte (st : MachineState) (addr : Word) : Option Byte :=
  match st.mem addr with
  | some b => some b
  | none => st.rom addr

/-- `ms_read_bytes_aux`. -/
def MachineState.readBytesAux (st : MachineState) (addr : Word) : Nat → Option (List Byte)
  | 0 => some []
  | n + 1 => do
    let b ← st.readByte addr
    let rest ← st.readBytesAux (addr + 1) n
    pure (b :: rest)

/-- `ms_read_bytes`. -/
def MachineState.readBytes (st : MachineState) (addr len : Word) : Option (List Byte) :=
  st.readBytesAux addr (wordToNat len)

/-- `ms_read_u64`. -/
def MachineState.readU64 (st : MachineState) (addr : Word) : Option Word :=
  (st.readBytes addr 8).map leBytesToWord

/-! ## Hex decode helpers -/

/-- `hex_nybble`: lowercase hex digits only; anything else is 16. -/
def hexNybble (c : UInt8) : Nat :=
  if 48 ≤ c ∧ c ≤ 57 then c.toNat - 48
  else if 97 ≤ c ∧ c ≤ 102 then c.toNat - 87
  else 16

/-- The byte at index `i` of a hex string (`hex_byte_at`). -/
def hexByteAt (s : String) (i : Nat) : Option Byte :=
  let b := s.toUTF8
  if h : 2 * i + 1 < b.size then
    let hi := hexNybble b[2 * i]
    let lo := hexNybble b[2 * i + 1]
    if hi < 16 ∧ lo < 16 then some (BitVec.ofNat 8 (hi * 16 + lo)) else none
  else none

/-- The byte at offset `off` of a hex-chunked image (upstream `segment_byte_at`). Chunk
boundaries have no memory meaning. -/
def hexChunksByteAt : List String → Nat → Option Byte
  | [], _ => none
  | chunk :: rest, off =>
    let chunkBytes := chunk.utf8ByteSize / 2
    if off < chunkBytes then hexByteAt chunk off else hexChunksByteAt rest (off - chunkBytes)

/-- Decode the first `n` bytes of a hex-chunked image, stopping at the first byte that is not
two lowercase hex digits. (Not used for segments, which keep every byte: `Segment.ofHex`.) -/
def hexChunksDecode (chunks : List String) (n : Nat) : Array Byte := Id.run do
  let mut out : Array Byte := #[]
  for i in [0:n] do
    match hexChunksByteAt chunks i with
    | some b => out := out.push b
    | none => return out
  return out

/-- Upstream's `string_has`: does the permission string carry the flag character? -/
def stringHas (c : Char) (s : String) : Bool := s.contains c

/-- A segment from upstream's representation: an `"rwx"` permission string and lowercase hex
chunks. -/
def Segment.ofHex (base size : Nat) (perms : String) (chunks : List String) : Segment :=
  { base, size
    perms := ⟨stringHas 'r' perms, stringHas 'w' perms, stringHas 'x' perms⟩
    data := Array.ofFn (n := size) fun i => hexChunksByteAt chunks i }

/-- A segment image of fully decoded bytes. -/
def Segment.bytesData (bytes : List Byte) : Array (Option Byte) := (bytes.map some).toArray

/-- The byte at offset `off` of a segment image (`segment_byte_at`). -/
def segmentByteAt (data : Array (Option Byte)) (off : Nat) : Option Byte := data[off]?.join

/-- Within the segment, a segment built from hex chunks reads each byte exactly as
upstream's `segment_byte_at` reads the chunks: a byte with a bad digit is a hole and the
bytes after it are unaffected. (Every read goes through `findSegment`, so `off < size`.) -/
theorem segmentByteAt_ofHex (base size : Nat) (perms : String) (chunks : List String)
    {off : Nat} (h : off < size) :
    segmentByteAt (Segment.ofHex base size perms chunks).data off = hexChunksByteAt chunks off := by
  simp [segmentByteAt, Segment.ofHex, h]

/-- Beyond its size, a segment built from hex chunks supplies no byte. -/
theorem segmentByteAt_ofHex_of_le (base size : Nat) (perms : String) (chunks : List String)
    {off : Nat} (h : size ≤ off) :
    segmentByteAt (Segment.ofHex base size perms chunks).data off = none := by
  simp [segmentByteAt, Segment.ofHex, Nat.not_lt.mpr h]

/-- A fully decoded image reads as its bytes. -/
theorem segmentByteAt_bytesData (bytes : List Byte) (off : Nat) :
    segmentByteAt (Segment.bytesData bytes) off = bytes[off]? := by
  simp only [segmentByteAt, Segment.bytesData, List.getElem?_toArray, List.getElem?_map]
  cases bytes[off]? <;> rfl

/-- `segment_read_bytes`. -/
def segmentReadBytes (data : Array (Option Byte)) (off : Nat) : Nat → Option (List Byte)
  | 0 => some []
  | n + 1 => do
    let b ← segmentByteAt data off
    let rest ← segmentReadBytes data (off + 1) n
    pure (b :: rest)

/-! ## Memory read -/

/-- The first segment covering all of `[addr, addr + n)` (`find_segment`). -/
def findSegment : List Segment → Nat → Nat → Option Segment
  | [], _, _ => none
  | seg :: rest, addr, n =>
    if seg.base ≤ addr ∧ addr + n ≤ seg.base + seg.size then some seg
    else findSegment rest addr n

/-- Read `n` bytes at `addr` from `seg`, each from the overlay when present and from the
static image otherwise (`seg_ov_read_bytes`). -/
def segOvReadBytes (m : Word → Option Byte) (seg : Segment) (addr : Word) :
    Nat → Option (List Byte)
  | 0 => some []
  | n + 1 => do
    let b ← match m addr with
      | some b => some b
      | none => segmentByteAt seg.data (addr.toNat - seg.base)
    let rest ← segOvReadBytes m seg (addr + 1) n
    pure (b :: rest)

/-- Does `[addr, addr + n)` avoid every non-writable segment (`range_avoids_ro_segs`)? -/
def rangeAvoidsRoSegs (segs : List Segment) (addr n : Nat) : Bool :=
  segs.all fun seg => seg.writable || !(seg.base < addr + n && addr < seg.base + seg.size)

section WithMemImage

variable (segs : List Segment)

/-- A data read inside one readable segment (`memory_read`). -/
def memoryRead (addr : Word) (n : Nat) : Option (List Byte) :=
  match findSegment segs addr.toNat n with
  | some seg =>
    if seg.readable then segmentReadBytes seg.data (addr.toNat - seg.base) n else none
  | none => none

/-- An instruction read from an immutable executable segment, x and not w (`code_read`). -/
def codeRead (addr : Word) (n : Nat) : Option (List Byte) :=
  match findSegment segs addr.toNat n with
  | some seg =>
    if seg.executable && !seg.writable then
      segmentReadBytes seg.data (addr.toNat - seg.base) n
    else none
  | none => none

/-- The static projection of the w+x fetch (`code_read_wx`). -/
def codeReadWx (addr : Word) (n : Nat) : Option (List Byte) :=
  match findSegment segs addr.toNat n with
  | some seg =>
    if seg.executable && seg.writable then
      segmentReadBytes seg.data (addr.toNat - seg.base) n
    else none
  | none => none

/-- An instruction read from a writable executable segment, overlay first
(`code_read_ov`). -/
def codeReadOv (m : Word → Option Byte) (addr : Word) (n : Nat) : Option (List Byte) :=
  match findSegment segs addr.toNat n with
  | some seg => if seg.executable && seg.writable then segOvReadBytes m seg addr n else none
  | none => none

/-- Would a real MMU trap on fetching byte `a`: unmapped, or mapped without 'x'
(`fetch_byte_traps`)? -/
def fetchByteTraps (a : Word) : Bool :=
  match findSegment segs a.toNat 1 with
  | none => true
  | some seg => !seg.executable

/-- The byte at `addr` as the kernel may write it: the overlay merged over writable
segments (`wview`). -/
def wview (m : Word → Option Byte) (addr : Word) : Option Byte :=
  match m addr with
  | some b => some b
  | none =>
    match findSegment segs addr.toNat 1 with
    | some seg => if seg.writable then segmentByteAt seg.data (addr.toNat - seg.base) else none
    | none => none

/-- `ms_writable_byte`. -/
def MachineState.writableByte (st : MachineState) (addr : Word) : Option Byte :=
  wview segs st.mem addr

/-- The store bound: every byte of the range is in the writable view (`store_ok`). -/
def storeOk (m : Word → Option Byte) (a : Word) : Nat → Bool
  | 0 => true
  | n + 1 =>
    match wview segs m a with
    | some _ => storeOk m (a + 1) n
    | none => false

/-! ## Instruction fetch -/

/-- Four bytes from immutable code at a 2-aligned address (`fetch_word`). IALIGN = 16
because compressed instructions are modeled. -/
def fetchWord (addr : Word) : Option (BitVec 32) :=
  if addr.toNat % 2 ≠ 0 then none
  else match codeRead segs addr 4 with
    | some [b0, b1, b2, b3] => some (le4 b3 b2 b1 b0)
    | _ => none

/-- The w+x word fetch through the overlay (`fetch_word_ov`). -/
def fetchWordOv (m : Word → Option Byte) (addr : Word) : Option (BitVec 32) :=
  if addr.toNat % 2 ≠ 0 then none
  else match codeReadOv segs m addr 4 with
    | some [b0, b1, b2, b3] => some (le4 b3 b2 b1 b0)
    | _ => none

/-- The static projection of `fetchWordOv` (`fetch_word_wx`). -/
def fetchWordWx (addr : Word) : Option (BitVec 32) :=
  if addr.toNat % 2 ≠ 0 then none
  else match codeReadWx segs addr 4 with
    | some [b0, b1, b2, b3] => some (le4 b3 b2 b1 b0)
    | _ => none

/-- One 16-bit parcel from immutable code (`fetch_half`). -/
def fetchHalf (addr : Word) : Option (BitVec 16) :=
  match codeRead segs addr 2 with
  | some [b0, b1] => some (le2 b1 b0)
  | _ => none

/-- The length-correct fetch (`fetch_tail`): read parcel 0, and parcel 1 only for a 32-bit
encoding. -/
def fetchTail (addr : Word) : Option (BitVec 32) :=
  if addr.toNat % 2 ≠ 0 then none
  else match fetchHalf segs addr with
    | none => none
    | some h0 =>
      if (bits 0 2 h0).toNat = 3 then
        match fetchHalf segs (addr + 2) with
        | some h1 => some (h1 ++ h0)
        | none => none
      else some ((0 : BitVec 16) ++ h0)

/-- `fetch_half_ov`. -/
def fetchHalfOv (m : Word → Option Byte) (addr : Word) : Option (BitVec 16) :=
  match codeReadOv segs m addr 2 with
  | some [b0, b1] => some (le2 b1 b0)
  | _ => none

/-- A parcel from whichever executable segment holds it (`fetch_half_any`). -/
def fetchHalfAny (m : Word → Option Byte) (addr : Word) : Option (BitVec 16) :=
  match fetchHalf segs addr with
  | some h => some h
  | none => fetchHalfOv segs m addr

/-- The length-correct fetch over both kinds of segment (`fetch_tail_any`). -/
def fetchTailAny (m : Word → Option Byte) (addr : Word) : Option (BitVec 32) :=
  if addr.toNat % 2 ≠ 0 then none
  else match fetchHalfAny segs m addr with
    | none => none
    | some h0 =>
      if (bits 0 2 h0).toNat = 3 then
        match fetchHalfAny segs m (addr + 2) with
        | some h1 => some (h1 ++ h0)
        | none => none
      else some ((0 : BitVec 16) ++ h0)

/-- RISC-V `ecall` is exactly `0x00000073` (`is_ecall`). -/
def isEcall (w : BitVec 32) : Bool := eqB w 0x73#32

/-! ## The tree interpreter -/

/-- Byte counts for the `load`/`store` widths in bits (`width_bytes`). -/
def widthBytes : Nat → Nat
  | 8 => 1
  | 16 => 2
  | 32 => 4
  | 64 => 8
  | _ => 0

/-- Overlay first, then the readable segments; fail on any miss (`ov_read_bytes`). -/
def ovReadBytes (m : Word → Option Byte) (addr : Word) : Nat → Option (List Byte)
  | 0 => some []
  | n + 1 => do
    let b ← match m addr with
      | some b => some b
      | none => match memoryRead segs addr 1 with
        | some (b :: _) => some b
        | _ => none
    let rest ← ovReadBytes m (addr + 1) n
    pure (b :: rest)

end WithMemImage

/-- A reported memory access: address and byte count (`memory_access`). -/
abbrev MemoryAccess := Word × Nat

/-- A result with the data-memory ranges the instruction accessed (`access_report`). -/
structure AccessReport (α : Type) where
  /-- `access_value`. -/
  value : α
  /-- `accessed_ranges`. -/
  ranges : List MemoryAccess

/-- `drop_access_report`. -/
def MachineResult.dropAccessReport {α : Type} : MachineResult (AccessReport α) → MachineResult α
  | .ok report => .ok report.value
  | .fault => .fault
  | .unmodeled => .unmodeled

/-- The tree interpreter (`interp_eff_accesses`), structural over the effect tree.
`ebreak`, `fault` and `definedIllegal` are faults; `illegal` and `ecall` are unmodeled; a
failed load or store is a fault (the SIGSEGV analogue). -/
def interpEffAccesses (segs : List Segment) :
    Eff → (Word → Option Byte) → MachineResult (AccessReport (Core × (Word → Option Byte)))
  | .done c, m => .ok ⟨(c, m), []⟩
  | .ebreak _, _ | .fault _, _ | .definedIllegal _, _ => .fault
  | .illegal _, _ | .ecall _, _ => .unmodeled
  | .load n a k, m =>
    match ovReadBytes segs m a (widthBytes n) with
    | some bs =>
      match interpEffAccesses segs (k ((leBytesToWord bs).extractLsb' 0 n)) m with
      | .ok report => .ok ⟨report.value, (a, widthBytes n) :: report.ranges⟩
      | .fault => .fault
      | .unmodeled => .unmodeled
    | none => .fault
  | .store n a v k, m =>
    if storeOk segs m a (widthBytes n) then
      match interpEffAccesses segs k (writeToMem m a (natToLeBytes (widthBytes n) v.toNat)) with
      | .ok report => .ok ⟨report.value, (a, widthBytes n) :: report.ranges⟩
      | .fault => .fault
      | .unmodeled => .unmodeled
    else .fault

/-- The one trusted interpreter, without access reports (`interp_eff`). -/
def interpEff (segs : List Segment) (t : Eff) (m : Word → Option Byte) :
    MachineResult (Core × (Word → Option Byte)) :=
  (interpEffAccesses segs t m).dropAccessReport

/-- `drop_interp_eff_accesses`. -/
theorem dropAccessReport_interpEffAccesses (segs : List Segment) (t : Eff)
    (m : Word → Option Byte) :
    (interpEffAccesses segs t m).dropAccessReport = interpEff segs t m := rfl

/-- The core of a machine state. -/
def MachineState.core (st : MachineState) : Core :=
  ⟨st.regs, st.fregs, st.pcVal, st.fcsr, st.resv⟩

/-- Decode and execute a fetched word (`decode_exec_accesses`). `ecall` is intercepted
before decoding; an undecodable word is unmodeled unless the ISA defines it illegal. -/
def decodeExecAccesses (segs : List Segment) (st : MachineState) (w : BitVec 32) :
    MachineResult (AccessReport MachineState) :=
  if isEcall w then .ok ⟨{ st with svcPending := some (st.reg 17) }, []⟩
  else
    match decodeAny w with
    | none => if isDefinedIllegal w then .fault else .unmodeled
    | some (i, isz) =>
      match interpEffAccesses segs (exec (BitVec.ofInt 64 isz) i st.core) st.mem with
      | .fault => .fault
      | .unmodeled => .unmodeled
      | .ok report =>
        let (c, m') := report.value
        .ok ⟨{ regs := c.regs, fregs := c.fregs, pcVal := c.pc, svcPending := none,
               resv := c.resv, fcsr := c.fcsr, mem := m', rom := st.rom }, report.ranges⟩

/-- `decode_exec`. -/
def decodeExec (segs : List Segment) (st : MachineState) (w : BitVec 32) :
    MachineResult MachineState :=
  (decodeExecAccesses segs st w).dropAccessReport

/-- Classify a fetch that every path declined (`fetch_failure`): a misaligned pc, or a needed
byte that is unmapped or non-executable, is a fault; otherwise the model declined. -/
def fetchFailure (segs : List Segment) (m : Word → Option Byte) (addr : Word) :
    MachineResult MachineState :=
  if addr.toNat % 2 ≠ 0 then .fault
  else
    let traps :=
      fetchByteTraps segs addr || fetchByteTraps segs (addr + 1) ||
        match fetchHalfAny segs m addr with
        | none => false -- parcel 0 is mapped and executable
        | some _ => fetchByteTraps segs (addr + 2) || fetchByteTraps segs (addr + 3)
    if traps then .fault else .unmodeled

/-- One machine step with its access report (`step_accesses`): the four-byte fast paths
first, then the length-correct halfword fetch, then the failure classification. -/
def stepAccesses (segs : List Segment) (st : MachineState) :
    MachineResult (AccessReport MachineState) :=
  match fetchWord segs st.pc with
  | some w => decodeExecAccesses segs st w
  | none =>
    match fetchWordOv segs st.mem st.pc with
    | some w => decodeExecAccesses segs st w
    | none =>
      match fetchTailAny segs st.mem st.pc with
      | some w => decodeExecAccesses segs st w
      | none =>
        match fetchFailure segs st.mem st.pc with
        | .ok st' => .ok ⟨st', []⟩
        | .fault => .fault
        | .unmodeled => .unmodeled

/-- One machine step (`step`). -/
def machineStep (segs : List Segment) (st : MachineState) : MachineResult MachineState :=
  (stepAccesses segs st).dropAccessReport

/-- `drop_decode_exec_accesses`. -/
theorem dropAccessReport_decodeExecAccesses (segs : List Segment) (st : MachineState)
    (w : BitVec 32) : (decodeExecAccesses segs st w).dropAccessReport = decodeExec segs st w :=
  rfl

/-- `drop_step_accesses`. -/
theorem dropAccessReport_stepAccesses (segs : List Segment) (st : MachineState) :
    (stepAccesses segs st).dropAccessReport = machineStep segs st := rfl

end Silmaril.RiscV.LPS

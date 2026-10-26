module

public import Silmaril.Crypto.X86.Sha256O2.Image
public import Silmaril.Crypto.SHA256.Kernel
public import Silmaril.X86.CallingConvention
public import Silmaril.X86.Ext.Machine
public import Silmaril.X86.EntryState

/-!
# The pilot contract: clang `-O2` `sha256_compress` under System V AMD64

The #882 pilot theorem for

    void sha256_compress(uint32_t state[8], const uint8_t block[64]);

compiled by clang 18.1.3 at `-O2` (`xcompile/wrappers/xc_sha256.c`), stated
over `Silmaril.X86.Ext`'s memory-backed machine and `Silmaril.X86.sysv64`.
The bytes it is about are `Sha256O2.image`, from `Sha256O2/Image.lean`.

This is the `-O2` instance of the contract shape Track 2b wrote for `-O0`. It
quotes the same `Machine.CallingConvention`, the same `X86.sysv64`, the same
`Process.Memory.WritesWithin` footprint predicate and the same
`Process.Region` disjointness; only the image, the frame size and the
relocation offset differ. See "Relation to the `-O0` contract" below for what
should be factored once both land.

## Shape

`Contract L frame` is the whole statement: from any `SysVEntry` state, any run
that returns to `L.exit` lands in a `Post` state. `sha256_compress_O2` claims
it at `frame = frameSize = 6 * 8 + 0xa8 = 216`. `Live` and `Realisable` are
the two non-vacuity obligations, discussed below. Both are **proved**: `Live`
as `Sha256O2/Exec.lean`'s `sha256_compress_O2_live`, and `Realisable` by
`realisable_of_geometry` and `realisable_concrete` at the end of this file.

## Endianness

Getting this backwards would make the theorem wrong rather than weak, so, to
be explicit:

* `state` is `uint32_t *`. On x86-64 a `uint32_t` is stored **little-endian**,
  so the eight hash words are the eight little-endian 4-byte groups at
  `state[0..32)`. `leWordAt` reads them and `stateOf` collects them into an
  `InitHash`.
* `block` is `const uint8_t *`, and the C builds each message word
  big-endian. At `-O2` clang implements that with a 32-bit load followed by
  `bswap` (`8b 0c 86` / `0f c9` at function offset `0x20`), rather than the
  four `movzbl`/`shl`/`or` of `-O0`; the *value* is the same, so `beWordAt` is
  shared with the `-O0` statement and only the proof differs.
* `K[]` is `uint32_t`, so it too is **little-endian** in `.rodata`.

So `state` and `K` are read little-endian and `block` big-endian, and that is
not a mistake.

## The `K` table is a precondition on *contents*, not just on permissions

`sha256_compress` reaches its constant schedule through

    d4:  48 8d 0d <disp32>    lea  K(%rip), %rcx

and then reads `K[t]` out of `.rodata` in the round loop. **What the function
computes therefore depends on what is in `.rodata`.** A contract that only
required `[rodataBase, rodataBase + 256)` to be *readable* would be false as
soon as it was non-vacuous: load the image with any other 256 bytes there and
the postcondition "`state` holds `SHA256.Kernel.compress …`" fails.

`SysVEntry.kTable` accordingly pins the bytes:
`m.memory.readBytes L.rodataBase.toNat 256 = some Sha256O2.kBytes`, with
`kBytes` the 256 bytes actually in the pinned object. `kBytes_eq_spec` then
checks by `decide` that those bytes are the little-endian encodings of
`Silmaril.Crypto.SHA256.Kernel.K0 … K63` — i.e. that the object's table really is the
FIPS 180-4 constant schedule and not merely 256 plausible-looking bytes. That
check is what makes the precondition a statement about SHA-256 rather than
about an opaque blob, and it is the bridge the round-loop proof will use to
rewrite a `.rodata` load into a spec constant.

This is a **difference from the `-O0` draft**, which requires only
`Permitted .read` on the `K` range. See "Relation to the `-O0` contract".

## Why `Ext.Returns` and not `wp_block`

`Silmaril/Crypto/X86/ProgramLogic.lean`'s `wp_block` runs a list of
instructions over `Silmaril.X86.State`, which is registers, RIP and flags and
**has no memory component at all**. It therefore cannot express a load, a
store, or a footprint. The vehicle is `Ext.Returns exit initial final` over
`Ext.MState` (`{ core : X86.State, memory : Process.Memory }`).

## Why `Process.Region` and not `Crypto.X86.Region`

`Silmaril/Crypto/X86/Contract.lean`'s `Regions.Disjoint` compares
`base + BitVec.ofNat 64 size` with `BitVec` `≤`, which wraps modulo `2^64`;
`Crypto.X86.not_disjoint_of_wrap` exhibits two non-wrapping regions that
overlap and that it still calls disjoint. This module uses
`Silmaril.Process.Region`, whose `base`, `size` and `Disjoint` are all over
`Nat`, matching the `Nat`-indexed `Process.Memory`.

## The footprint, and why `-O2` is the tight case

`Footprint` is `state[0..32)` together with
`[rspEntry − frame − 128, rspEntry)`, the frame and the System V red zone, as
#882 asks. At `frame = 216` the floor is `rspEntry - 344`.

**At `-O2` that bound is exactly attained.** The function's own `%rsp` is
`rspEntry - 216`, and `mov %r12d,-0x80(%rsp)` writes at `rspEntry - 344`. So
unlike `-O0`, which leaves four bytes of slack, the `-128` red-zone term here
is load-bearing to the byte: a statement without it would be **false**, not
merely weaker. This is the sharpest evidence in the pilot for #882's insistence
that the red zone appear in the modifies set.

The `w[]` array runs up to `rsp + 160 = rspEntry - 56`, and the six callee-saved
pushes occupy `[rspEntry - 48, rspEntry)`, so the whole footprint is used and
nothing above `rspEntry` is written.

## What this says, and what it does not

Checked against #882 clause by clause.

**Captured as asked.**
* `rdi = state`, `rsi = block` (`SysVEntry.argState`, `.argBlock`), tied to the
  convention by `sysv64_argRegs`.
* `state[0..32)`, `block[0..64)`, the code, the `.rodata` `K` table and the
  stack frame valid and pairwise disjoint: `SysVEntry.mapped` clauses and
  `.disjoint` over the six `regions`, with `Region.Disjoint` over `Nat`.
* `rsp ≡ 8 (mod 16)` at entry: `SysVEntry.aligned`, which is
  `sysv64.EntryAligned`, definitionally `rspEntry.toNat % 16 = 8`.
* Return address at `[rsp]`: `SysVEntry.returnAddress`, matching
  `sysv64.returnAddress = .onStack 0`.
* `state[]` holds `Spec.compress` of the entry words: `Post.compressed`.
* `rsp` restored: `Post.rsp`. **Convention:** `final` is the state *after* the
  `ret` has executed, so the claim is `rsp = rspEntry + 8`, the entry value
  plus the eight bytes of return address the `ret` popped.
* Callee-saved `rbx, rbp, r12, r13, r14, r15` restored: `Post.saved`, as
  `sysv64.Preserved`, so the register list comes from the convention record
  rather than being repeated here. All six are genuinely at risk at `-O2`:
  the prologue pushes every one of them and the body uses all six as ordinary
  scratch, `%rbp` included — there is no frame pointer.
* Modifies set: `Post.untouched`, as
  `Memory.WritesWithin initial.memory final.memory (Footprint …)`.
* Caller-saved registers and flags are unconstrained: `Post` does not mention
  them.

**Stronger than asked, deliberately.**
* The return-address slot `[rspEntry, rspEntry + 8)` is *outside* the
  footprint, so the theorem says the function does not scribble on its own
  return address.
* `block[]`, the code and the `K` table are outside the footprint too, so
  their preservation is a consequence of `Post.untouched` and
  `SysVEntry.disjoint`; `block_unchanged` derives it.
* `WritesWithin` freezes `regions`, so a run that unmapped a page does not
  count as having written nothing.
* `Ext.Returns` is itself a strong fault-freedom claim: every intermediate
  step is `stepOpt = some`, i.e. `Outcome.retired`, so **nowhere in the run**
  is there a data fault, a fetch fault, an undecodable byte, a `ud2` trap, a
  `#DE`, or a branch on an undefined flag.

**Weakened, or not said.**
* Nothing is said about *timing*, about flags, or about caller-saved
  registers. That is intended.
* The red-zone bound is `sysv64.redZone = 128`, the ABI bound. At `-O2` it is
  also the tight bound, which is a coincidence worth not relying on.
* `SysVEntry.stateAligned` records that `uint32_t *state` is 4-byte aligned.
  **The model does not need it**: `Ext` has no alignment check. It is carried
  because it is part of the C-level contract and because an AArch64 or RV64
  instance of the same statement will need it.
* Only the `INTEGER` class of System V is modelled.

**Where it could be vacuous, and whether that is closed.**

The statement has the shape `SysVEntry → Returns → Post`. Two antecedents can
be empty, and #882's failure mode — "satisfied by a machine that never runs" —
is exactly the second.

1. **No run returns.** `Live` is the obligation that closes this, and it is
   **closed**: `Sha256O2/Exec.lean` proves `sha256_compress_O2_live`, with
   `#print axioms` giving `[propext, Classical.choice, Quot.sound]` and no
   `sorryAx`. The pilot theorem is no longer satisfiable by a machine that
   never runs.

   It got there in two stages, and both are worth keeping because the
   distinction between them is the useful part. First the *decoding*
   obstruction went: Track 1's P1 band landed every form this image needs, and
   `Sha256O2/Decode.lean` proves by `rfl` that `Ext.decode` consumes all 459
   bytes in 133 canonical instructions (`decodeLengths_raw`,
   `instructionLengths_sum`). That did **not** make the theorem non-vacuous —
   it moved the obstruction from decoding to execution. Then the execution
   obstruction went too: every step retires, with no data fault on any
   `%rsp`-relative access, no fetch fault, no undecodable byte, no `ud2`, no
   `#DE` and no branch on an undefined flag, and all three counted loops
   terminate.

   Because `Ext.Returns` requires every step to retire, `Live` is also a
   fault-freedom claim over all 133 instructions.
2. **No entry state exists.** `Realisable` is that obligation. It is now
   closed: `realisable_of_geometry` exhibits an entry state for every layout
   and choice of buffers whose six regions fit and do not overlap, and
   `realisable_concrete` discharges those side conditions at fixed addresses,
   so `Realisable` holds with no hypotheses for at least one layout. The state
   is built by `Silmaril/X86/EntryState.lean`, shared with the other
   optimisation levels. `Layout.RelocFits` is a real constraint on the layout,
   not a formality.

Both non-vacuity obligations are therefore discharged, and the one remaining
gap in this track is `compressed_O2`, which is named in this file and in the
module doc above.

**A trap that is closed.** `Contract` would be **false**, not weak, if it
quantified over an arbitrary code image: `sha256_compress` is not position
independent, and `image textBase rodataBase` is the relocated byte string. It
would also be false for a layout in which the `R_X86_64_PC32` displacement
does not fit in 32 bits, because `image` would then store a truncated
displacement and the `lea` would compute the wrong address for `K`. That is
why `Layout.RelocFits` is a precondition. And, as above, it would be false
without `SysVEntry.kTable` pinning the constant schedule.

## Relation to the `-O0` contract

`Layout`, `byteAt`, `leWordAt`, `beWordAt`, `stateOf`, `compressBlock`,
`StateHolds`, `Footprint`, `SysVEntry`, `Post`, `Contract`, `Live` and
`Realisable` have the same shape here as in Track 2b's `-O0` statement; what
differs is `image`, `size`, `relocOffset` and `frameSize`, all four of which
come from `Sha256O2/Image.lean`. They were written out here because Track 2b's
`Silmaril/Crypto/X86/Sha256O0.lean` was not yet importable; it now is, so the
reason has lapsed and the duplication is a deliberate deferral rather than a
necessity. Factoring the two into one module parametric in those four
constants is the right end state, and is **not** done here: it would rewrite
the headline statement of two open PRs, which is exactly what the
statement-first rule exists to prevent.

**These definitions should be factored into one module parametric in
(image, size, relocOffset) once both files exist**, with `Sha256O0` and
`Sha256O2` as two instances. That is a deliberate note, not an oversight: the
duplication is temporary and the shapes were kept identical precisely so the
factoring is mechanical.

One difference is **not** cosmetic and should survive the factoring:
`SysVEntry.kTable` here pins the 256 `K` bytes, where the `-O0` draft requires
only that the range be readable. The `-O0` contract needs the same
strengthening for the same reason — its `lea`/`mov (%rcx,%rax,4),%ecx` pair
reads the same table — and is false without it once `Live` holds.
-/

@[expose] public section

namespace Silmaril.Crypto.X86.Sha256O2

open Silmaril.Process (Memory Region Byte Permissions)
open Silmaril.X86 (Word Reg MState sysv64)
open Silmaril.X86.Ext (Returns leBytes)
open Silmaril.Crypto.SHA256.Kernel (InitHash compress)

/-! ## Reading the buffers -/

/-- The byte at index `i`, or zero past the end. The preconditions make every
index this module uses in range. -/
def byteAt (bytes : List Byte) (i : Nat) : Byte := bytes.getD i 0

/-- The `i`-th **little-endian** `uint32` of a byte list: how `uint32_t
state[8]` and `uint32_t K[64]` sit in memory on x86-64. -/
def leWordAt (bytes : List Byte) (i : Nat) : SHA256.Kernel.Word :=
  (byteAt bytes (4 * i)).setWidth 32 |||
    ((byteAt bytes (4 * i + 1)).setWidth 32 <<< 8) |||
    ((byteAt bytes (4 * i + 2)).setWidth 32 <<< 16) |||
    ((byteAt bytes (4 * i + 3)).setWidth 32 <<< 24)

/-- The `i`-th **big-endian** `uint32` of a byte list: how the C reads
`const uint8_t block[64]` into a message word. At `-O2` clang implements this
as a 32-bit load plus `bswap`. -/
def beWordAt (bytes : List Byte) (i : Nat) : SHA256.Kernel.Word :=
  ((byteAt bytes (4 * i)).setWidth 32 <<< 24) |||
    ((byteAt bytes (4 * i + 1)).setWidth 32 <<< 16) |||
    ((byteAt bytes (4 * i + 2)).setWidth 32 <<< 8) |||
    (byteAt bytes (4 * i + 3)).setWidth 32

/-- The eight little-endian `uint32` of `state[]`, as a spec hash value. -/
def stateOf (bytes : List Byte) : InitHash :=
  ⟨leWordAt bytes 0, leWordAt bytes 1, leWordAt bytes 2, leWordAt bytes 3,
   leWordAt bytes 4, leWordAt bytes 5, leWordAt bytes 6, leWordAt bytes 7⟩

/-- `SHA256.Kernel.compress` applied to a hash value and the sixteen big-endian
message words of a 64-byte block. -/
def compressBlock (H : InitHash) (block : List Byte) : InitHash :=
  compress H
    (beWordAt block 0) (beWordAt block 1) (beWordAt block 2) (beWordAt block 3)
    (beWordAt block 4) (beWordAt block 5) (beWordAt block 6) (beWordAt block 7)
    (beWordAt block 8) (beWordAt block 9) (beWordAt block 10) (beWordAt block 11)
    (beWordAt block 12) (beWordAt block 13) (beWordAt block 14) (beWordAt block 15)

/-- The thirty-two bytes at `state`, read back as eight little-endian
`uint32`, are `H`. -/
def StateHolds (memory : Memory) (state : Word) (H : InitHash) : Prop :=
  ∃ bytes, memory.readBytes state.toNat 32 = some bytes ∧ stateOf bytes = H

/-! ## The object's `K` table is the FIPS 180-4 schedule

The sixty-four little-endian words of `Sha256O2.kBytes` are
`SHA256.Kernel.K0 … SHA256.Kernel.K63`. This is the link between the bytes the compiled code
loads from `.rodata` and the constants the specification names; without it,
`SysVEntry.kTable` would pin an opaque blob. -/

/-- The sixty-four constants of the specification, in order. -/
def specK : List SHA256.Kernel.Word :=
  [SHA256.Kernel.K0,  SHA256.Kernel.K1,  SHA256.Kernel.K2,  SHA256.Kernel.K3,  SHA256.Kernel.K4,  SHA256.Kernel.K5,
   SHA256.Kernel.K6,  SHA256.Kernel.K7,  SHA256.Kernel.K8,  SHA256.Kernel.K9,  SHA256.Kernel.K10, SHA256.Kernel.K11,
   SHA256.Kernel.K12, SHA256.Kernel.K13, SHA256.Kernel.K14, SHA256.Kernel.K15, SHA256.Kernel.K16, SHA256.Kernel.K17,
   SHA256.Kernel.K18, SHA256.Kernel.K19, SHA256.Kernel.K20, SHA256.Kernel.K21, SHA256.Kernel.K22, SHA256.Kernel.K23,
   SHA256.Kernel.K24, SHA256.Kernel.K25, SHA256.Kernel.K26, SHA256.Kernel.K27, SHA256.Kernel.K28, SHA256.Kernel.K29,
   SHA256.Kernel.K30, SHA256.Kernel.K31, SHA256.Kernel.K32, SHA256.Kernel.K33, SHA256.Kernel.K34, SHA256.Kernel.K35,
   SHA256.Kernel.K36, SHA256.Kernel.K37, SHA256.Kernel.K38, SHA256.Kernel.K39, SHA256.Kernel.K40, SHA256.Kernel.K41,
   SHA256.Kernel.K42, SHA256.Kernel.K43, SHA256.Kernel.K44, SHA256.Kernel.K45, SHA256.Kernel.K46, SHA256.Kernel.K47,
   SHA256.Kernel.K48, SHA256.Kernel.K49, SHA256.Kernel.K50, SHA256.Kernel.K51, SHA256.Kernel.K52, SHA256.Kernel.K53,
   SHA256.Kernel.K54, SHA256.Kernel.K55, SHA256.Kernel.K56, SHA256.Kernel.K57, SHA256.Kernel.K58, SHA256.Kernel.K59,
   SHA256.Kernel.K60, SHA256.Kernel.K61, SHA256.Kernel.K62, SHA256.Kernel.K63]

set_option maxRecDepth 20000 in
/-- The 256 `.rodata` bytes of `sha256_compress.K`, read as little-endian
`uint32`, are exactly the specification's constant schedule. Machine-checked
against the object, so the contract's `K` precondition is a claim about
SHA-256 and not about an opaque blob. -/
theorem kBytes_eq_spec : (List.range 64).map (leWordAt kBytes) = specK := by
  decide

/-! ## The layout -/

/-- Where the loader put the function and its `.rodata`, and where it must
return to. -/
structure Layout where
  /-- Load address of the `sha256_compress` image. -/
  textBase : Word
  /-- Load address of `.rodata`, hence of `sha256_compress.K`. -/
  rodataBase : Word
  /-- The address the function must return to: what the caller's `call`
  pushed. -/
  exit : Word

/-- The displacement the single `R_X86_64_PC32` relocation computes,
`S + A - P`, before truncation to 32 bits. -/
def Layout.relocValue (L : Layout) : Word :=
  L.rodataBase - L.textBase - BitVec.ofNat 64 (relocOffset + 4)

/-- The constraint a static linker enforces on the layout: the displacement
fits in the signed 32-bit field. If it does not, `image` stores a truncated
displacement and the `lea` computes the wrong address for `K`, so the contract
would be **false** rather than merely weak. -/
def Layout.RelocFits (L : Layout) : Prop :=
  (L.relocValue.setWidth 32).signExtend 64 = L.relocValue

/-! ## Regions

Six regions, over `Silmaril.Process.Region`: `base` and `size` are `Nat` and
`Region.Disjoint` is the `Nat` statement, so nothing here wraps at `2^64`. -/

/-- `uint32_t state[8]`: 32 bytes, read-write. The output buffer. -/
def stateRegion (state : Word) : Region :=
  ⟨state.toNat, 32, { read := true, write := true, execute := false }⟩

/-- `const uint8_t block[64]`: 64 bytes, read-only. -/
def blockRegion (block : Word) : Region :=
  ⟨block.toNat, 64, { read := true, write := false, execute := false }⟩

/-- The `.text` of `sha256_compress`: readable and executable, not writable. -/
def codeRegion (L : Layout) : Region :=
  ⟨L.textBase.toNat, size, { read := true, write := false, execute := true }⟩

/-- The 256 bytes of `sha256_compress.K` at the base of `.rodata`. -/
def kTableRegion (L : Layout) : Region :=
  ⟨L.rodataBase.toNat, kSize, { read := true, write := false, execute := false }⟩

/-- The stack the callee owns: its frame `[rspEntry − frame, rspEntry)`
together with the `sysv64.redZone` bytes below it that a System V leaf may use
without moving `%rsp`. `frame` is measured from the entry `%rsp`, so it counts
the six callee-saved pushes as well as the `sub`. -/
def frameRegion (rspEntry : Word) (frame : Nat) : Region :=
  ⟨sysv64.frameFloor rspEntry.toNat frame, sysv64.frameExtent frame,
   { read := true, write := true, execute := false }⟩

/-- The eight bytes at `[rspEntry, rspEntry + 8)` holding the return address.
Deliberately **not** part of the footprint. -/
def returnSlot (rspEntry : Word) : Region :=
  ⟨rspEntry.toNat, 8, { read := true, write := true, execute := false }⟩

/-- The six regions the contract requires to be pairwise disjoint. -/
def regions (L : Layout) (state block rspEntry : Word) (frame : Nat) : List Region :=
  [stateRegion state, blockRegion block, codeRegion L, kTableRegion L,
   frameRegion rspEntry frame, returnSlot rspEntry]

/-! ## The modifies set -/

/-- The footprint: the output buffer `state[0..32)` and the stack the callee
owns, `[rspEntry − frame − 128, rspEntry)`. Everything else — `block[]`, the
code, the `K` table, the return-address slot, the caller's frames and anything
else mapped — is outside it.

At `frame = frameSize = 216` the lower bound is `rspEntry - 344`, and the
image attains it exactly; see the module doc. -/
def Footprint (state rspEntry : Word) (frame : Nat) (address : Nat) : Prop :=
  (stateRegion state).Contains address ∨ (frameRegion rspEntry frame).Contains address

/-! ## Backing of the two input buffers

`Memory.Permitted .read` says a span is *mapped readable*; it does not say the
bytes are *backed*. An unbacked byte inside a mapped region passes the
permission check and then `readBacking` returns `none`, so the load is a
`dataFault`. A postcondition conditioned on `readBytes … = some _` is
satisfied vacuously when the read fails, so a capability suffices for `Post`;
a liveness claim has to *rule the failure out*, so it needs the fact.

The general test, which catches this whole class: **for every precondition
phrased as a capability — `Permitted`, `Disjoint` — ask whether the theorem
that consumes it needs the corresponding fact. `Post` can live on
capabilities; `Live` cannot.**

These are the same definitions as Track 2b's `Sha256O0.StateReads` and
`Sha256O0.BlockReads`, so the two contracts stay literally sisters. Note the
deliberate asymmetry: **the frame and the red zone keep permission only**,
because a fresh stack frame *is* a mapped-but-unbacked region and requiring
backing there would make the precondition unsatisfiable by any real caller.
That the function never reads an unwritten slot is the proof's obligation, not
a precondition. -/

/-- `state[]` is not merely mapped but **backed**: all 32 bytes read. -/
def StateReads (memory : Memory) (state : Word) : Prop :=
  ∃ bytes, memory.readBytes state.toNat 32 = some bytes

/-- `block[]` is not merely mapped but **backed**: all 64 bytes read. -/
def BlockReads (memory : Memory) (block : Word) : Prop :=
  ∃ bytes, memory.readBytes block.toNat 64 = some bytes

/-- Backing subsumes permission, so replacing the old `Permitted .read`
clauses by these loses nothing. -/
theorem StateReads.permitted {memory : Memory} {state : Word} (h : StateReads memory state) :
    memory.Permitted .read state.toNat 32 := by
  obtain ⟨bytes, hb⟩ := h
  exact Memory.readWith_permitted hb

theorem BlockReads.permitted {memory : Memory} {block : Word} (h : BlockReads memory block) :
    memory.Permitted .read block.toNat 64 := by
  obtain ⟨bytes, hb⟩ := h
  exact Memory.readWith_permitted hb

/-! ## Preconditions -/

/-- A System V AMD64 entry state for `sha256_compress`, with the clang `-O2`
image loaded at `L.textBase`. -/
structure SysVEntry (L : Layout) (state block rspEntry : Word) (frame : Nat)
    (m : MState) : Prop where
  /-- Execution starts at the first byte of the function. -/
  rip : m.core.rip = L.textBase
  /-- The relocated image is loaded, and readable as executable bytes. -/
  code : m.memory.fetchBytes L.textBase.toNat size = some (image L.textBase L.rodataBase)
  /-- The layout keeps the `R_X86_64_PC32` displacement in range. -/
  relocFits : L.RelocFits
  /-- The 256 bytes at `.rodata` **are** `sha256_compress.K`. Not merely
  readable: what the function computes depends on them, and `kBytes_eq_spec`
  identifies them with `SHA256.Kernel.K0 … K63`. See the module doc. -/
  kTable : m.memory.readBytes L.rodataBase.toNat kSize = some kBytes
  /-- First integer argument, `sysv64.intArgRegs[0] = rdi`: `uint32_t *state`. -/
  argState : m.core.read .rdi = state
  /-- Second integer argument, `sysv64.intArgRegs[1] = rsi`:
  `const uint8_t *block`. -/
  argBlock : m.core.read .rsi = block
  /-- The entry stack pointer. -/
  rsp : m.core.read .rsp = rspEntry
  /-- `rsp ≡ 8 (mod 16)` at entry: the caller was 16-byte aligned and the
  `call` pushed eight bytes. -/
  aligned : sysv64.EntryAligned rspEntry.toNat
  /-- The return address is at `[rsp]`, per `sysv64.returnAddress = .onStack 0`. -/
  returnAddress : m.memory.readBytes rspEntry.toNat 8 = some (leBytes L.exit 8)
  /-- `state[]` is **backed**, not merely mapped: see above. -/
  stateReads : StateReads m.memory state
  /-- `state[]` is writable. -/
  stateWritable : m.memory.Permitted .write state.toNat 32
  /-- `block[]` is **backed**, not merely mapped: see above. -/
  blockReads : BlockReads m.memory block
  /-- The frame and the red zone are readable and writable. -/
  frameMapped :
    m.memory.Permitted .read (sysv64.frameFloor rspEntry.toNat frame)
        (sysv64.frameExtent frame) ∧
      m.memory.Permitted .write (sysv64.frameFloor rspEntry.toNat frame)
        (sysv64.frameExtent frame)
  /-- The frame and red zone fit below the entry stack pointer, so the
  subtraction in `frameFloor` does not truncate. -/
  frameFits : sysv64.frameExtent frame ≤ rspEntry.toNat
  /-- No region runs off the top of the address space. -/
  noWrap : ∀ r ∈ regions L state block rspEntry frame,
    r.base + r.size ≤ Silmaril.Process.addressLimit
  /-- The six regions are pairwise disjoint. -/
  disjoint : (regions L state block rspEntry frame).Pairwise Region.Disjoint
  /-- `uint32_t *` is 4-byte aligned. The machine does not check alignment, so
  this is a C-level precondition carried deliberately; see the module doc. -/
  stateAligned : state.toNat % 4 = 0

/-! ## Postconditions -/

/-- The state at the `ret`. `final` is the state **after** the `ret` executed,
so `rsp` is the entry value plus the eight bytes the `ret` popped. -/
structure Post (L : Layout) (state block rspEntry : Word) (frame : Nat)
    (initial final : MState) : Prop where
  /-- `state[]` holds `Spec.compress` of its entry words and the sixteen
  big-endian words of `block[]`. -/
  compressed : ∀ stateBytes blockBytes,
    initial.memory.readBytes state.toNat 32 = some stateBytes →
    initial.memory.readBytes block.toNat 64 = some blockBytes →
    StateHolds final.memory state (compressBlock (stateOf stateBytes) blockBytes)
  /-- `rsp` restored, with the return address consumed. -/
  rsp : final.core.read .rsp = rspEntry + 8#64
  /-- The six System V callee-saved registers are restored. At `-O2` all six
  are pushed by the prologue and used as scratch by the body. -/
  saved : sysv64.Preserved initial.core.read final.core.read
  /-- Memory outside the footprint is byte-for-byte unchanged, and no mapping
  changed. -/
  untouched : Memory.WritesWithin initial.memory final.memory (Footprint state rspEntry frame)

/-! ## The contract -/

/-- The pilot contract for a layout and a frame size. -/
def Contract (L : Layout) (frame : Nat) : Prop :=
  ∀ state block rspEntry initial final,
    SysVEntry L state block rspEntry frame initial →
    Returns L.exit initial final →
    Post L state block rspEntry frame initial final

/-- **Non-vacuity obligation 1.** From a System V entry state the machine
really does run to the `ret`.

**Proved**, as `Sha256O2/Exec.lean`'s `sha256_compress_O2_live` — stated here
and discharged there, because the proof consumes the symbolic execution. The
statement is unchanged from this branch's first contract commit; nothing was
weakened to reach it. See the module doc. -/
def Live (L : Layout) (frame : Nat) : Prop :=
  ∀ state block rspEntry initial,
    SysVEntry L state block rspEntry frame initial →
    ∃ final, Returns L.exit initial final

/-- **Non-vacuity obligation 2.** Some state satisfies the preconditions.
**Proved**, below: `realisable_of_geometry` builds an entry state for every
layout whose six regions fit and do not overlap, and `realisable_concrete`
instantiates it at fixed addresses, so `Realisable` holds unconditionally for at
least one layout. The state is built by `Silmaril.X86.EntryState`, which is
shared with the other optimisation levels. -/
def Realisable (L : Layout) (frame : Nat) : Prop :=
  ∃ state block rspEntry m, SysVEntry L state block rspEntry frame m

/-! ## The convention, quoted rather than repeated -/

/-- The argument registers come from the convention record, not from this
file. -/
theorem sysv64_argRegs :
    sysv64.intArgReg? 0 = some Reg.rdi ∧ sysv64.intArgReg? 1 = some Reg.rsi := by
  decide

/-- The return address is at `[rsp]`, per the convention record. -/
theorem sysv64_returnAddress :
    sysv64.returnAddress = Silmaril.Machine.ReturnAddress.onStack 0 := rfl

/-- The footprint floor at this image's frame size is `rspEntry - 344`, which
is `rspEntry - F - 128` for `F = 216`. The image attains it exactly, at
`mov %r12d,-0x80(%rsp)`; see the module doc. -/
theorem frameFloor_frameSize (rspEntry : Word) :
    sysv64.frameFloor rspEntry.toNat frameSize = rspEntry.toNat - 344 := by
  simp only [Silmaril.Machine.CallingConvention.frameFloor, frameSize_eq,
    Silmaril.X86.sysv64_redZone]
  omega

/-! ## The pilot theorem

**The data invariant**, `compressed_O2` — `state[]` holds `Spec.compress` of
its entry words and the sixteen big-endian words of `block[]` — is proved in
`Sha256O2/Exec.lean`, not here: it is `Post.compressed` and nothing else, but
the proof needs the execution lemmas, and `Sha256O2/Exec.lean` imports this
file rather than the other way around, so the declaration lives there. -/

/-- `block[]` is not written: it lies outside the footprint, so
`Post.untouched` and `SysVEntry.disjoint` give it back unchanged. Stated
separately because it is the clause a caller actually wants.

It is a consequence of the footprint, not of the mathematics: `block[]` is
disjoint from both halves of the modifies set, so `Post.untouched` returns it
unchanged. -/
theorem block_unchanged (L : Layout) (state block rspEntry : Word) (frame : Nat)
    (initial final : MState)
    (hentry : SysVEntry L state block rspEntry frame initial)
    (hpost : Post L state block rspEntry frame initial final) :
    final.memory.readBytes block.toNat 64 = initial.memory.readBytes block.toNat 64 := by
  have hp := hentry.disjoint
  simp only [regions, List.pairwise_cons, List.mem_cons] at hp
  have hsb : Region.Disjoint (stateRegion state) (blockRegion block) := hp.1 _ (by simp)
  have hbf : Region.Disjoint (blockRegion block) (frameRegion rspEntry frame) :=
    hp.2.1 _ (by simp)
  refine Memory.WritesWithin.readBytes hpost.untouched ?_
  intro o ho
  rintro (hs | hf)
  · simp only [stateRegion, blockRegion, Region.Disjoint, Region.Contains] at hsb hs
    omega
  · simp only [blockRegion, frameRegion, Region.Disjoint, Region.Contains] at hbf hf
    omega

/-! ## Non-vacuity: `Realisable` is proved

The precondition is only worth proving things from if something satisfies it.
`realisable_of_geometry` exhibits an entry state for every layout and every
choice of buffers whose regions fit in the address space and do not overlap, and
`realisable_concrete` discharges those side conditions at fixed addresses, so
the precondition is non-vacuous outright, not merely under hypotheses.

The state comes from `Silmaril.X86.EntryState`: the six regions below with
their backing, and a register file with RIP at the entry, the two arguments in
RDI and RSI and RSP at the entry stack pointer. The side conditions of
`realisable_of_geometry` are exactly `SysVEntry`'s own geometric fields —
`relocFits`, `aligned`, `frameFits`, `stateAligned`, `noWrap` and `disjoint` —
and nothing else: every clause about *contents* is discharged by the builder.
-/

/-- The six regions of `regions`, with backing. `state[]` and `block[]` are
backed by zeros — the contract only asks that they read, not what they hold —
the code by the relocated image, `.rodata` by `kBytes`, and `[rsp]` by the
return address. The frame is deliberately left **unbacked**: a fresh stack frame
is exactly a mapped-but-unbacked region, which is why `SysVEntry.frameMapped`
asks for permission and not for backing. -/
def placements (L : Layout) (state block rspEntry : Word) (frame : Nat) :
    List Silmaril.X86.EntryState.Placement :=
  [⟨stateRegion state, some (List.replicate 32 0)⟩,
   ⟨blockRegion block, some (List.replicate 64 0)⟩,
   ⟨codeRegion L, some (image L.textBase L.rodataBase)⟩,
   ⟨kTableRegion L, some kBytes⟩,
   ⟨frameRegion rspEntry frame, none⟩,
   ⟨returnSlot rspEntry, some (leBytes L.exit 8)⟩]

/-- The placements map onto exactly the regions the contract names. -/
theorem placements_regions (L : Layout) (state block rspEntry : Word) (frame : Nat) :
    (placements L state block rspEntry frame).map Silmaril.X86.EntryState.Placement.region =
      regions L state block rspEntry frame := rfl

/-- The builder's side conditions are the contract's own `noWrap` and
`disjoint`, plus the four backing lengths, which are arithmetic. -/
theorem placements_wf {L : Layout} {state block rspEntry : Word} {frame : Nat}
    (noWrap : ∀ r ∈ regions L state block rspEntry frame,
      r.base + r.size ≤ Silmaril.Process.addressLimit)
    (disjoint : (regions L state block rspEntry frame).Pairwise Region.Disjoint) :
    Silmaril.X86.EntryState.WF (placements L state block rspEntry frame) where
  backing_length := by
    rintro p hp bs hbs
    simp only [placements, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Option.some.injEq, reduceCtorEq] at hbs <;> subst hbs <;>
      simp [stateRegion, blockRegion, codeRegion, kTableRegion, returnSlot]
  noWrap := by
    intro p hp
    exact noWrap p.region (placements_regions L state block rspEntry frame ▸
      List.mem_map_of_mem hp)
  disjoint := placements_regions L state block rspEntry frame ▸ disjoint

/-- The entry state the builder produces for this contract. -/
def entryState (L : Layout) (state block rspEntry : Word) (frame : Nat) : MState :=
  Silmaril.X86.EntryState.build
    (Silmaril.X86.EntryState.sysvCore (Silmaril.X86.EntryState.blankCore L.textBase) L.textBase state block rspEntry)
    (placements L state block rspEntry frame)

/-- **`entryState` satisfies the precondition.** Every clause about contents —
the code fetches back as the image, `K` reads back as `kBytes`, the buffers are
backed with the right permissions, the return address is at `[rsp]`, the frame
is mapped read-write, the registers hold the arguments — is discharged by
`Silmaril.X86.EntryState`. What is left are exactly `SysVEntry`'s own geometric
fields, which are the hypotheses. -/
theorem entryState_sysVEntry {L : Layout} {state block rspEntry : Word} {frame : Nat}
    (relocFits : L.RelocFits)
    (aligned : sysv64.EntryAligned rspEntry.toNat)
    (frameFits : sysv64.frameExtent frame ≤ rspEntry.toNat)
    (stateAligned : state.toNat % 4 = 0)
    (noWrap : ∀ r ∈ regions L state block rspEntry frame,
      r.base + r.size ≤ Silmaril.Process.addressLimit)
    (disjoint : (regions L state block rspEntry frame).Pairwise Region.Disjoint) :
    SysVEntry L state block rspEntry frame (entryState L state block rspEntry frame) := by
  have wf := placements_wf noWrap disjoint
  have hstate : (⟨stateRegion state, some (List.replicate 32 0)⟩ : Silmaril.X86.EntryState.Placement) ∈
      placements L state block rspEntry frame := by simp [placements]
  have hblock : (⟨blockRegion block, some (List.replicate 64 0)⟩ : Silmaril.X86.EntryState.Placement) ∈
      placements L state block rspEntry frame := by simp [placements]
  have hcode : (⟨codeRegion L, some (image L.textBase L.rodataBase)⟩ : Silmaril.X86.EntryState.Placement) ∈
      placements L state block rspEntry frame := by simp [placements]
  have hk : (⟨kTableRegion L, some kBytes⟩ : Silmaril.X86.EntryState.Placement) ∈
      placements L state block rspEntry frame := by simp [placements]
  have hframe : (⟨frameRegion rspEntry frame, none⟩ : Silmaril.X86.EntryState.Placement) ∈
      placements L state block rspEntry frame := by simp [placements]
  have hret : (⟨returnSlot rspEntry, some (leBytes L.exit 8)⟩ : Silmaril.X86.EntryState.Placement) ∈
      placements L state block rspEntry frame := by simp [placements]
  have frameSizePos : 0 < (frameRegion rspEntry frame).size := by
    show 0 < sysv64.frameExtent frame
    have extent : sysv64.frameExtent frame = frame + 128 := rfl
    omega
  have statePos : 0 < (stateRegion state).size := by simp [stateRegion]
  have blockPos : 0 < (blockRegion block).size := by simp [blockRegion]
  have codePos : 0 < (codeRegion L).size := by simp [codeRegion, size]
  have kPos : 0 < (kTableRegion L).size := by simp [kTableRegion, kSize]
  have retPos : 0 < (returnSlot rspEntry).size := by simp [returnSlot]
  exact
    { rip := rfl
      code := Silmaril.X86.EntryState.fetchBytes_blob wf hcode rfl rfl codePos
      relocFits := relocFits
      kTable := Silmaril.X86.EntryState.readBytes_blob wf hk rfl rfl kPos
      argState := Silmaril.X86.EntryState.sysvCore_rdi _ _ _ _ _
      argBlock := Silmaril.X86.EntryState.sysvCore_rsi _ _ _ _ _
      rsp := Silmaril.X86.EntryState.sysvCore_rsp _ _ _ _ _
      aligned := aligned
      returnAddress := Silmaril.X86.EntryState.readBytes_blob wf hret rfl rfl retPos
      stateReads := ⟨_, Silmaril.X86.EntryState.readBytes_blob wf hstate rfl rfl statePos⟩
      stateWritable := Silmaril.X86.EntryState.permitted_region wf hstate rfl statePos
      blockReads := ⟨_, Silmaril.X86.EntryState.readBytes_blob wf hblock rfl rfl blockPos⟩
      frameMapped :=
        ⟨Silmaril.X86.EntryState.permitted_region wf hframe rfl frameSizePos,
         Silmaril.X86.EntryState.permitted_region wf hframe rfl frameSizePos⟩
      frameFits := frameFits
      noWrap := noWrap
      disjoint := disjoint
      stateAligned := stateAligned }

/-- **The precondition is satisfiable for every layout that fits.** The side
conditions are the geometric fields of `SysVEntry` itself: the relocation fits,
the entry `%rsp` has the System V residue, the frame is below it, `state[]` is
four-byte aligned, and the six regions neither wrap nor overlap. -/
theorem realisable_of_geometry {L : Layout} {state block rspEntry : Word} {frame : Nat}
    (relocFits : L.RelocFits)
    (aligned : sysv64.EntryAligned rspEntry.toNat)
    (frameFits : sysv64.frameExtent frame ≤ rspEntry.toNat)
    (stateAligned : state.toNat % 4 = 0)
    (noWrap : ∀ r ∈ regions L state block rspEntry frame,
      r.base + r.size ≤ Silmaril.Process.addressLimit)
    (disjoint : (regions L state block rspEntry frame).Pairwise Region.Disjoint) :
    Realisable L frame :=
  ⟨state, block, rspEntry, _,
    entryState_sysVEntry relocFits aligned frameFits stateAligned noWrap disjoint⟩

/-- A layout a static linker could produce: `.text` at `0x400000`, `.rodata` one
page later, and the caller returning into a third page. -/
def concreteLayout : Layout :=
  { textBase := 0x400000, rodataBase := 0x401000, exit := 0x402000 }

/-- `state[]` at `0x500000`, `block[]` at `0x501000`, and an entry `%rsp` of
`0x7ffff008`, which has the System V residue `8` and leaves room for the frame
and the red zone. -/
theorem realisable_concrete : Realisable concreteLayout frameSize := by
  refine realisable_of_geometry (state := 0x500000) (block := 0x501000)
    (rspEntry := 0x7ffff008) ?_ ?_ ?_ ?_ ?_ ?_
  · show (concreteLayout.relocValue.setWidth 32).signExtend 64 = concreteLayout.relocValue
    decide
  · rw [Silmaril.X86.sysv64_entryAligned_iff]; decide
  · decide
  · decide
  · decide
  · decide

/-- Non-vacuity, as one statement: the `-O0` contract's precondition is
satisfiable, so `Live` and `Contract` are not vacuously true. -/
theorem contract_not_vacuous :
    Realisable concreteLayout frameSize := realisable_concrete

end Silmaril.Crypto.X86.Sha256O2

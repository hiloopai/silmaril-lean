module

public import Silmaril.X86.Sep.Xmm.Defs
public import Silmaril.Machine.SystemV.Abi.Ffi.Defs
/-!
# Placement assertions for System V call plans

A `CallPlan` computed by
`Silmaril.Machine.SystemV.Abi.plan` (`Silmaril.Machine.SystemV.Abi`) says where each argument's object bytes live at
callee entry: in register chunks (`Chunk`: GP register, part of a vector register, or x87),
or on the stack at `[rsp + 8 + stackOffset]`. This file turns that data into `XSProp`s
(`Sep/Xmm`), with **no classification of our own**: every location comes from the plan.

* `Frame`: the entry `rsp` and return address.
* `byteSlice v off n`: bytes `off … off+n-1` (little-endian) of a bit vector.
* `chunksPt bytes cs`: the registers named by the chunks `cs` are owned (each register once,
  even when several chunks share it, as SSE/SSEUP halves do), and each chunk's register bytes
  are the matching slice of the object bytes `bytes`. Excess register bits are free, as in
  the ABI model's `Ffi.ChunksAt`. Chunks that this logic cannot represent (x87, vector index ≥ 16,
  vector bytes beyond the low 128 bits, GP chunks over 8 bytes) make the assertion `False`
  (`modelled`): such plans give unsatisfiable, not wrong, specs. `chunkPt b c` is
  `chunksPt b [c]`.
* `argPt fr a bytes`: a register argument is `chunksPt bytes a.chunks`; a stack argument is
  `↑ₓ(bytesPt (fr.sp + 8 + off) bytes)`. `argsPt fr plan bss`: all arguments, in order.
* `retPt res sret rb`: the result at callee exit; `.indirect` returns `rax = sret` and owns
  the `size` result bytes at `sret`.
* `sretPt res sret`: the hidden result pointer at entry (`rdi`, an owned `size`-byte block
  aligned to the result alignment).
* `alPt plan`: for variadic plans, `al` bounds the number of vector registers used
  (`Ffi.Entry.variadicAL`).
* `ffiXState s`: the `Sse9.XState` projection of an `Ffi.State` (the integer machine, and
  the low 128 bits of vector registers 0-15); `toSepBytes`: `Ffi`'s `UInt8` bytes as
  `Sep`'s `BitVec 8` bytes.

Agreement with the ABI model (`chunksPt_iff_chunksAt`, `argPt_stack`, …) is in `Sep/Plan/Thms.lean`.

Name hygiene: no declaration here is named after the ABI convention type, and
no `open` of the compiler's category namespace.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Plan

open Silmaril.X86 (Reg XReg Word Byte)
open Silmaril.X86.Sse9 (Xmm XState)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Xmm
open Silmaril.Machine.SystemV.Abi (Chunk Argument CallPlan Location)

/-- The callee-entry frame: `rsp` at entry (pointing at the return address) and the return
address. -/
structure Frame where
  sp : Word
  ret : Word
  deriving DecidableEq

/-! ## Bytes -/

/-- Bytes `off … off + n - 1` of `v`, least significant first. -/
def byteSlice {w : Nat} (v : BitVec w) (off n : Nat) : List Byte :=
  (List.range n).map fun j => v.extractLsb' (8 * (off + j)) 8

/-- Bytes `off … off + n - 1` of an object. -/
def slice (bytes : List Byte) (off n : Nat) : List Byte := (bytes.drop off).take n

/-- `Ffi`'s bytes (`UInt8`) as `Sep`'s bytes (`BitVec 8`); the same map as `Ffi.StoredAt`. -/
def toSepBytes (bs : Silmaril.Cerberus.NativeTypes.Bytes) : List Byte :=
  bs.map fun b => BitVec.ofNat 8 b.toNat

/-- The XMM register with hardware number `i` (meaningful for `i < 16`). -/
def xregOfIdx (i : Nat) : XReg := XReg.ofBitVec (BitVec.ofNat 4 i)

/-! ## Chunks -/

/-- The chunks this logic represents: GP chunks of at most 8 bytes, and vector chunks of
XMM0-15 within the low 128 bits. x87 chunks are not modelled. -/
def modelled (c : Chunk) : Bool :=
  match c.location with
  | .gp _ => decide (c.bytes ≤ 8)
  | .vector i o => decide (i < 16) && decide (o + c.bytes ≤ 16)
  | .x87 _ => false

/-- One chunk's bytes, given the GP values `g` and XMM values `v`: the chunk is modelled, lies
inside the object, and its register bytes are the object's slice. -/
def ChunkVal (g : Reg → Word) (v : XReg → Sse9.Xmm) (bytes : List Byte) (c : Chunk) : Prop :=
  modelled c = true ∧ c.offset + c.bytes ≤ bytes.length ∧
    match c.location with
    | .gp r => byteSlice (g r) 0 c.bytes = slice bytes c.offset c.bytes
    | .vector i o => byteSlice (v (xregOfIdx i)) o c.bytes = slice bytes c.offset c.bytes
    | .x87 _ => False

/-- The GP registers named by the chunks. -/
def gpRegs (cs : List Chunk) : List Reg :=
  cs.filterMap fun c => match c.location with
    | .gp r => some r
    | _ => none

/-- The XMM registers named by the chunks. -/
def xRegs (cs : List Chunk) : List XReg :=
  cs.filterMap fun c => match c.location with
    | .vector i _ => some (xregOfIdx i)
    | _ => none

/-- The fragment owning exactly the GP registers `rs`, with values `g`. -/
def regsFrag (rs : List Reg) (g : Reg → Word) : Frag := fun l =>
  match l with
  | .reg r => if r ∈ rs then some (.word (g r)) else none
  | _ => none

/-- The XMM map owning exactly the registers `xs`, with values `v`. -/
def xmmsMap (xs : List XReg) (v : XReg → Sse9.Xmm) : XMap := fun r =>
  if r ∈ xs then some (v r) else none

/-- **Register chunks of one object.** The registers of `cs` are owned (each once), and every
chunk holds its slice of `bytes`. -/
def chunksPt (bytes : List Byte) (cs : List Chunk) : XSProp := fun h =>
  ∃ (g : Reg → Word) (v : XReg → Sse9.Xmm), h = (regsFrag (gpRegs cs) g, xmmsMap (xRegs cs) v) ∧
    ∀ c ∈ cs, ChunkVal g v bytes c

/-- One register chunk. -/
def chunkPt (bytes : List Byte) (c : Chunk) : XSProp := chunksPt bytes [c]

/-! ## Arguments, results, sret and `al` -/

/-- **One argument at callee entry**, from its plan entry: register chunks, or the object
bytes at `[rsp + 8 + stackOffset]` (after the return address). -/
def argPt (fr : Frame) (a : Argument) (bytes : List Byte) : XSProp :=
  match a.stackOffset with
  | none => chunksPt bytes a.chunks
  | some off => ↑ₓ(bytesPt (fr.sp.toNat + 8 + off) bytes)

/-- Arguments in order; `False` when the byte lists do not match the arguments one-to-one. -/
def argsPtL (fr : Frame) : List Argument → List (List Byte) → XSProp
  | [], [] => xemp
  | a :: as, b :: bs => argPt fr a b ∗ₓ argsPtL fr as bs
  | _, _ => fun _ => False

/-- **All arguments of a plan at callee entry.** -/
def argsPt (fr : Frame) (p : CallPlan) (bytes : List (List Byte)) : XSProp :=
  argsPtL fr p.arguments bytes

/-- **The result at callee exit.** `void`: no bytes; `direct`: the result chunks hold `rb`;
`indirect` (sret): `rax` echoes the hidden pointer, which owns the `size` result bytes. -/
def retPt : Silmaril.Machine.SystemV.Abi.Return → Option Word → List Byte → XSProp
  | .void, _, rb => ⌜rb = []⌝ₓ
  | .direct cs, _, rb => chunksPt rb cs
  | .indirect size _, some r, rb =>
      ↑ₓ(regPt .rax r ∗ bytesPt r.toNat rb ∗ ⌜rb.length = size⌝)
  | .indirect .., none, _ => fun _ => False

/-- **The hidden result pointer at callee entry.** For an `indirect` result, `rdi = r`, the
caller hands over `size` writable bytes at `r`, and `r` is aligned; otherwise there is no
pointer. A mismatch between the plan and `sret` is `False`. -/
def sretPt : Silmaril.Machine.SystemV.Abi.Return → Option Word → XSProp
  | .indirect size align, some r =>
      ↑ₓ(regPt .rdi r ∗ blockAny r.toNat size ∗ ⌜r.toNat % align = 0⌝)
  | .indirect .., none => fun _ => False
  | _, none => xemp
  | _, some _ => fun _ => False

/-- **`al` for variadic calls**: an upper bound (at most 8) on the vector registers used
(`Ffi.Entry.variadicAL`); nothing for fixed calls. -/
def alPt (p : CallPlan) : XSProp :=
  match p.variadicAL with
  | none => xemp
  | some k => ↑ₓ(sexists fun w : Word => regPt .rax w ∗ ⌜k ≤ w.toNat % 256 ∧ w.toNat % 256 ≤ 8⌝)

/-! ## The `Ffi.State` projection -/

/-- The `Sse9.XState` of an `Ffi.State`: the integer machine, and the low 128 bits of vector
registers 0-15. -/
def ffiXState (s : Silmaril.Machine.SystemV.Abi.Ffi.State) : XState :=
  ⟨s.machine, fun r => (s.vectors r.toBitVec.toNat).setWidth 128⟩

end Silmaril.X86.Sep.Plan

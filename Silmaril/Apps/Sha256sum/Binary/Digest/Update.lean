module

public import Silmaril.Apps.Sha256sum.Binary.Digest.Copy
public import Silmaril.Apps.Sha256sum.Binary.Digest.CompressCall

/-! # `sha_update` in `digest_file` (WIP)

The segment from `0x402f06` (after `read(fd, iobuf, 32768)` returned `r`) to the next `read`
(`0x402ef0`) or, for `r = 0`, to the padding (`0x403034`). One cut point (`0x402f38`, the
`while (n)` head), the copy loop as a summary (`Copy.summary` at `0x402f69`), and two
contracted calls of `sha256_compress` (`compressCall` at `0x402fc0`, `0x402fd5`).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest.Update

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Crypto.X86.Sha256O2 (StateHolds compressBlock stateOf)
open Silmaril.Crypto.SHA256.Kernel (InitHash)

/-- `iobuf`. -/
def iobuf : Word := 0x40a0c0#64

/-- The `struct sha` of `digest_fd`, in the frame at `sp`: `h[8]` at `sp+0x20`, `blk[64]` at
`sp+0x40`, `blen` at `sp+0x80`, `total` at `sp+0x88`. `blocks` are the compressed blocks and
`tail` the buffered bytes; `T` is the stored total. -/
structure Buf (m : Memory) (sp : Word) (H0 : InitHash) (blocks : List (List Byte))
    (tail : List Byte) (T : Nat) : Prop where
  hState : StateHolds m (sp + 0x20#64) (blocks.foldl compressBlock H0)
  hTail : m.readBytes (sp + 0x40#64).toNat tail.length = some tail
  hBlen : loadN m (sp + 0x80#64) 8 = some (BitVec.ofNat 64 tail.length)
  hTotal : loadN m (sp + 0x88#64) 8 = some (BitVec.ofNat 64 T)
  hFull : ∀ b ∈ blocks, b.length = 64
  hRoom : tail.length < 64

/-- The ghost context of one `sha_update` call. -/
structure Ctx where
  sp : Word
  chunk : List Byte
  H0 : InitHash
  blocks : List (List Byte)
  tail : List Byte
  T : Nat
  r0 : Silmaril.X86.Reg → Word

/-- What every point of the segment knows. -/
structure Frame (c : Ctx) (s : XState) : Prop where
  rsp : s.core.read .rsp = c.sp
  rbx : s.core.read .rbx = 64#64
  rbp : s.core.read .rbp = c.r0 .rbp
  r13 : s.core.read .r13 = c.r0 .r13
  chunk : s.memory.readBytes iobuf.toNat c.chunk.length = some c.chunk
  chunkLen : c.chunk.length ≤ 32768

def pre (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ s.core.read .rax = BitVec.ofNat 64 c.chunk.length ∧
    Buf s.memory c.sp c.H0 c.blocks c.tail c.T

/-- Consumed `i` bytes of the chunk: the struct holds them, and `r12` points past them. -/
def At (c : Ctx) (s : XState) (i : Nat) : Prop :=
  s.core.read .r12 = iobuf + BitVec.ofNat 64 i ∧ i ≤ c.chunk.length ∧
    s.core.read .r15 = BitVec.ofNat 64 (c.chunk.length - i) ∧
    ∃ blocks tail, blocks.flatten ++ tail = c.blocks.flatten ++ c.tail ++ c.chunk.take i ∧
      Buf s.memory c.sp c.H0 blocks tail (c.T + c.chunk.length)

/-- `0x402f38`, the `while (n)` head: `n = r15 > 0`. -/
def inv72 (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ ∃ i, i < c.chunk.length ∧ At c s i

/-- `0x402fa0`, `test %r15,%r15`. -/
def inv176 (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ ∃ i, At c s i

/-- `0x402f9a`: `k = r14` bytes taken from `iobuf + i` are already in the struct. -/
def inv170 (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ ∃ i k, 1 ≤ k ∧ i + k ≤ c.chunk.length ∧
    s.core.read .r12 = iobuf + BitVec.ofNat 64 i ∧
    s.core.read .r14 = BitVec.ofNat 64 k ∧
    s.core.read .r15 = BitVec.ofNat 64 (c.chunk.length - i) ∧
    ∃ blocks tail, blocks.flatten ++ tail = c.blocks.flatten ++ c.tail ++ c.chunk.take (i + k) ∧
      Buf s.memory c.sp c.H0 blocks tail (c.T + c.chunk.length)

/-- `0x402f81`, after the copy: the buffer holds `tail ++ chunk[i, i+k)`, `blen` still
`tail.length`. -/
def inv145 (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ ∃ (i k : Nat) (blocks : List (List Byte)) (tail : List Byte), 1 ≤ k ∧
    i + k ≤ c.chunk.length ∧ tail.length + k ≤ 64 ∧
    s.core.read .r12 = iobuf + BitVec.ofNat 64 i ∧
    s.core.read .r14 = BitVec.ofNat 64 k ∧
    s.core.read .r15 = BitVec.ofNat 64 (c.chunk.length - i) ∧
    s.core.read .rsi = c.sp + 0x40#64 ∧
    blocks.flatten ++ tail = c.blocks.flatten ++ c.tail ++ c.chunk.take i ∧
    StateHolds s.memory (c.sp + 0x20#64) (blocks.foldl compressBlock c.H0) ∧
    s.memory.readBytes (c.sp + 0x40#64).toNat (tail.length + k) =
      some (tail ++ (c.chunk.drop i).take k) ∧
    loadN s.memory (c.sp + 0x80#64) 8 = some (BitVec.ofNat 64 tail.length) ∧
    loadN s.memory (c.sp + 0x88#64) 8 = some (BitVec.ofNat 64 (c.T + c.chunk.length)) ∧
    (∀ b ∈ blocks, b.length = 64)

def postRead (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ ∃ blocks tail,
    blocks.flatten ++ tail = c.blocks.flatten ++ c.tail ++ c.chunk ∧
    Buf s.memory c.sp c.H0 blocks tail (c.T + c.chunk.length)

def postEof (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ c.chunk = [] ∧ Buf s.memory c.sp c.H0 c.blocks c.tail c.T

def r15n (s : XState) : Nat := (s.core.read .r15).toNat
def r14n (s : XState) : Nat := (s.core.read .r14).toNat

def cuts (c : Ctx) : List (Nat × Cut (σ := XState)) :=
  [(72, { inv := inv72 c, measure := fun s => 4 * r15n s + 3 }),
   (145, { inv := inv145 c, measure := fun s => 4 * r15n s + 2 }),
   (170, { inv := inv170 c, measure := fun s => 4 * (r15n s - r14n s) + 5 }),
   (176, { inv := inv176 c, measure := fun s => 4 * r15n s + 4 })]

def stops (c : Ctx) : List (Nat × (XState → Prop)) :=
  [(0, postRead c), (324, postEof c), (248, fun _ => False)]

def calls (r11 : Core → Word) : List (Nat × Nat × Call (Isa.sys r11)) :=
  [(208, 213, compressCall r11), (229, 234, compressCall r11)]

def subs (r11 : Core → Word) : List (Nat × Nat × Call (Isa.sys r11)) :=
  [(121, 145, Copy.summary r11)]

theorem Frame.congr {c : Ctx} {s t : XState} (h : Frame c s) (hm : t.memory = s.memory)
    (hsp : t.core.read .rsp = s.core.read .rsp) (hbx : t.core.read .rbx = s.core.read .rbx)
    (hbp : t.core.read .rbp = s.core.read .rbp) (h13 : t.core.read .r13 = s.core.read .r13) :
    Frame c t :=
  ⟨hsp.trans h.rsp, hbx.trans h.rbx, hbp.trans h.rbp, h13.trans h.r13, hm ▸ h.chunk, h.chunkLen⟩

theorem At.congr {c : Ctx} {s t : XState} {i : Nat} (h : At c s i) (hm : t.memory = s.memory)
    (h12 : t.core.read .r12 = s.core.read .r12) (h15 : t.core.read .r15 = s.core.read .r15) :
    At c t i := by
  obtain ⟨a, b, d, blocks, tail, e, f⟩ := h
  exact ⟨h12.trans a, b, h15.trans d, blocks, tail, e, hm ▸ f⟩

/-- Values below `2 ^ 32` survive `ofNat`/`toNat`. -/
theorem toNat_ofNat_small {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 64 n).toNat = n := by
  simp only [BitVec.toNat_ofNat]; omega

theorem vc_176 (r11 : Core → Word) (c : Ctx) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 176 → inv176 c s →
      wpN (Isa.sys r11) code listing (cuts c) (stops c) (calls r11) (subs r11) base
        (some (4 * r15n s + 4)) 4 176 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, i, hAt⟩ := hinv
  have hAt' := hAt
  obtain ⟨h12, hi, h15, blocks, tail, hacc, hB⟩ := hAt
  seg_vc [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, h15]
  have hlen := hF.chunkLen
  have hn : (BitVec.ofNat 64 (c.chunk.length - i)).toNat = c.chunk.length - i :=
    toNat_ofNat_small (by omega)
  simp only [BitVec.and_self] at *
  refine ⟨fun hne => ⟨⟨?_, i, ?_, ?_⟩, ?_⟩, fun heq => ⟨?_, blocks, tail, ?_, ?_⟩⟩
  · exact hF.congr rfl rfl rfl rfl rfl
  · simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hne
    by_contra hc
    exact hne (by rw [show c.chunk.length - i = 0 by omega])
  · exact hAt'.congr rfl rfl rfl
  · show 4 * (s.core.read .r15).toNat + 3 < 4 * r15n s + 4
    simp only [r15n]; omega
  · exact hF.congr rfl rfl rfl rfl rfl
  · simp only [Bool.not_eq_false', beq_iff_eq] at heq
    have : c.chunk.length - i = 0 := by
      have := congrArg BitVec.toNat heq; rw [hn] at this; simpa using this
    rw [hacc, List.take_of_length_le (by omega)]
  · exact hB

end Silmaril.Apps.Sha256sum.Binary.Digest.Update

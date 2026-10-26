module

public import Silmaril.Apps.Sha256sum.Binary.Digest.Copy
public import Silmaril.Apps.Sha256sum.Binary.Digest.Facts
public import Silmaril.X86.SegVC.Mono

/-! # `sha_update` in `digest_file`

The segment from `0x402f06` (after `read(fd, iobuf, 32768)` returned `r`) to the next `read`
(`0x402ef0`) or, for `r = 0`, to the padding (`0x403034`). One cut point (`0x402f38`, the
`while (n)` head), the copy loop as a summary (`Copy.summary` at `0x402f69`), and two
contracted calls of `sha256_compress` (`compressCall` at `0x402fc0`, `0x402fd5`).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest.Update

-- `omega` over spans with large offsets needs a deeper recursion limit.
set_option maxRecDepth 100000

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
  /-- The memory at the segment's entry (what `Frame.keep` is relative to). -/
  m0 : Memory

/-- The stack span the segment writes: the callee frames below `sp` and the part of
`digest_file`'s frame above its first four slots. `[sp, sp + 0x20)` (the operand pointer, the
descriptor at `sp + 8`, the digest pointer at `sp + 0x10`) and everything from `sp + 0x98` up
(saved registers, return address) are never written. -/
def stackSpan (sp : Word) (a : Nat) : Prop :=
  (sp.toNat - 400 ≤ a ∧ a < sp.toNat) ∨ (sp.toNat + 0x20 ≤ a ∧ a < sp.toNat + 152)

/-- What every point of the segment knows. -/
structure Frame (c : Ctx) (s : XState) : Prop where
  rsp : s.core.read .rsp = c.sp
  rbx : s.core.read .rbx = 64#64
  rbp : s.core.read .rbp = c.r0 .rbp
  r13 : s.core.read .r13 = c.r0 .r13
  chunk : s.memory.readBytes iobuf.toNat c.chunk.length = some c.chunk
  chunkLen : c.chunk.length ≤ 32768
  spAlign : c.sp.toNat % 16 = 0
  spLow : 0x420000 ≤ c.sp.toNat
  spHigh : c.sp.toNat + 0x1000 < 2 ^ 64
  stackW : s.memory.Permitted .write (c.sp.toNat - 400) 552
  stackR : s.memory.Permitted .read (c.sp.toNat - 400) 552
  code : s.memory.fetchBytes Binary.textBase.toNat Silmaril.Crypto.X86.Sha256O2.size =
    some (Silmaril.Crypto.X86.Sha256O2.image Binary.textBase Binary.rodataBase)
  kTable : s.memory.readBytes Binary.rodataBase.toNat Silmaril.Crypto.X86.Sha256O2.kSize =
    some Silmaril.Crypto.X86.Sha256O2.kBytes
  /-- Since the entry, only the stack span was written. -/
  keep : Memory.WritesWithin c.m0 s.memory (stackSpan c.sp)

def pre (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ s.core.read .rax = BitVec.ofNat 64 c.chunk.length ∧
    Buf s.memory c.sp c.H0 c.blocks c.tail c.T

/-- Consumed `i` bytes of the chunk: the struct holds them, and `r12` points past them. -/
def At (c : Ctx) (s : XState) (i : Nat) : Prop :=
  0 < c.chunk.length ∧ s.core.read .r12 = iobuf + BitVec.ofNat 64 i ∧ i ≤ c.chunk.length ∧
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
  Frame c s ∧ 0 < c.chunk.length ∧ ∃ blocks tail,
    blocks.flatten ++ tail = c.blocks.flatten ++ c.tail ++ c.chunk ∧
    Buf s.memory c.sp c.H0 blocks tail (c.T + c.chunk.length)

def postEof (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ c.chunk = [] ∧ Buf s.memory c.sp c.H0 c.blocks c.tail c.T ∧
    s.core.read .rdx = BitVec.ofNat 64 c.T

def r15n (s : XState) : Nat := (s.core.read .r15).toNat
def r14n (s : XState) : Nat := (s.core.read .r14).toNat

/-- `0x402f4b`, the copy setup (`mov %rbx,%r8`): `blen = rdx` bytes are buffered and the
chunk is not exhausted. -/
def inv91 (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ ∃ i blocks tail, i < c.chunk.length ∧
    s.core.read .r12 = iobuf + BitVec.ofNat 64 i ∧
    s.core.read .r15 = BitVec.ofNat 64 (c.chunk.length - i) ∧
    s.core.read .rdx = BitVec.ofNat 64 tail.length ∧
    blocks.flatten ++ tail = c.blocks.flatten ++ c.tail ++ c.chunk.take i ∧
    Buf s.memory c.sp c.H0 blocks tail (c.T + c.chunk.length)

/-- The cut points and their measures. Every path between two of them shrinks
`8 * r15 + offset` (the copy and the compress steps consume at least one byte). -/
def cuts (c : Ctx) : List (Nat × Cut (σ := XState)) :=
  [(72, { inv := inv72 c, measure := fun s => 8 * r15n s + 6 }),
   (91, { inv := inv91 c, measure := fun s => 8 * r15n s + 5 }),
   (145, { inv := inv145 c, measure := fun s => 8 * r15n s + 4 }),
   (170, { inv := inv170 c, measure := fun s => 8 * (r15n s - r14n s) + 9 }),
   (176, { inv := inv176 c, measure := fun s => 8 * r15n s + 7 })]

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
  ⟨hsp.trans h.rsp, hbx.trans h.rbx, hbp.trans h.rbp, h13.trans h.r13, hm ▸ h.chunk, h.chunkLen,
    h.spAlign, h.spLow, h.spHigh, hm ▸ h.stackW, hm ▸ h.stackR, hm ▸ h.code, hm ▸ h.kTable,
    hm ▸ h.keep⟩

/-- `Frame` survives writes to the stack span. -/
theorem Frame.transfer {c : Ctx} {s t : XState} (h : Frame c s)
    (hw : Memory.WritesWithin s.memory t.memory (stackSpan c.sp))
    (hsp : t.core.read .rsp = s.core.read .rsp) (hbx : t.core.read .rbx = s.core.read .rbx)
    (hbp : t.core.read .rbp = s.core.read .rbp) (h13 : t.core.read .r13 = s.core.read .r13) :
    Frame c t := by
  have lo := h.spLow
  refine ⟨hsp.trans h.rsp, hbx.trans h.rbx, hbp.trans h.rbp, h13.trans h.r13, ?_, h.chunkLen,
    h.spAlign, h.spLow, h.spHigh, (hw.permitted_iff _ _ _).mpr h.stackW,
    (hw.permitted_iff _ _ _).mpr h.stackR, ?_, ?_, h.keep.trans hw⟩
  · rw [hw.readBytes]; · exact h.chunk
    intro off hoff hin; simp only [stackSpan, iobuf] at hin; have := h.chunkLen
    simp only [BitVec.toNat_ofNat] at hin; omega
  · rw [hw.fetchBytes]; · exact h.code
    intro off hoff hin; simp only [stackSpan, Binary.textBase, Silmaril.Crypto.X86.Sha256O2.size] at hin hoff
    simp only [BitVec.toNat_ofNat] at hin; omega
  · rw [hw.readBytes]; · exact h.kTable
    intro off hoff hin; simp only [stackSpan, Binary.rodataBase, Silmaril.Crypto.X86.Sha256O2.kSize] at hin hoff
    simp only [BitVec.toNat_ofNat] at hin; omega

/-- The memory half of `Frame`. -/
structure FrameMem (c : Ctx) (m : Memory) : Prop where
  chunk : m.readBytes iobuf.toNat c.chunk.length = some c.chunk
  stackW : m.Permitted .write (c.sp.toNat - 400) 552
  stackR : m.Permitted .read (c.sp.toNat - 400) 552
  code : m.fetchBytes Binary.textBase.toNat Silmaril.Crypto.X86.Sha256O2.size =
    some (Silmaril.Crypto.X86.Sha256O2.image Binary.textBase Binary.rodataBase)
  kTable : m.readBytes Binary.rodataBase.toNat Silmaril.Crypto.X86.Sha256O2.kSize =
    some Silmaril.Crypto.X86.Sha256O2.kBytes
  keep : Memory.WritesWithin c.m0 m (stackSpan c.sp)

theorem Frame.mem {c : Ctx} {s : XState} (h : Frame c s) : FrameMem c s.memory :=
  ⟨h.chunk, h.stackW, h.stackR, h.code, h.kTable, h.keep⟩

/-- `FrameMem` survives writes to the stack span. -/
theorem FrameMem.transfer {c : Ctx} {m m' : Memory} (h : FrameMem c m) (hlen : c.chunk.length ≤ 32768)
    (hw : Memory.WritesWithin m m' (stackSpan c.sp)) (lo : 0x420000 ≤ c.sp.toNat) :
    FrameMem c m' := by
  refine ⟨?_, (hw.permitted_iff _ _ _).mpr h.stackW, (hw.permitted_iff _ _ _).mpr h.stackR, ?_, ?_,
    h.keep.trans hw⟩
  · rw [hw.readBytes]; · exact h.chunk
    intro off hoff hin; simp only [stackSpan, iobuf] at hin
    simp only [BitVec.toNat_ofNat] at hin; omega
  · rw [hw.fetchBytes]; · exact h.code
    intro off hoff hin; simp only [stackSpan, Binary.textBase, Silmaril.Crypto.X86.Sha256O2.size] at hin hoff
    simp only [BitVec.toNat_ofNat] at hin; omega
  · rw [hw.readBytes]; · exact h.kTable
    intro off hoff hin; simp only [stackSpan, Binary.rodataBase, Silmaril.Crypto.X86.Sha256O2.kSize] at hin hoff
    simp only [BitVec.toNat_ofNat] at hin; omega

theorem Frame.of_mem {c : Ctx} {s t : XState} (h : Frame c s) (hm : FrameMem c t.memory)
    (hsp : t.core.read .rsp = s.core.read .rsp) (hbx : t.core.read .rbx = s.core.read .rbx)
    (hbp : t.core.read .rbp = s.core.read .rbp) (h13 : t.core.read .r13 = s.core.read .r13) :
    Frame c t :=
  ⟨hsp.trans h.rsp, hbx.trans h.rbx, hbp.trans h.rbp, h13.trans h.r13, hm.chunk, h.chunkLen,
    h.spAlign, h.spLow, h.spHigh, hm.stackW, hm.stackR, hm.code, hm.kTable, hm.keep⟩

/-- The `sha256_compress` footprint lies in the stack span. -/
theorem calleeSpan_sub {sp : Word} {a : Nat} (h : calleeSpan sp a) : stackSpan sp a := by
  simp only [calleeSpan, stackSpan] at *; omega

/-- An empty read inside the address space succeeds. -/
theorem readBytes_nil {m : Memory} {a : Nat} (h : a < 2 ^ 64) : m.readBytes a 0 = some [] := by
  simp [Memory.readBytes, Memory.readWith, Memory.checkSpan, Memory.readBacking,
    Silmaril.Process.addressLimit]
  omega

theorem At.congr {c : Ctx} {s t : XState} {i : Nat} (h : At c s i) (hm : t.memory = s.memory)
    (h12 : t.core.read .r12 = s.core.read .r12) (h15 : t.core.read .r15 = s.core.read .r15) :
    At c t i := by
  obtain ⟨p, a, b, d, blocks, tail, e, f⟩ := h
  exact ⟨p, h12.trans a, b, h15.trans d, blocks, tail, e, hm ▸ f⟩

/-- Values below `2 ^ 32` survive `ofNat`/`toNat`. -/
theorem toNat_ofNat_small {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 64 n).toNat = n := by
  simp only [BitVec.toNat_ofNat]; omega

theorem vc_176 (r11 : Core → Word) (c : Ctx) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 176 → inv176 c s →
      wpN (Isa.sys r11) code listing (cuts c) (stops c) (calls r11) (subs r11) base
        (some (8 * r15n s + 7)) 4 176 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, i, hAt⟩ := hinv
  have hAt' := hAt
  obtain ⟨hpos0, h12, hi, h15, blocks, tail, hacc, hB⟩ := hAt
  seg_vc [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, h15]
  have hlen := hF.chunkLen
  have hn : (BitVec.ofNat 64 (c.chunk.length - i)).toNat = c.chunk.length - i :=
    toNat_ofNat_small (by omega)
  simp only [BitVec.and_self] at *
  refine ⟨fun hne => ⟨⟨?_, i, ?_, ?_⟩, ?_⟩, fun heq => ⟨?_, hpos0, blocks, tail, ?_, ?_⟩⟩
  · exact hF.congr rfl rfl rfl rfl rfl
  · simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hne
    by_contra hc
    exact hne (by rw [show c.chunk.length - i = 0 by omega])
  · exact hAt'.congr rfl rfl rfl
  · show 8 * (s.core.read .r15).toNat + 6 < 8 * r15n s + 7
    simp only [r15n]; omega
  · exact hF.congr rfl rfl rfl rfl rfl
  · simp only [Bool.not_eq_false', beq_iff_eq] at heq
    have : c.chunk.length - i = 0 := by
      have := congrArg BitVec.toNat heq; rw [hn] at this; simpa using this
    rw [hacc, List.take_of_length_le (by omega)]
  · exact hB

theorem vc_170 (r11 : Core → Word) (c : Ctx) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 170 → inv170 c s →
      wpN (Isa.sys r11) code listing (cuts c) (stops c) (calls r11) (subs r11) base
        (some (8 * (r15n s - r14n s) + 9)) 4 170 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, i, k, hk, hik, h12, h14, h15, blocks, tail, hacc, hB⟩ := hinv
  seg_vc [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, h15, h12, h14]
  have hlen := hF.chunkLen
  refine ⟨⟨hF.congr rfl (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read []),
    i + k, by omega, ?_, by omega, ?_, blocks, tail, hacc, hB⟩, ?_⟩
  · seg_read []
    rw [BitVec.ofNat_add]
  · seg_read []
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · simp only [r15n, r14n, h15, h14, BitVec.toNat_ofNat]
    seg_read []
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

set_option maxRecDepth 100000 in
theorem code_length : code.length = 248 := by decide

/-- The region's code lies below `.bss` and the stack. -/
theorem base_toNat : base.toNat = 0x402ef0 := rfl

/-- Everything `sha_update` writes between two cut points, seen from the struct: below `sp`,
`state[]`, or `blen`. -/
def updSpan (sp : Word) (a : Nat) : Prop :=
  a < sp.toNat ∨ (sp.toNat + 0x20 ≤ a ∧ a < sp.toNat + 0x40) ∨
    (sp.toNat + 0x80 ≤ a ∧ a < sp.toNat + 0x88)

theorem take_add_drop_take (l : List Byte) (i k : Nat) :
    l.take (i + k) = l.take i ++ (l.drop i).take k := List.take_add ..

set_option maxRecDepth 100000 in
theorem vc_145 (r11 : Core → Word) (c : Ctx) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 145 → inv145 c s →
      wpN (Isa.sys r11) code listing (cuts c) (stops c) (calls r11) (subs r11) base
        (some (8 * r15n s + 4)) 12 145 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, i, k, blocks, tail, hk, hik, hroom, h12, h14, h15, hsi, hacc, hst, hbuf, hblen, htot,
    hfull⟩ := hinv
  have hblen' := hblen
  rw [← hF.rsp] at hblen'
  seg_vc [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, h15, h12,
    h14, hblen', hsi]
  have hlen := hF.chunkLen
  have spH := hF.spHigh
  have spL := hF.spLow
  have hsp := hF.rsp
  have e80 : (c.sp + 128#64).toNat = c.sp.toNat + 128 := toNat_sp_add spH (by decide)
  have e40 : (c.sp + 64#64).toNat = c.sp.toNat + 64 := toNat_sp_add spH (by decide)
  have e20 : (c.sp + 32#64).toNat = c.sp.toNat + 32 := toNat_sp_add spH (by decide)
  have e88 : (c.sp + 136#64).toNat = c.sp.toNat + 136 := toNat_sp_add spH (by decide)
  have e8 : (c.sp - 8#64).toNat = c.sp.toNat - 8 := toNat_sp_sub spL (by decide)
  have hv : (BitVec.ofNat 64 tail.length + BitVec.ofNat 64 k).toNat = tail.length + k := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have htk : ((c.chunk.drop i).take k).length = k := by
    simp only [List.length_take, List.length_drop]; omega
  have hn15 : (BitVec.ofNat 64 (c.chunk.length - i)).toNat = c.chunk.length - i :=
    toNat_ofNat_small (by omega)
  have hn14 : (BitVec.ofNat 64 k).toNat = k := toNat_ofNat_small (by omega)
  rw [hsp]
  refine ⟨by rw [e80]; exact Memory.Permitted.sub hF.stackW (by omega) (by omega) (by omega),
    fun after hstore => ?_⟩
  have hS := Stored.of_storeN hstore
  rw [e80] at hS
  have hWu : Memory.WritesWithin s.memory after (updSpan c.sp) :=
    hS.writesWithin (fun off hoff => by
      simp only [length_leBytes] at hoff; simp only [updSpan]; omega)
  have hW : Memory.WritesWithin s.memory after (stackSpan c.sp) :=
    hS.writesWithin (fun off hoff => by
      simp only [length_leBytes] at hoff; simp only [stackSpan]; omega)
  have hL : Loaded after base code :=
    Loaded.of_stored hl hS (by simp only [length_leBytes, base_toNat, code_length]; omega)
  have hFM := hF.mem.transfer hlen hW spL
  have hblen1 : loadN after (c.sp + 128#64) 8 = some (BitVec.ofNat 64 (tail.length + k)) := by
    have hr : s.memory.Permitted .read (c.sp + 128#64).toNat 8 := by
      rw [e80]; exact Memory.Permitted.sub hF.stackR (by omega) (by omega) (by omega)
    rw [loadN_storeN hstore hr, hv]
    congr 2; omega
  have htot1 : loadN after (c.sp + 136#64) 8 = some (BitVec.ofNat 64 (c.T + c.chunk.length)) := by
    rw [loadN_storeN_disjoint hstore (by rw [e88, e80]; omega)]; exact htot
  have hbuf1 : after.readBytes (c.sp + 64#64).toNat (tail.length + k) =
      some (tail ++ (c.chunk.drop i).take k) := by
    rw [hWu.readBytes]; · exact hbuf
    intro o ho hin; simp only [updSpan, e40] at hin; omega
  have hst1 : StateHolds after (c.sp + 32#64) (blocks.foldl compressBlock c.H0) :=
    Digest.StateHolds.transfer hst (hS.writesWithin (inside := fun a => c.sp.toNat + 128 ≤ a ∧ a < c.sp.toNat + 136)
      (fun off hoff => by simp only [length_leBytes] at hoff; omega))
      (fun o ho hin => by rw [e20] at hin; omega)
  refine ⟨hL, hL, fun hfb => ?_, fun hnf => ?_⟩
  · -- the block is full: compress it, then `blen = 0`
    have h64 : tail.length + k = 64 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hfb); rw [hv] at this; simpa using this
    have hpw : after.Permitted .write (c.sp - 8#64).toNat 8 := by
      rw [e8]; exact Memory.Permitted.sub hFM.stackW (by omega) (by omega) (by omega)
    refine ⟨hL, hL, hpw, fun after1 hpush => ?_⟩
    rw [e8] at hpush
    have hS1 := Stored.of_writeBytes hpush
    have hW1u : Memory.WritesWithin after after1 (updSpan c.sp) :=
      hS1.writesWithin (fun off hoff => by
        simp only [X86.length_encodeWords_singleton] at hoff; simp only [updSpan]; omega)
    have hW1 : Memory.WritesWithin after after1 (stackSpan c.sp) :=
      hS1.writesWithin (fun off hoff => by
        simp only [X86.length_encodeWords_singleton] at hoff; simp only [stackSpan]; omega)
    have hL1 : Loaded after1 base code :=
      Loaded.of_stored hL hS1 (by
        simp only [base_toNat, code_length, X86.length_encodeWords_singleton]; omega)
    have hFM1 := hFM.transfer hlen hW1 spL
    have hret : after1.readBytes (c.sp - 8#64).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [base + 234#64]) := by
      rw [e8]
      have := hS1.readWith_self (access := .read) (by
        simp only [X86.length_encodeWords_singleton]
        exact Memory.Permitted.sub hFM.stackR (by omega) (by omega) (by omega))
      simp only [X86.length_encodeWords_singleton] at this
      exact this
    have hst2 : StateHolds after1 (c.sp + 32#64) (blocks.foldl compressBlock c.H0) :=
      Digest.StateHolds.transfer hst1 (hS1.writesWithin (inside := fun a => c.sp.toNat - 8 ≤ a ∧ a < c.sp.toNat)
        (fun off hoff => by simp only [X86.length_encodeWords_singleton] at hoff; omega))
        (fun o ho hin => by rw [e20] at hin; omega)
    have hblk : after1.readBytes (c.sp + 64#64).toNat 64 = some (tail ++ (c.chunk.drop i).take k) := by
      rw [hW1u.readBytes]
      · have hb64 := hbuf1; rw [h64] at hb64; exact hb64
      intro o ho hin; simp only [updSpan, e40] at hin; omega
    refine ⟨hL1, compress_vc r11 (sp := c.sp) (blk := c.sp + 64#64) (ret := base + 234#64)
      (by rfl) (by seg_read []) (by seg_read [hsi]) (by seg_read []) hret hFM1.code hFM1.kTable hst2
      hblk hFM1.stackW hFM1.stackR hF.spAlign spL spH (.inr e40) ?_⟩
    intro fin hst3 hsp3 hsv3 hWc hrip3
    have hsv : ∀ r ∈ X86.sysv64.calleeSaved, fin.core.read r = s.core.read r := by
      intro r hr
      rw [hsv3 r hr]
      simp only [X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> seg_read []
    have hL3 : Loaded fin.memory base code := by
      unfold Loaded; rw [hWc.fetchBytes]; · exact hL1
      intro o ho hin; simp only [calleeSpan, base_toNat, code_length] at hin ho; omega
    have hWcs : Memory.WritesWithin after1 fin.memory (stackSpan c.sp) :=
      hWc.mono fun a ha => calleeSpan_sub ha
    have hWcu : Memory.WritesWithin after1 fin.memory (updSpan c.sp) :=
      hWc.mono fun a ha => by simp only [calleeSpan, updSpan] at ha ⊢; omega
    have hFM3 := hFM1.transfer hlen hWcs spL
    simp only [withExtState]
    have hpw2 : fin.memory.Permitted .write (fin.core.read .rsp + 128#64).toNat 8 := by
      rw [hsp3, e80]; exact Memory.Permitted.sub hFM3.stackW (by omega) (by omega) (by omega)
    refine ⟨hrip3, hL3, hpw2, fun after2 hstore2 => ?_⟩
    rw [hsp3] at hstore2
    have hS2 := Stored.of_storeN hstore2
    rw [e80] at hS2
    have hW2u : Memory.WritesWithin fin.memory after2 (updSpan c.sp) :=
      hS2.writesWithin (fun off hoff => by
        simp only [length_leBytes] at hoff; simp only [updSpan]; omega)
    have hW2 : Memory.WritesWithin fin.memory after2 (stackSpan c.sp) :=
      hS2.writesWithin (fun off hoff => by
        simp only [length_leBytes] at hoff; simp only [stackSpan]; omega)
    have hL2 : Loaded after2 base code :=
      Loaded.of_stored hL3 hS2 (by simp only [length_leBytes, base_toNat, code_length]; omega)
    have hFM2 := hFM3.transfer hlen hW2 spL
    have hWall : Memory.WritesWithin s.memory after2 (updSpan c.sp) :=
      ((hWu.trans hW1u).trans hWcu).trans hW2u
    refine ⟨hL2, hL2, ⟨hF.of_mem hFM2 (by seg_read [hsp3, hsp]) (by seg_read [hsv .rbx (by decide)])
      (by seg_read [hsv .rbp (by decide)]) (by seg_read [hsv .r13 (by decide)]),
      i, k, hk, hik, by seg_read [hsv .r12 (by decide), h12], by seg_read [hsv .r14 (by decide), h14],
      by seg_read [hsv .r15 (by decide), h15], blocks ++ [tail ++ (c.chunk.drop i).take k], [], ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [← List.append_assoc, hacc, take_add_drop_take]; simp
    · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact Digest.StateHolds.transfer hst3
        (hS2.writesWithin (inside := fun a => c.sp.toNat + 128 ≤ a ∧ a < c.sp.toNat + 136)
          (fun off hoff => by simp only [length_leBytes] at hoff; omega))
        (fun o ho hin => by rw [e20] at hin; omega)
    · exact readBytes_nil (by simp only [e40]; omega)
    · have hr : fin.memory.Permitted .read (c.sp + 128#64).toNat 8 := by
        rw [e80]; exact Memory.Permitted.sub hFM3.stackR (by omega) (by omega) (by omega)
      rw [loadN_storeN hstore2 hr]; rfl
    · rw [loadN_transfer hWall (fun o ho hin => by simp only [updSpan, e88] at hin; omega)]
      exact htot
    · intro b hb
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hfull b hb
      · simp only [List.length_append, htk]; omega
    · simp
    · simp only [r15n, r14n]
      seg_read [hsv .r15 (by decide), hsv .r14 (by decide), h15, h14, hn15, hn14]
      omega
  · -- the block is not full: `blen += k`
    have hlt : tail.length + k < 64 := by
      have hne : BitVec.ofNat 64 tail.length + BitVec.ofNat 64 k ≠ 64#64 := by
        simpa using hnf
      have : tail.length + k ≠ 64 := fun e => hne (by
        apply BitVec.eq_of_toNat_eq; rw [hv, e]; rfl)
      omega
    refine ⟨hL, ⟨hF.of_mem hFM (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read []),
      i, k, hk, hik, by seg_read [h12], by seg_read [h14], by seg_read [h15], blocks,
      tail ++ (c.chunk.drop i).take k, ?_, hst1, ?_, ?_, htot1, hfull, ?_⟩, ?_⟩
    · rw [← List.append_assoc, hacc, take_add_drop_take]; simp
    · simp only [List.length_append, htk]; exact hbuf1
    · simp only [List.length_append, htk]; exact hblen1
    · simp only [List.length_append, htk]; exact hlt
    · simp only [r15n, r14n]
      seg_read [h15, h14, hn15, hn14]
      omega

/-- One byte of a successful span read, through a one-byte load. -/
theorem loadN_one_of_readBytes {m : Memory} {a n : Nat} {bs : List Byte}
    (h : m.readBytes a n = some bs) {w : Word} {j : Nat} (hj : j < n) (hw : w.toNat = a + j) :
    loadN m w 1 = some (BitVec.ofNat 64 (bs.getD j 0).toNat) := by
  have hlen : bs.length = n := Memory.readWith_length h
  unfold loadN
  rw [hw, Memory.readBytes_sub_range h hj (by omega)]
  have : (bs.drop j).take 1 = [bs.getD j 0] := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    rw [List.take_one, List.head?_drop, List.getElem?_eq_getElem (by omega)]
    rfl
  rw [this]
  simp [leValue]

/-- **The copy loop as a summary, from the caller's facts**: its precondition at `0x402f69`
from `k = r14`, `src = r12`, `dst = rdi` and the buffer facts. -/
theorem copy_pre_of (r11 : Core → Word) {x : XState} {k : Nat} {src dst : Word}
    (hrip : x.core.rip = base + 121#64) (hl : Loaded x.memory base code)
    (h14 : x.core.read .r14 = BitVec.ofNat 64 k) (h12 : x.core.read .r12 = src)
    (hdi : x.core.read .rdi = dst) (hk1 : 1 ≤ k) (hk : k < 2 ^ 32)
    (hsrc : ∀ j < k, ∃ b : Byte, loadN x.memory (src + BitVec.ofNat 64 j) 1 =
      some (BitVec.ofNat 64 b.toNat))
    (dstW : x.memory.Permitted .write dst.toNat k) (dstR : x.memory.Permitted .read dst.toNat k)
    (dstFit : dst.toNat + k < 2 ^ 64) (srcFit : src.toNat + k < 2 ^ 64)
    (apart : dst.toNat + k ≤ src.toNat ∨ src.toNat + k ≤ dst.toNat)
    (codeApart : dst.toNat + k ≤ base.toNat ∨ base.toNat + code.length ≤ dst.toNat) :
    (Copy.summary r11).pre x := by
  refine ⟨hrip, hl, Copy.Ctx.mk k src dst
    (fun j => (loadN x.memory (src + BitVec.ofNat 64 j) 1).getD 0) x.core.read x.memory, ⟨fun r _ _ => rfl, Memory.WritesWithin.refl _ _, h14, h12,
    hdi, hk1, hk, fun j hj => ?_, dstW, dstR, dstFit, srcFit, apart, codeApart, fun j hj => ?_⟩, rfl⟩
  · obtain ⟨b, hb⟩ := hsrc j hj
    simp only [hb, Option.getD_some]
  · obtain ⟨b, hb⟩ := hsrc j hj
    simp only [hb, Option.getD_some, BitVec.toNat_ofNat]
    have := b.isLt; omega

/-- What the copy summary gives back: the registers but `rcx`, `rdx`, writes only in the
destination, and the `k` source bytes at the destination. -/
theorem copy_post_facts (r11 : Core → Word) {x t : XState} {k : Nat} {src dst : Word}
    (h14 : x.core.read .r14 = BitVec.ofNat 64 k) (h12 : x.core.read .r12 = src)
    (hdi : x.core.read .rdi = dst) (hk : k < 2 ^ 32) (hpost : (Copy.summary r11).post x t) :
    t.core.rip = base + BitVec.ofNat 64 145 ∧ Loaded t.memory base code ∧
      (∀ r, r ≠ .rcx → r ≠ .rdx → t.core.read r = x.core.read r) ∧
      Memory.WritesWithin x.memory t.memory (fun a => dst.toNat ≤ a ∧ a < dst.toNat + k) ∧
      ∀ j < k, loadN t.memory (dst + BitVec.ofNat 64 j) 1 =
        loadN x.memory (src + BitVec.ofNat 64 j) 1 := by
  obtain ⟨hrip, hl, cc, ⟨hF, hm⟩, hF', hloads⟩ := hpost
  have hkk : cc.k = k := by
    have e := (hF.regs .r14 (by decide) (by decide)).trans hF.k
    rw [h14] at e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    have := hF.kLt
    omega
  have hsrc : cc.src = src := hF.src.symm.trans ((hF.regs .r12 (by decide) (by decide)).symm.trans h12)
  have hdst : cc.dst = dst := hF.dst.symm.trans ((hF.regs .rdi (by decide) (by decide)).symm.trans hdi)
  subst hkk hsrc hdst
  refine ⟨hrip, hl, fun r h1 h2 => (hF'.regs r h1 h2).trans (hF.regs r h1 h2).symm, ?_, ?_⟩
  · rw [hm]; exact hF'.writes
  · intro j hj
    rw [hloads j hj, hm, hF.srcRead j hj]

/-- What a `sha256_compress` call writes, seen from the struct: below `sp`, or `state[]`. -/
def callSpan (sp : Word) (a : Nat) : Prop :=
  a < sp.toNat ∨ (sp.toNat + 0x20 ≤ a ∧ a < sp.toNat + 0x40)

theorem toNat_iobuf_add {i : Nat} (h : i ≤ 32768) : (iobuf + BitVec.ofNat 64 i).toNat = iobuf.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [iobuf, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 100000 in
theorem vc_72 (r11 : Core → Word) (c : Ctx) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 72 → inv72 c s →
      wpN (Isa.sys r11) code listing (cuts c) (stops c) (calls r11) (subs r11) base
        (some (8 * r15n s + 6)) 16 72 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, i, hiL, -, h12, hi, h15, blocks, tail, hacc, hB⟩ := hinv
  have hbl := hB.hBlen
  rw [← hF.rsp] at hbl
  seg_vc [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, h15, h12,
    hbl, hF.rbx]
  have hlen := hF.chunkLen
  have spH := hF.spHigh
  have spL := hF.spLow
  have hsp := hF.rsp
  have htl := hB.hRoom
  have hn15 : (BitVec.ofNat 64 (c.chunk.length - i)).toNat = c.chunk.length - i :=
    toNat_ofNat_small (by omega)
  have hntl : (BitVec.ofNat 64 tail.length).toNat = tail.length := toNat_ofNat_small (by omega)
  have e20 : (c.sp + 32#64).toNat = c.sp.toNat + 32 := toNat_sp_add spH (by decide)
  have e80 : (c.sp + 128#64).toNat = c.sp.toNat + 128 := toNat_sp_add spH (by decide)
  have e88 : (c.sp + 136#64).toNat = c.sp.toNat + 136 := toNat_sp_add spH (by decide)
  have e8 : (c.sp - 8#64).toNat = c.sp.toNat - 8 := toNat_sp_sub spL (by decide)
  have hinv91 : ∀ t : XState, t.memory = s.memory → t.core.read .rsp = s.core.read .rsp →
      t.core.read .rbx = s.core.read .rbx → t.core.read .rbp = s.core.read .rbp →
      t.core.read .r13 = s.core.read .r13 → t.core.read .r12 = s.core.read .r12 →
      t.core.read .r15 = s.core.read .r15 → t.core.read .rdx = BitVec.ofNat 64 tail.length →
      inv91 c t ∧ 8 * r15n t + 5 < 8 * r15n s + 6 := by
    intro t hm hsp' hbx hbp h13 h12' h15' hdx
    refine ⟨⟨hF.congr hm hsp' hbx hbp h13, i, blocks, tail, hiL, h12'.trans h12, h15'.trans h15,
      hdx, hacc, hm ▸ hB⟩, ?_⟩
    simp only [r15n, h15']; omega
  rw [hsp]
  refine ⟨fun _ => hinv91 _ rfl (by seg_read []) (by seg_read []) (by seg_read [])
    (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read []), fun hgt => ⟨fun hz => ?_,
    fun _ => hinv91 _ rfl (by seg_read []) (by seg_read []) (by seg_read [])
    (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read [])⟩⟩
  -- a whole block straight from `iobuf`: `sha256_compress(s->h, p)`
  have htl0 : tail.length = 0 := by
    simp only [BitVec.and_self, beq_iff_eq] at hz
    have := congrArg BitVec.toNat hz; rw [hntl] at this; simpa using this
  have hnil : tail = [] := List.eq_nil_of_length_eq_zero htl0
  subst hnil
  have hi64 : i + 64 ≤ c.chunk.length := by
    have : ¬ (c.chunk.length - i ≤ 63) := fun h => by
      have : (BitVec.ofNat 64 (c.chunk.length - i)).ule 63#64 = true := by
        simp only [BitVec.ule, hn15]; simpa using h
      rw [this] at hgt; cases hgt
    omega
  have hpw : s.memory.Permitted .write (c.sp - 8#64).toNat 8 := by
    rw [e8]; exact Memory.Permitted.sub hF.stackW (by omega) (by omega) (by omega)
  refine ⟨hpw, fun after hpush => ?_⟩
  rw [e8] at hpush
  have hS1 := Stored.of_writeBytes hpush
  have hW1c : Memory.WritesWithin s.memory after (callSpan c.sp) :=
    hS1.writesWithin (fun off hoff => by
      simp only [X86.length_encodeWords_singleton] at hoff; simp only [callSpan]; omega)
  have hW1 : Memory.WritesWithin s.memory after (stackSpan c.sp) :=
    hS1.writesWithin (fun off hoff => by
      simp only [X86.length_encodeWords_singleton] at hoff; simp only [stackSpan]; omega)
  have hL1 : Loaded after base code :=
    Loaded.of_stored hl hS1 (by
      simp only [base_toNat, code_length, X86.length_encodeWords_singleton]; omega)
  have hFM1 := hF.mem.transfer hlen hW1 spL
  have hret : after.readBytes (c.sp - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [base + 213#64]) := by
    rw [e8]
    have := hS1.readWith_self (access := .read) (by
      simp only [X86.length_encodeWords_singleton]
      exact Memory.Permitted.sub hF.stackR (by omega) (by omega) (by omega))
    simp only [X86.length_encodeWords_singleton] at this
    exact this
  have hst2 : StateHolds after (c.sp + 32#64) (blocks.foldl compressBlock c.H0) :=
    Digest.StateHolds.transfer hB.hState
      (hS1.writesWithin (inside := fun a => c.sp.toNat - 8 ≤ a ∧ a < c.sp.toNat)
        (fun off hoff => by simp only [X86.length_encodeWords_singleton] at hoff; omega))
      (fun o ho hin => by rw [e20] at hin; omega)
  have hio : (iobuf + BitVec.ofNat 64 i).toNat = iobuf.toNat + i := toNat_iobuf_add (by omega)
  have hblk : after.readBytes (iobuf + BitVec.ofNat 64 i).toNat 64 =
      some ((c.chunk.drop i).take 64) := by
    rw [hio]; exact Memory.readBytes_sub_range hFM1.chunk (by omega) (by omega)
  refine ⟨hL1, compress_vc r11 (sp := c.sp) (blk := iobuf + BitVec.ofNat 64 i)
    (ret := base + 213#64) (by rfl) (by seg_read []) (by seg_read []) (by seg_read []) hret
    hFM1.code hFM1.kTable hst2 hblk hFM1.stackW hFM1.stackR hF.spAlign spL spH
    (.inl (by rw [hio]; simp only [iobuf, BitVec.toNat_ofNat]; omega)) ?_⟩
  intro fin hst3 hsp3 hsv3 hWc hrip3
  have hsv : ∀ r ∈ X86.sysv64.calleeSaved, r ≠ .r12 → r ≠ .r15 →
      fin.core.read r = s.core.read r := by
    intro r hr h1 h2
    rw [hsv3 r hr]
    simp only [X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> first | (exfalso; contradiction) | seg_read []
  have h12f : fin.core.read .r12 = iobuf + BitVec.ofNat 64 (i + 64) := by
    rw [hsv3 .r12 (by decide)]; seg_read []; rw [BitVec.ofNat_add]
  have h15f : fin.core.read .r15 = BitVec.ofNat 64 (c.chunk.length - (i + 64)) := by
    rw [hsv3 .r15 (by decide)]; seg_read []
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hL3 : Loaded fin.memory base code := by
    unfold Loaded; rw [hWc.fetchBytes]; · exact hL1
    intro o ho hin; simp only [calleeSpan, base_toNat, code_length] at hin ho; omega
  have hWcs : Memory.WritesWithin after fin.memory (stackSpan c.sp) :=
    hWc.mono fun a ha => calleeSpan_sub ha
  have hWcc : Memory.WritesWithin after fin.memory (callSpan c.sp) :=
    hWc.mono fun a ha => by simp only [calleeSpan, callSpan] at ha ⊢; omega
  have hFM3 := hFM1.transfer hlen hWcs spL
  have hWall := hW1c.trans hWcc
  simp only [withExtState]
  refine ⟨hrip3, hL3, hL3, ⟨hF.of_mem hFM3 (by seg_read [hsp3, hsp])
    (by seg_read [hsv .rbx (by decide) (by decide) (by decide)])
    (by seg_read [hsv .rbp (by decide) (by decide) (by decide)])
    (by seg_read [hsv .r13 (by decide) (by decide) (by decide)]),
    i + 64, by omega, by seg_read [h12f], hi64, by seg_read [h15f],
    blocks ++ [(c.chunk.drop i).take 64], [], ?_, ?_⟩, ?_⟩
  · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] at hacc ⊢
    rw [hacc, take_add_drop_take, List.append_assoc]
  · refine ⟨?_, readBytes_nil (by rw [toNat_sp_add spH (by decide)]; simp; omega), ?_, ?_, ?_,
      by simp⟩
    · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]; exact hst3
    · rw [loadN_transfer hWall (fun o ho hin => by simp only [callSpan, e80] at hin; omega)]
      exact hB.hBlen
    · rw [loadN_transfer hWall (fun o ho hin => by simp only [callSpan, e88] at hin; omega)]
      exact hB.hTotal
    · intro b hb
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hB.hFull b hb
      · simp only [List.length_take, List.length_drop]; omega
  · simp only [r15n]
    seg_read [h15f]
    rw [toNat_ofNat_small (by omega), h15, hn15]
    omega

set_option maxRecDepth 100000 in
theorem vc_91 (r11 : Core → Word) (c : Ctx) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 91 → inv91 c s →
      wpN (Isa.sys r11) code listing (cuts c) (stops c) (calls r11) (subs r11) base
        (some (8 * r15n s + 5)) 16 91 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, i, blocks, tail, hiL, h12, h15, hdx, hacc, hB⟩ := hinv
  have htl := hB.hRoom
  have hlen := hF.chunkLen
  have hmin : (if (!(64#64 - BitVec.ofNat 64 tail.length).ule (BitVec.ofNat 64 (c.chunk.length - i))) = true then
      BitVec.ofNat 64 (c.chunk.length - i) else 64#64 - BitVec.ofNat 64 tail.length) =
      BitVec.ofNat 64 (min (64 - tail.length) (c.chunk.length - i)) := by
    have h1 : (64#64 - BitVec.ofNat 64 tail.length).toNat = 64 - tail.length := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
    have h2 : (BitVec.ofNat 64 (c.chunk.length - i)).toNat = c.chunk.length - i :=
      toNat_ofNat_small (by omega)
    have hule : (64#64 - BitVec.ofNat 64 tail.length).ule (BitVec.ofNat 64 (c.chunk.length - i)) =
        decide (64 - tail.length ≤ c.chunk.length - i) := by
      rw [BitVec.ule, h1, h2]
    rw [hule]
    by_cases hc : 64 - tail.length ≤ c.chunk.length - i
    · simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [Nat.min_eq_left hc]
      apply BitVec.eq_of_toNat_eq; rw [h1]; simp only [BitVec.toNat_ofNat]; omega
    · simp only [hc, decide_false, Bool.not_false, ite_true]
      rw [Nat.min_eq_right (by omega)]
  seg_vc [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, h15, h12,
    hdx, hF.rbx, hmin, BitVec.and_self]
  have spH := hF.spHigh
  have spL := hF.spLow
  have hsp := hF.rsp
  generalize hkdef : min (64 - tail.length) (c.chunk.length - i) = kk at *
  have hk1 : 1 ≤ kk := by omega
  have hk64 : tail.length + kk ≤ 64 := by omega
  have hkL : i + kk ≤ c.chunk.length := by omega
  have hkn : (BitVec.ofNat 64 kk).toNat = kk := toNat_ofNat_small (by omega)
  have hn15 : (BitVec.ofNat 64 (c.chunk.length - i)).toNat = c.chunk.length - i :=
    toNat_ofNat_small (by omega)
  have e20 : (c.sp + 32#64).toNat = c.sp.toNat + 32 := toNat_sp_add spH (by decide)
  have e40 : (c.sp + 64#64).toNat = c.sp.toNat + 64 := toNat_sp_add spH (by decide)
  have e80 : (c.sp + 128#64).toNat = c.sp.toNat + 128 := toNat_sp_add spH (by decide)
  have e88 : (c.sp + 136#64).toNat = c.sp.toNat + 136 := toNat_sp_add spH (by decide)
  have edst : (c.sp + (64#64 + BitVec.ofNat 64 tail.length)).toNat = c.sp.toNat + 64 + tail.length := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hio : (iobuf + BitVec.ofNat 64 i).toNat = iobuf.toNat + i := toNat_iobuf_add (by omega)
  have hiob : iobuf.toNat = 0x40a0c0 := rfl
  have hchunk := hF.chunk
  rw [hsp]
  refine ⟨fun h0 => absurd h0 (by
    rw [Bool.not_eq_true, beq_eq_false_iff_ne]; intro e
    have := congrArg BitVec.toNat e; rw [hkn] at this; simp at this; omega), fun _ => ?_⟩
  have hsrcb : ∀ j < kk, loadN s.memory (iobuf + BitVec.ofNat 64 i + BitVec.ofNat 64 j) 1 =
      some (BitVec.ofNat 64 (c.chunk.getD (i + j) 0).toNat) := by
    intro j hj
    apply loadN_one_of_readBytes hchunk (by omega)
    rw [BitVec.toNat_add, hio, BitVec.toNat_ofNat]; simp only [hiob]; omega
  refine ⟨copy_pre_of r11 (k := kk) (src := iobuf + BitVec.ofNat 64 i)
    (dst := c.sp + (64#64 + BitVec.ofNat 64 tail.length)) rfl hl (by seg_read []) (by seg_read [h12])
    (by seg_read []) hk1 (by omega) (fun j hj => ⟨_, hsrcb j hj⟩)
    (by rw [edst]; exact Memory.Permitted.sub hF.stackW (by omega) (by omega) (by omega))
    (by rw [edst]; exact Memory.Permitted.sub hF.stackR (by omega) (by omega) (by omega))
    (by rw [edst]; omega) (by rw [hio, hiob]; omega) (by rw [edst, hio, hiob]; omega)
    (by rw [edst, base_toNat, code_length]; omega), fun t ht => ?_⟩
  obtain ⟨hript, hlt, hregs, hWd, hloads⟩ := copy_post_facts r11 (k := kk)
    (src := iobuf + BitVec.ofNat 64 i) (dst := c.sp + (64#64 + BitVec.ofNat 64 tail.length))
    (by seg_read []) (by seg_read [h12]) (by seg_read []) (by omega) ht
  have hWs : Memory.WritesWithin s.memory t.memory (stackSpan c.sp) :=
    hWd.mono fun a ha => by rw [edst] at ha; simp only [stackSpan]; omega
  have hFMt := hF.mem.transfer hlen hWs spL
  have hr : ∀ r, r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .rsi → r ≠ .rdi → r ≠ .r14 →
      t.core.read r = s.core.read r := by
    intro r h1 h2 h3 h4 h5 h6
    rw [hregs r h1 h2]; seg_read [h3, h4, h5, h6]
  have hout : ∀ a, c.sp.toNat + 64 + tail.length ≤ a → a < c.sp.toNat + 64 + tail.length + kk →
      ¬ (a < c.sp.toNat + 64 + tail.length) := fun a h _ => by omega
  have r1 : t.memory.readBytes (c.sp + 64#64).toNat tail.length = some tail := by
    rw [hWd.readBytes]; · exact hB.hTail
    intro o ho hin; rw [edst, e40] at hin; omega
  have r2 : t.memory.readBytes (c.sp.toNat + 64 + tail.length) kk =
      some ((c.chunk.drop i).take kk) := by
    have := readBytes_of_loads (m := t.memory) (a := c.sp + (64#64 + BitVec.ofNat 64 tail.length))
      (bs := (c.chunk.drop i).take kk) (by simp only [List.length_take, List.length_drop, edst]; omega)
      (fun j hj => by
        simp only [List.length_take, List.length_drop] at hj
        rw [hloads j (by omega)]
        show loadN s.memory _ 1 = _
        rw [hsrcb j (by omega)]
        congr 3
        simp only [List.getElem_take, List.getElem_drop]
        rw [List.getD_eq_getElem _ _ (by omega)])
    simpa only [edst, List.length_take, List.length_drop, Nat.min_eq_left (show kk ≤ c.chunk.length - i by omega)] using this
  refine ⟨hript, hlt, ⟨hF.of_mem hFMt (by seg_read [hr .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by seg_read [hr .rbx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by seg_read [hr .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by seg_read [hr .r13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]),
    i, kk, blocks, tail, hk1, hkL, hk64,
    by seg_read [hr .r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h12],
    by seg_read [hregs .r14 (by decide) (by decide)],
    by seg_read [hr .r15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h15],
    by seg_read [hregs .rsi (by decide) (by decide)],
    hacc, ?_, ?_, ?_, ?_, hB.hFull⟩, ?_⟩
  · exact Digest.StateHolds.transfer hB.hState hWd (fun o ho hin => by rw [edst, e20] at hin; omega)
  · have := Memory.readBytes_append r1 (by rw [e40]; exact r2)
    rw [e40] at this ⊢; exact this
  · rw [loadN_transfer hWd (fun o ho hin => by rw [edst, e80] at hin; omega)]; exact hB.hBlen
  · rw [loadN_transfer hWd (fun o ho hin => by rw [edst, e88] at hin; omega)]; exact hB.hTotal
  · simp only [r15n]
    seg_read [hr .r15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h15]
    omega

set_option maxRecDepth 100000 in
theorem vc_entry (r11 : Core → Word) (c : Ctx) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 22 → pre c s →
      wpN (Isa.sys r11) code listing (cuts c) (stops c) (calls r11) (subs r11) base none 16 22 s := by
  intro s hlv hl hrip hpre
  obtain ⟨hF, hax, hB⟩ := hpre
  have htot := hB.hTotal
  rw [← hF.rsp] at htot
  seg_vc [listing, cuts, stops, calls, subs, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hax, htot]
  have hlen := hF.chunkLen
  have spH := hF.spHigh
  have spL := hF.spLow
  have hsp := hF.rsp
  have hn : (BitVec.ofNat 64 c.chunk.length).toNat = c.chunk.length := toNat_ofNat_small (by omega)
  have e20 : (c.sp + 32#64).toNat = c.sp.toNat + 32 := toNat_sp_add spH (by decide)
  have e40 : (c.sp + 64#64).toNat = c.sp.toNat + 64 := toNat_sp_add spH (by decide)
  have e80 : (c.sp + 128#64).toNat = c.sp.toNat + 128 := toNat_sp_add spH (by decide)
  have e88 : (c.sp + 136#64).toNat = c.sp.toNat + 136 := toNat_sp_add spH (by decide)
  simp only [BitVec.and_self]
  rw [hsp]
  refine ⟨fun hm => ?_, fun _ => ⟨fun hz => ?_, fun hnz => ?_⟩⟩
  · rw [BitVec.msb_eq_decide, hn] at hm; simp at hm; omega
  · have h0 : c.chunk.length = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz); rw [hn] at this; simpa using this
    exact ⟨hF.congr rfl (by seg_read []) (by seg_read []) (by seg_read []) (by seg_read []),
      List.eq_nil_of_length_eq_zero h0, hB, by seg_read []⟩
  · have hpos : 0 < c.chunk.length := by
      have : BitVec.ofNat 64 c.chunk.length ≠ 0#64 := by simpa using hnz
      have h' : c.chunk.length ≠ 0 := fun e => this (by rw [e])
      omega
    refine ⟨by rw [e88]; exact Memory.Permitted.sub hF.stackW (by omega) (by omega) (by omega),
      fun after hstore => ?_⟩
    have hS := Stored.of_storeN hstore
    rw [e88] at hS
    have hW8 : Memory.WritesWithin s.memory after
        (fun a => c.sp.toNat + 136 ≤ a ∧ a < c.sp.toNat + 144) :=
      hS.writesWithin (fun off hoff => by simp only [length_leBytes] at hoff; omega)
    have hW : Memory.WritesWithin s.memory after (stackSpan c.sp) :=
      hW8.mono fun a ha => by simp only [stackSpan]; omega
    have hL : Loaded after base code :=
      Loaded.of_stored hl hS (by simp only [length_leBytes, base_toNat, code_length]; omega)
    have hr : s.memory.Permitted .read (c.sp + 136#64).toNat 8 := by
      rw [e88]; exact Memory.Permitted.sub hF.stackR (by omega) (by omega) (by omega)
    refine ⟨hL, hL, hF.of_mem (hF.mem.transfer hlen hW spL) (by seg_read []) (by seg_read [])
      (by seg_read []) (by seg_read []), 0, hpos, hpos, by seg_read []; rfl, by omega, by seg_read [Nat.sub_zero],
      c.blocks, c.tail, by simp, ?_, ?_, ?_, ?_, hB.hFull, hB.hRoom⟩
    · exact Digest.StateHolds.transfer hB.hState hW8 (fun o ho hin => by rw [e20] at hin; omega)
    · rw [hW8.readBytes]; · exact hB.hTail
      intro o ho hin; have := hB.hRoom; rw [e40] at hin; omega
    · rw [loadN_transfer hW8 (fun o ho hin => by rw [e80] at hin; omega)]; exact hB.hBlen
    · rw [loadN_storeN hstore hr]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
      omega

/-- All the VCs of the `sha_update` segment. -/
theorem vc_all (r11 : Core → Word) (c : Ctx) :
    vc (Isa.sys r11) code listing (cuts c) (stops c) (calls r11) (subs r11) base 22 (pre c) 16 := by
  refine ⟨vc_entry r11 c, ?_⟩
  intro oc hoc
  simp only [cuts, List.mem_cons, List.not_mem_nil, or_false] at hoc
  rcases hoc with rfl | rfl | rfl | rfl | rfl
  · exact vc_72 r11 c
  · exact vc_91 r11 c
  · exact fun s hlv hl hrip hinv => wpN_mono (by decide) (vc_145 r11 c s hlv hl hrip hinv)
  · exact fun s hlv hl hrip hinv => wpN_mono (by decide) (vc_170 r11 c s hlv hl hrip hinv)
  · exact fun s hlv hl hrip hinv => wpN_mono (by decide) (vc_176 r11 c s hlv hl hrip hinv)

/-- **VERIFIED. `sha_update` in `sha256sum-min`.** After `read(fd, iobuf, 32768)` returned
`r = chunk.length` bytes (at `0x402f06`), with the `struct sha` holding the chaining value of
`blocks` and the buffered `tail`, the process reaches, by internal steps only (no system
call, no `brk`: retiring steps `rStep`), either

* for `r > 0`, the next `read` (`0x402ef0`), with the struct holding the fold of the full blocks of
  `blocks ++ tail ++ chunk` and the rest buffered (`postRead`), or
* for `r = 0`, the padding (`0x403034`) with the struct unchanged (`postEof`).

Every byte of the chunk is consumed, through the inlined `memcpy` (`Copy.summary`) and the
linked `sha256_compress` (`compressCall`, via the pilot contract and the call bridge). -/
theorem update_runs (r11 : Core → Word) (c : Ctx) (s : XState) (hlv : s.faulted = false)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 22)
    (hpre : pre c s) :
    ∃ t, Silmaril.Machine.Execution.Reaches rStep s t ∧ t.faulted = false ∧
      Loaded t.memory base code ∧
      ((t.core.rip = base + BitVec.ofNat 64 0 ∧ postRead c t) ∨
        (t.core.rip = base + BitVec.ofNat 64 324 ∧ postEof c t)) := by
  obtain ⟨o, q, t, hq, ht, hr, hrip', hl', hlv'⟩ :=
    sound (I := Isa.sys r11) listing_valid (vc_all r11 c) s hlv hl hrip hpre
  refine ⟨t, hr, hlv', hl', ?_⟩
  simp only [stops, List.lookup_cons, List.lookup_nil] at hq
  split at hq
  · rename_i he; cases hq; simp only [beq_iff_eq] at he; subst he; exact .inl ⟨hrip', ht⟩
  · split at hq
    · rename_i he; cases hq; simp only [beq_iff_eq] at he; subst he; exact .inr ⟨hrip', ht⟩
    · split at hq
      · cases hq; exact ht.elim
      · cases hq

end Silmaril.Apps.Sha256sum.Binary.Digest.Update

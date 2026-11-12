module

public import Silmaril.Libc.X86Alloc.Ladder.Coalesce.Defs
public import Silmaril.Libc.X86Alloc.Ladder.FirstFit.Live
public import Silmaril.Raw.Libc.X86Alloc.Steps
public import Silmaril.Raw.Libc.X86Alloc.Whole
public import Silmaril.Raw.Libc.X86Alloc.Loop
public import Silmaril.Raw.Libc.X86Alloc.HdrSeg
public import Silmaril.X86.Sep.Alloc.Thms

/-!
# Proofs: rung 06 (coalescing) `free` — the listing and the merge lemmas

The allocator state and tokens are rung 05's (`FirstFit.iface`): the coalescing `free` keeps the
free list an `hdrSeg` (its address order is not needed for safety: each merge is guarded by an
address-equality check, so the merged blocks are contiguous). `merge_pay` joins a block's payload
with the contiguous block after it; `close` folds the final list into the loose interface's `mm`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.Coalesce
open Silmaril.Libc.X86Alloc.Ladder.FirstFit (iface flAddr)
open Silmaril.Raw.Libc.X86Alloc.Frame

/-- The operand `d(%b,%i,1)`. -/
def idx (b i : Reg) (h : i ≠ .rsp) (d : BitVec 32) : Silmaril.X86.Ext.Mem :=
  ⟨.reg b, some ⟨i, 0, h⟩, d, fun h => by cases h⟩

theorem idx_addr (b i : Reg) (h : i ≠ .rsp) (d : BitVec 32) (s : Silmaril.X86.State) (next : Word) :
    (idx b i h d).addr s next = s.read b + s.read i + d.signExtend 64 := by
  simp [Silmaril.X86.Ext.Mem.addr, idx, Silmaril.X86.Ext.Base.value, Silmaril.X86.Ext.Index.value]

/-! ## The listing of `free`, decoded once -/

theorem e128 : Silmaril.X86.Ext.decode ((code.drop 128).take 3) = some (.mov .q (.reg .rsi) .rdi, 3) := by
  decide +kernel
theorem e131 : Silmaril.X86.Ext.decode ((code.drop 131).take 3) = some (.test .q (.reg .rdi) .rdi, 3) := by
  decide +kernel
theorem e134 : Silmaril.X86.Ext.decode ((code.drop 134).take 2) = some (.jcc8 .e 0x50, 2) := by
  decide +kernel
theorem e136 : Silmaril.X86.Ext.decode ((code.drop 136).take 7) = some (.load .q .rax (ripMem 0x1ce1), 7) := by
  decide +kernel
theorem e143 : Silmaril.X86.Ext.decode ((code.drop 143).take 4) = some (.lea .q .rdx (Silmaril.X86.Sep.Insn.memAt .rdi 0xfffffff0), 4) := by
  decide +kernel
theorem e147 : Silmaril.X86.Ext.decode ((code.drop 147).take 3) = some (.test .q (.reg .rax) .rax, 3) := by
  decide +kernel
theorem e150 : Silmaril.X86.Ext.decode ((code.drop 150).take 2) = some (.jcc8 .e 0x60, 2) := by
  decide +kernel
theorem e152 : Silmaril.X86.Ext.decode ((code.drop 152).take 3) = some (.alu .q .cmp (.reg .rax) .rdx, 3) := by
  decide +kernel
theorem e155 : Silmaril.X86.Ext.decode ((code.drop 155).take 2) = some (.jcc8 .ae 0x5b, 2) := by
  decide +kernel
theorem e157 : Silmaril.X86.Ext.decode ((code.drop 157).take 3) = some (.nop 2, 3) := by
  decide +kernel
theorem e160 : Silmaril.X86.Ext.decode ((code.drop 160).take 3) = some (.mov .q (.reg .rcx) .rax, 3) := by
  decide +kernel
theorem e163 : Silmaril.X86.Ext.decode ((code.drop 163).take 4) = some (.load .q .rax (Silmaril.X86.Sep.Insn.memAt .rax 8), 4) := by
  decide +kernel
theorem e167 : Silmaril.X86.Ext.decode ((code.drop 167).take 3) = some (.test .q (.reg .rax) .rax, 3) := by
  decide +kernel
theorem e170 : Silmaril.X86.Ext.decode ((code.drop 170).take 2) = some (.jcc8 .e 0x05, 2) := by
  decide +kernel
theorem e172 : Silmaril.X86.Ext.decode ((code.drop 172).take 3) = some (.alu .q .cmp (.reg .rax) .rdx, 3) := by
  decide +kernel
theorem e175 : Silmaril.X86.Ext.decode ((code.drop 175).take 2) = some (.jcc8 .b 0xef, 2) := by
  decide +kernel
theorem e177 : Silmaril.X86.Ext.decode ((code.drop 177).take 4) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0xfffffff8)) .rax, 4) := by
  decide +kernel
theorem e181 : Silmaril.X86.Ext.decode ((code.drop 181).take 3) = some (.test .q (.reg .rax) .rax, 3) := by
  decide +kernel
theorem e184 : Silmaril.X86.Ext.decode ((code.drop 184).take 2) = some (.jcc8 .e 0x0d, 2) := by
  decide +kernel
theorem e186 : Silmaril.X86.Ext.decode ((code.drop 186).take 4) = some (.load .q .rdi (Silmaril.X86.Sep.Insn.memAt .rsi 0xfffffff0), 4) := by
  decide +kernel
theorem e190 : Silmaril.X86.Ext.decode ((code.drop 190).take 4) = some (.lea .q .r8 (idx .rsi .rdi (by decide) 0), 4) := by
  decide +kernel
theorem e194 : Silmaril.X86.Ext.decode ((code.drop 194).take 3) = some (.alu .q .cmp (.reg .rax) .r8, 3) := by
  decide +kernel
theorem e197 : Silmaril.X86.Ext.decode ((code.drop 197).take 2) = some (.jcc8 .e 0x4f, 2) := by
  decide +kernel
theorem e199 : Silmaril.X86.Ext.decode ((code.drop 199).take 3) = some (.load .q .rax (Silmaril.X86.Sep.Insn.memAt .rcx 0), 3) := by
  decide +kernel
theorem e202 : Silmaril.X86.Ext.decode ((code.drop 202).take 4) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rcx 8)) .rdx, 4) := by
  decide +kernel
theorem e206 : Silmaril.X86.Ext.decode ((code.drop 206).take 5) = some (.lea .q .rdi (idx .rcx .rax (by decide) 0x10), 5) := by
  decide +kernel
theorem e211 : Silmaril.X86.Ext.decode ((code.drop 211).take 3) = some (.alu .q .cmp (.reg .rdx) .rdi, 3) := by
  decide +kernel
theorem e214 : Silmaril.X86.Ext.decode ((code.drop 214).take 2) = some (.jcc8 .e 0x08, 2) := by
  decide +kernel
theorem e224 : Silmaril.X86.Ext.decode ((code.drop 224).take 4) = some (.load .q .rdx (Silmaril.X86.Sep.Insn.memAt .rsi 0xfffffff0), 4) := by
  decide +kernel
theorem e228 : Silmaril.X86.Ext.decode ((code.drop 228).take 5) = some (.lea .q .rax (idx .rax .rdx (by decide) 0x10), 5) := by
  decide +kernel
theorem e233 : Silmaril.X86.Ext.decode ((code.drop 233).take 3) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rcx 0)) .rax, 3) := by
  decide +kernel
theorem e236 : Silmaril.X86.Ext.decode ((code.drop 236).take 4) = some (.load .q .rax (Silmaril.X86.Sep.Insn.memAt .rsi 0xfffffff8), 4) := by
  decide +kernel
theorem e240 : Silmaril.X86.Ext.decode ((code.drop 240).take 4) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rcx 8)) .rax, 4) := by
  decide +kernel
theorem e248 : Silmaril.X86.Ext.decode ((code.drop 248).take 4) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0xfffffff8)) .rax, 4) := by
  decide +kernel
theorem e252 : Silmaril.X86.Ext.decode ((code.drop 252).take 3) = some (.test .q (.reg .rax) .rax, 3) := by
  decide +kernel
theorem e255 : Silmaril.X86.Ext.decode ((code.drop 255).take 2) = some (.jcc8 .e 0x0d, 2) := by
  decide +kernel
theorem e257 : Silmaril.X86.Ext.decode ((code.drop 257).take 4) = some (.load .q .rcx (Silmaril.X86.Sep.Insn.memAt .rsi 0xfffffff0), 4) := by
  decide +kernel
theorem e261 : Silmaril.X86.Ext.decode ((code.drop 261).take 4) = some (.lea .q .rdi (idx .rsi .rcx (by decide) 0), 4) := by
  decide +kernel
theorem e265 : Silmaril.X86.Ext.decode ((code.drop 265).take 3) = some (.alu .q .cmp (.reg .rax) .rdi, 3) := by
  decide +kernel
theorem e268 : Silmaril.X86.Ext.decode ((code.drop 268).take 2) = some (.jcc8 .e 0x22, 2) := by
  decide +kernel
theorem e270 : Silmaril.X86.Ext.decode ((code.drop 270).take 7) = some (.mov .q (.mem (ripMem 0x1c5b)) .rdx, 7) := by
  decide +kernel
theorem e278 : Silmaril.X86.Ext.decode ((code.drop 278).take 3) = some (.load .q .r8 (Silmaril.X86.Sep.Insn.memAt .rax 0), 3) := by
  decide +kernel
theorem e281 : Silmaril.X86.Ext.decode ((code.drop 281).take 4) = some (.load .q .rax (Silmaril.X86.Sep.Insn.memAt .rax 8), 4) := by
  decide +kernel
theorem e285 : Silmaril.X86.Ext.decode ((code.drop 285).take 5) = some (.lea .q .rdi (idx .rdi .r8 (by decide) 0x10), 5) := by
  decide +kernel
theorem e290 : Silmaril.X86.Ext.decode ((code.drop 290).take 4) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0xfffffff8)) .rax, 4) := by
  decide +kernel
theorem e294 : Silmaril.X86.Ext.decode ((code.drop 294).take 4) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0xfffffff0)) .rdi, 4) := by
  decide +kernel
theorem e298 : Silmaril.X86.Ext.decode ((code.drop 298).take 2) = some (.jmp8 0x9b, 2) := by
  decide +kernel
theorem e304 : Silmaril.X86.Ext.decode ((code.drop 304).take 3) = some (.load .q .rdi (Silmaril.X86.Sep.Insn.memAt .rax 0), 3) := by
  decide +kernel
theorem e307 : Silmaril.X86.Ext.decode ((code.drop 307).take 4) = some (.load .q .rax (Silmaril.X86.Sep.Insn.memAt .rax 8), 4) := by
  decide +kernel
theorem e311 : Silmaril.X86.Ext.decode ((code.drop 311).take 5) = some (.lea .q .rcx (idx .rcx .rdi (by decide) 0x10), 5) := by
  decide +kernel
theorem e316 : Silmaril.X86.Ext.decode ((code.drop 316).take 4) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0xfffffff8)) .rax, 4) := by
  decide +kernel
theorem e320 : Silmaril.X86.Ext.decode ((code.drop 320).take 4) = some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0xfffffff0)) .rcx, 4) := by
  decide +kernel
theorem e324 : Silmaril.X86.Ext.decode ((code.drop 324).take 2) = some (.jmp8 0xc8, 2) := by
  decide +kernel
theorem q216 : (code.drop 216).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem q244 : (code.drop 244).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem q277 : (code.drop 277).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem hlen : code.length = 336 := by decide +kernel
theorem fit (o k : Nat) (h : o + k ≤ 336 := by decide) : o + k ≤ code.length := hlen ▸ h

/-! ## Merging and closing -/

theorem toNat_add8 (c : Block) (hWF : c.WF) : (c.addr + 8#64).toNat = c.addr.toNat + 8 := by
  have := hWF.2.2
  rw [BitVec.toNat_add, show (8#64 : Word).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]

/-- **Merge** a payload with the contiguous block after it. -/
theorem merge_pay (a : Nat) (sz : Nat) (c : Block) (X Y : Word) (hc : c.addr.toNat = a + 16 + sz)
    (hWF : c.WF) :
    (blockAny (a + 16) sz ∗ wordPt c.addr.toNat X ∗ wordPt (c.addr + 8#64).toNat Y ∗
      blockAny (c.addr.toNat + 16) c.size) ⊢ₛ blockAny (a + 16) (sz + 16 + c.size) := by
  rw [toNat_add8 c hWF]
  refine entails_trans (sep_mono_right _ (sep_mono (wordPt_blockAny _ _)
    (sep_mono_left _ (wordPt_blockAny _ _)))) (entails_of_eq ?_)
  rw [show sz + 16 + c.size = sz + (8 + (8 + c.size)) by omega, blockAny_add, blockAny_add,
    blockAny_add, ← hc, show c.addr.toNat + 8 + 8 = c.addr.toNat + 16 by omega]

/-- The merged block is well formed. -/
theorem merge_WF (a : Word) (sz : Nat) (c : Block) (ha : Block.WF ⟨a, sz⟩)
    (hc : c.addr.toNat = a.toNat + 16 + sz) (hWF : c.WF) : Block.WF ⟨a, sz + 16 + c.size⟩ := by
  obtain ⟨h0, h16, -⟩ := ha
  have := hWF.2.2
  exact ⟨h0, h16, by simp only at this ⊢; omega⟩

/-- **Close**: a free list from the `freelist` global is the loose interface's state. -/
theorem close (fl : List Block) (h : Word) :
    (wordPt flAddr.toNat h ∗ hdrSeg fl h ∗ strue) ⊢ₛ iface.toIface.mm :=
  sexists_intro ([] : List Block) (sexists_intro fl (sexists_intro h
    (spure_sep_intro (fun _ hb => absurd hb List.not_mem_nil) (entails_refl _))))

end Silmaril.Raw.Libc.X86Alloc.Ladder.CoalesceFree

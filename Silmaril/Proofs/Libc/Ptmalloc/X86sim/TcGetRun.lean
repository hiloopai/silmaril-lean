module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.Kit

/-!
# ptmalloc x86sim: gcc's `tcache_get`, as an instruction sequence

`TcGetSeqR code o ri l0 l34`: the 11 instructions gcc emits for an inlined `tcache_get (tc_idx)`
(`__libc_malloc`, after `tcache->counts[tc_idx] > 0` was tested) start at offset `o` of `code`,
with the tcache in `rdx`, the bin in `ri` and its count in `rcx` (`TcGetSeq code o`: `ri = r12`,
gcc 13/14, glibc 2.39/2.40; glibc 2.36's gcc 12 uses `rbp`, which shortens two instructions). It is a list of decode
facts, so a pin whose compiler emitted the same sequence (any offset, any address) reuses
`tcGetRun` by `decide` on its own bytes.

`tcGetRun`: from such a state, with the head entry `e` aligned and its `next` word `v`
readable, the run reaches `o + tcGetLen l0 l34` (47 for `r12`) having done exactly the three stores of `tcache_get`
(`entries[i] := REVEAL_PTR (e->next)`, `counts[i] := count - 1`, `e->key := 0`), with
`rax = e` and every register but `rax`, `rcx`, `rsi`, `rdi` unchanged.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN Mem Cond subFlagsN logicFlagsN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.X86
namespace Silmaril.Libc.Ptmalloc.X86sim

/-- An `Ext` instruction as a `Str9Fs` one. -/
abbrev ix (i : Silmaril.X86.Ext.Instr) : Str9Fs.Instr := .str9 (.ext9 (.ext8 (.base i)))

/-- **gcc's inlined `tcache_get`** at offset `o` of `code`, with the bin index in register `ri`
(the decode facts of its 11 instructions). `l0` and `l34` are the lengths of the two instructions
that address through `ri` (`lea 0x10(%ri),%rdi` and `mov %cx,(%rdx,%ri,2)`): 5 bytes each for
`r12` (gcc 13/14, glibc 2.39/2.40), 4 bytes each for `rbp` (gcc 12, glibc 2.36). The block is
`tcGetLen l0 l34` bytes long. Finding V1-F3. -/
structure TcGetSeqR (code : List Byte) (o : Nat) (ri : Reg) (l0 l34 : Nat) : Prop where
  /-- The index register is neither the stack pointer (it is an SIB index) nor one of the
  registers the sequence writes or reads otherwise. -/
  regs : ri ≠ .rsp ∧ ri ≠ .rax ∧ ri ≠ .rcx ∧ ri ≠ .rdi ∧ ri ≠ .rsi ∧ ri ≠ .rdx := by decide
  fit : o + (37 + l0 + l34) ≤ code.length
  i0 : Str9Fs.decode ((code.drop o).take l0) = some (ix (.lea .q .rdi (Ext.Mem.ofReg ri none 0x10#32)), l0)
  i5 : Str9Fs.decode ((code.drop (o + l0)).take 4) =
    some (ix (.load .q .rax (Ext.Mem.ofReg .rdx (some ⟨.rdi, 3#2, by decide⟩) 0#32)), 4)
  i9 : Str9Fs.decode ((code.drop (o + l0 + 4)).take 2) = some (ix (.testA8 0x0f#8), 2)
  i11 : ∃ rel, Str9Fs.decode ((code.drop (o + l0 + 6)).take 6) = some (ix (.jcc .ne rel), 6)
  i17 : Str9Fs.decode ((code.drop (o + l0 + 12)).take 3) = some (ix (.mov .q (.reg .rsi) .rax), 3)
  i20 : Str9Fs.decode ((code.drop (o + l0 + 15)).take 3) =
    some (ix (.aluI8 .d .sub (.reg .rcx) 0x01#8), 3)
  i23 : Str9Fs.decode ((code.drop (o + l0 + 18)).take 4) =
    some (ix (.shift .q .shr (.reg .rsi) (.imm 0x0c#8)), 4)
  i27 : Str9Fs.decode ((code.drop (o + l0 + 22)).take 3) =
    some (ix (.aluR .q .xor .rsi (.mem (Ext.Mem.ofReg .rax none 0#32))), 3)
  i30 : Str9Fs.decode ((code.drop (o + l0 + 25)).take 4) =
    some (ix (.mov .q (.mem (Ext.Mem.ofReg .rdx (some ⟨.rdi, 3#2, by decide⟩) 0#32)) .rsi), 4)
  i34 : Str9Fs.decode ((code.drop (o + l0 + 29)).take l34) =
    some (ix (.store .w (.mem (Ext.Mem.ofReg .rdx (some ⟨ri, 1#2, regs.1⟩) 0#32)) .rcx), l34)
  i39 : Str9Fs.decode ((code.drop (o + l0 + 29 + l34)).take 8) =
    some (ix (.movI .q (.mem (Ext.Mem.ofReg .rax none 8#32)) 0#32), 8)

/-- The length of the `tcache_get` sequence (47 bytes with `r12`, 45 with `rbp`). -/
abbrev tcGetLen (l0 l34 : Nat) : Nat := 37 + l0 + l34

/-- **gcc 13/14's inlined `tcache_get`** (glibc 2.39/2.40): the bin index in `r12`, 47 bytes. -/
abbrev TcGetSeq (code : List Byte) (o : Nat) : Prop := TcGetSeqR code o .r12 5 5

/-- A load survives a store apart from it. -/
theorem ld_store {m m' : Memory} {a b : Word} {k k' : Nat} {w v : Word}
    (hs : storeN m a k w = some m') (hap : Apart a.toNat k b.toNat (b.toNat + k'))
    (h : loadN m b k' = some v) : loadN m' b k' = some v := by
  have wo := Silmaril.X86.Ext.storeN_writesOnly hs
  rw [Memory.writesOnly_iff_writesWithin] at wo
  refine ld_ww wo (fun i hi ⟨h1, h2⟩ => ?_) h
  obtain ⟨j, hj, hj'⟩ : ∃ j < k, a.toNat + j = b.toNat + i := ⟨b.toNat + i - a.toNat, by omega, by omega⟩
  exact hap j hj ⟨by omega, by omega⟩

/-- A permission survives a store. -/
theorem perm_store {m m' : Memory} {a : Word} {k : Nat} {w : Word} {acc : Silmaril.Process.Access}
    {x n : Nat} (hs : storeN m a k w = some m') (h : m.Permitted acc x n) : m'.Permitted acc x n := by
  have e := (Silmaril.X86.Ext.storeN_writesOnly hs).1
  simpa [Memory.Permitted, Memory.checkSpan, Memory.permits, e] using h

/-- The footprint of a store. -/
def span (a : Word) (k : Nat) (x : Nat) : Prop := a.toNat ≤ x ∧ x < a.toNat + k

theorem ww_store {m m' : Memory} {a : Word} {k : Nat} {w : Word} (hs : storeN m a k w = some m') :
    m.WritesWithin m' (span a k) := by
  have wo := Silmaril.X86.Ext.storeN_writesOnly hs
  rw [Memory.writesOnly_iff_writesWithin] at wo
  exact wo

set_option maxHeartbeats 4000000 in
/-- **The run of `tcache_get`**, for any code carrying `TcGetSeqR` at `o` (any index register). -/
theorem tcGetRun {code : List Byte} {o : Nat} {ri : Reg} {l0 l34 : Nat} (hs : TcGetSeqR code o ri l0 l34)
    {A : Word} {m : MState}
    {tc idx cnt e v : Word} (hl : Loaded m.memory A code)
    (hrip : m.core.rip = A + BitVec.ofNat 64 o) (hrdx : m.core.read .rdx = tc)
    (hr12 : m.core.read ri = idx) (hrcx : m.core.read .rcx = cnt)
    (hent : loadN m.memory (tc + ((idx + 16#64) <<< 3)) 8 = some e) (he : e.setWidth 8 &&& 0xf#8 = 0)
    (hnext : loadN m.memory e 8 = some v)
    (hw1 : m.memory.Permitted .write (tc + ((idx + 16#64) <<< 3)).toNat 8)
    (hw2 : m.memory.Permitted .write (tc + (idx <<< 1)).toNat 2)
    (hw3 : m.memory.Permitted .write (e + 8#64).toNat 8)
    (hc1 : Apart (tc + ((idx + 16#64) <<< 3)).toNat 8 A.toNat (A.toNat + code.length))
    (hc2 : Apart (tc + (idx <<< 1)).toNat 2 A.toNat (A.toNat + code.length))
    (hc3 : Apart (e + 8#64).toNat 8 A.toNat (A.toNat + code.length)) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 (o + tcGetLen l0 l34) ∧
      m'.core.read .rax = e ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ Loaded m'.memory A code ∧
      ∃ m1 m2, storeN m.memory (tc + ((idx + 16#64) <<< 3)) 8 ((e >>> 12) ^^^ v) = some m1 ∧
        storeN m1 (tc + (idx <<< 1)) 2 ((cnt.setWidth 32 - 1#32).setWidth 64) = some m2 ∧
        storeN m2 (e + 8#64) 8 0#64 = some m'.memory := by
  have hN : code.length = code.length := rfl
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrdx hr12 hrcx hent hnext hw1 hw2 hw3 ⊢
  obtain ⟨rel, i11⟩ := hs.i11
  have hf := hs.fit
  obtain ⟨-, nax, ncx, ndi, nsi, ndx⟩ := hs.regs
  -- the loads, then the three stores
  refine ex_head (stepC hN (o := o) (l := l0) hl hrip (by omega) hs.i0 exec_lea) ?_
  refine ex_head (stepC hN (o := o + l0) (l := 4) hl (by simp [hrip, rip_add]) (by omega) hs.i5
    (exec_loadidx8 (v := e) (by simpa [hrdx, hr12, ndi, ndx] using hent))) ?_
  refine ex_head (stepC hN (o := o + l0 + 4) (l := 2) hl (by simp [hrip, rip_add]) (by omega) hs.i9
    exec_testA8) ?_
  refine ex_head (stepC hN (o := o + l0 + 6) (l := 6) hl (by simp [hrip, rip_add]) (by omega) i11
    (exec_jcc (b := false) (by
      simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN,
        Silmaril.X86.Ext.kNot, he]))) ?_
  refine ex_head (stepC hN (o := o + l0 + 12) (l := 3) hl (by simp [hrip, rip_add]) (by omega) hs.i17
    exec_movrr) ?_
  refine ex_fC hN hl (o := o + l0 + 15) (l := 3) (by simp [hrip, rip_add]) (by omega) hs.i20
    (exec_aluI8r32 (op := .sub) (by decide)) (fun f1 => ?_)
  refine ex_fC hN hl (o := o + l0 + 18) (l := 4) (by simp [hrip, rip_add]) (by omega) hs.i23
    exec_shr (fun f2 => ?_)
  refine ex_fC hN hl (o := o + l0 + 22) (l := 3) (by simp [hrip, rip_add]) (by omega) hs.i27
    (exec_xorm (v := v) (by simpa using hnext)) (fun f3 => ?_)
  obtain ⟨mem1, h1, -⟩ := Silmaril.X86.Ext.storeN_isSome (v := (e >>> 12) ^^^ v) hw1
  obtain ⟨mem2, h2, -⟩ := Silmaril.X86.Ext.storeN_isSome
    (v := (cnt.setWidth 32 - 1#32).setWidth 64) (perm_store h1 hw2)
  obtain ⟨mem3, h3, -⟩ := Silmaril.X86.Ext.storeN_isSome (v := 0#64) (perm_store h2 (perm_store h1 hw3))
  have hl1 := loadedC_store hN hl h1 hc1
  have hl2 := loadedC_store hN hl1 h2 hc2
  have hl3 := loadedC_store hN hl2 h3 hc3
  refine ex_head (stepC hN (o := o + l0 + 25) (l := 4) hl (by simp [hrip, rip_add]) (by omega) hs.i30
    (exec_storeidx8 (mem' := mem1) (by
      simpa [hrdx, hr12, ndi, ndx, nsi, nax, ncx, Silmaril.X86.Ext.AluOp.resultN] using h1))) ?_
  refine ex_head (stepC hN (o := o + l0 + 29) (l := l34) hl1 (by simp [hrip, rip_add]) (by omega) hs.i34
    (exec_storew (mem' := mem2) (by
      simpa [hrdx, hr12, hrcx, ndi, ndx, nsi, nax, ncx, Silmaril.X86.Ext.AluOp.resultN] using h2))) ?_
  refine ex_head (stepC hN (o := o + l0 + 29 + l34) (l := 8) hl2 (by simp [hrip, rip_add]) (by omega) hs.i39
    (exec_movI0 (mem' := mem3) (by simpa using h3))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, rfl, hl3, mem1, mem2, h1, h2, h3⟩
  · rw [show o + tcGetLen l0 l34 = o + l0 + 29 + l34 + 8 by unfold tcGetLen; omega]
    simp [hrip, rip_add]
  · simp
  · intro r a b c d; simp [a, b, c, d]

end Silmaril.Libc.Ptmalloc.X86sim

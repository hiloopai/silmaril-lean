module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcGetRun

/-!
# ptmalloc x86sim: gcc's `tcache_put`, as an instruction sequence

`TcPutSeq code o kd jr`: the 10 instructions gcc emits for an inlined `tcache_put (chunk,
tc_idx)` (glibc 2.39 `_int_free`, after the bin and count tests) start at offset `o` of `code`:
the chunk in `rsi`, its payload in `r10`, the tcache in `r8`, the bin in `rax`, its count in
`rcx`; `tcache_key` is read rip-relative (displacement `kd`) and the block ends with a `jmp`
(displacement `jr`) to the function's epilogue.

`tcPutRun`: the four stores of `tcache_put` (`e->key := tcache_key`,
`e->next := PROTECT_PTR (&e->next, entries[i])`, `entries[i] := e`, `counts[i] += 1`) and the
jump; every register but `rcx`, `rdx` unchanged.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN Mem Cond subFlagsN logicFlagsN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.X86
namespace Silmaril.Libc.Ptmalloc.X86sim

/-- **gcc's inlined `tcache_put`** at offset `o` of `code`. -/
structure TcPutSeq (code : List Byte) (o : Nat) (kd jr : BitVec 32) : Prop where
  fit : o + 51 ≤ code.length
  i0 : Str9Fs.decode ((code.drop o).take 7) = some (ix (.load .q .rdx (Ext.Mem.ofRip kd)), 7)
  i7 : Str9Fs.decode ((code.drop (o + 7)).take 3) = some (ix (.aluI8 .d .add (.reg .rcx) 0x01#8), 3)
  i10 : Str9Fs.decode ((code.drop (o + 10)).take 4) =
    some (ix (.mov .q (.mem (Ext.Mem.ofReg .rsi none 0x18#32)) .rdx), 4)
  i14 : Str9Fs.decode ((code.drop (o + 14)).take 3) = some (ix (.mov .q (.reg .rdx) .r10), 3)
  i17 : Str9Fs.decode ((code.drop (o + 17)).take 4) =
    some (ix (.shift .q .shr (.reg .rdx) (.imm 0x0c#8)), 4)
  i21 : Str9Fs.decode ((code.drop (o + 21)).take 8) =
    some (ix (.aluR .q .xor .rdx (.mem (Ext.Mem.ofReg .r8 (some ⟨.rax, 3#2, by decide⟩) 0x80#32))), 8)
  i29 : Str9Fs.decode ((code.drop (o + 29)).take 4) =
    some (ix (.mov .q (.mem (Ext.Mem.ofReg .rsi none 0x10#32)) .rdx), 4)
  i33 : Str9Fs.decode ((code.drop (o + 33)).take 8) =
    some (ix (.mov .q (.mem (Ext.Mem.ofReg .r8 (some ⟨.rax, 3#2, by decide⟩) 0x80#32)) .r10), 8)
  i41 : Str9Fs.decode ((code.drop (o + 41)).take 5) =
    some (ix (.store .w (.mem (Ext.Mem.ofReg .r8 (some ⟨.rax, 1#2, by decide⟩) 0#32)) .rcx), 5)
  i46 : Str9Fs.decode ((code.drop (o + 46)).take 5) = some (ix (.jmp jr), 5)

set_option maxHeartbeats 4000000 in
/-- **The run of `tcache_put`**, for any code carrying `TcPutSeq` at `o`. -/
theorem tcPutRun {code : List Byte} {o : Nat} {kd jr : BitVec 32} (hs : TcPutSeq code o kd jr)
    {A : Word} {m : MState} {q tc idx cnt key h : Word} (hl : Loaded m.memory A code)
    (hrip : m.core.rip = A + BitVec.ofNat 64 o) (hrsi : m.core.read .rsi = q)
    (hr10 : m.core.read .r10 = q + 0x10#64) (hr8 : m.core.read .r8 = tc)
    (hrax : m.core.read .rax = idx) (hrcx : m.core.read .rcx = cnt)
    (hkey : loadN m.memory (A + BitVec.ofNat 64 (o + 7) + kd.signExtend 64) 8 = some key)
    (hent : loadN m.memory (tc + (idx <<< 3) + 0x80#64) 8 = some h)
    (hw0 : m.memory.Permitted .write (q + 0x18#64).toNat 8)
    (hw1 : m.memory.Permitted .write (q + 0x10#64).toNat 8)
    (hw2 : m.memory.Permitted .write (tc + (idx <<< 3) + 0x80#64).toNat 8)
    (hw3 : m.memory.Permitted .write (tc + (idx <<< 1)).toNat 2)
    (hke : Apart (q + 0x18#64).toNat 8 (tc + (idx <<< 3) + 0x80#64).toNat
      ((tc + (idx <<< 3) + 0x80#64).toNat + 8))
    (hc0 : Apart (q + 0x18#64).toNat 8 A.toNat (A.toNat + code.length))
    (hc1 : Apart (q + 0x10#64).toNat 8 A.toNat (A.toNat + code.length))
    (hc2 : Apart (tc + (idx <<< 3) + 0x80#64).toNat 8 A.toNat (A.toNat + code.length))
    (hc3 : Apart (tc + (idx <<< 1)).toNat 2 A.toNat (A.toNat + code.length)) :
    ∃ m', Reaches Str9Fs.step m m' ∧
      m'.core.rip = A + BitVec.ofNat 64 (o + 51) + jr.signExtend 64 ∧
      (∀ r, r ≠ .rcx → r ≠ .rdx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ Loaded m'.memory A code ∧
      ∃ m1 m2 m3, storeN m.memory (q + 0x18#64) 8 key = some m1 ∧
        storeN m1 (q + 0x10#64) 8 (((q + 0x10#64) >>> 12) ^^^ h) = some m2 ∧
        storeN m2 (tc + (idx <<< 3) + 0x80#64) 8 (q + 0x10#64) = some m3 ∧
        storeN m3 (tc + (idx <<< 1)) 2 ((cnt.setWidth 32 + 1#32).setWidth 64) = some m'.memory := by
  have hN : code.length = code.length := rfl
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsi hr10 hr8 hrax hrcx hkey hent hw0 hw1 hw2 hw3 ⊢
  have hf := hs.fit
  have e18 : (0x18#32).signExtend 64 = 0x18#64 := by decide
  have e10 : (0x10#32).signExtend 64 = 0x10#64 := by decide
  have e80 : (0x80#32).signExtend 64 = 0x80#64 := by decide
  have e01 : (0x01#8).signExtend 32 = 1#32 := by decide
  obtain ⟨mem1, h1, -⟩ := Silmaril.X86.Ext.storeN_isSome (v := key) hw0
  obtain ⟨mem2, h2, -⟩ := Silmaril.X86.Ext.storeN_isSome (v := ((q + 0x10#64) >>> 12) ^^^ h)
    (perm_store h1 hw1)
  obtain ⟨mem3, h3, -⟩ := Silmaril.X86.Ext.storeN_isSome (v := q + 0x10#64)
    (perm_store h2 (perm_store h1 hw2))
  obtain ⟨mem4, h4, -⟩ := Silmaril.X86.Ext.storeN_isSome (v := (cnt.setWidth 32 + 1#32).setWidth 64)
    (perm_store h3 (perm_store h2 (perm_store h1 hw3)))
  have hl1 := loadedC_store hN hl h1 hc0
  have hl2 := loadedC_store hN hl1 h2 hc1
  have hl3 := loadedC_store hN hl2 h3 hc2
  have hl4 := loadedC_store hN hl3 h4 hc3
  have hent1 := ld_store h1 hke hent
  refine ex_head (stepC hN (o := o) (l := 7) hl hrip (by omega) hs.i0
    (e_loadrip (v := key) (by simpa [hrip, rip_add] using hkey))) ?_
  refine ex_fC hN hl (o := o + 7) (l := 3) (by simp [hrip, rip_add]) (by omega) hs.i7
    (e_aluI8r32 (op := .add) (by decide)) (fun f1 => ?_)
  refine ex_head (stepC hN (o := o + 10) (l := 4) hl (by simp [hrip, rip_add]) (by omega) hs.i10
    (e_storeqd (mem' := mem1) (by simpa [hrsi, e18] using h1))) ?_
  refine ex_head (stepC hN (o := o + 14) (l := 3) hl1 (by simp [hrip, rip_add]) (by omega) hs.i14
    e_movrr) ?_
  refine ex_fC hN hl1 (o := o + 17) (l := 4) (by simp [hrip, rip_add]) (by omega) hs.i17
    e_shr (fun f2 => ?_)
  refine ex_fC hN hl1 (o := o + 21) (l := 8) (by simp [hrip, rip_add]) (by omega) hs.i21
    (e_xoridx8d (v := h) (by simpa [hr8, hrax, e80] using hent1)) (fun f3 => ?_)
  refine ex_head (stepC hN (o := o + 29) (l := 4) hl1 (by simp [hrip, rip_add]) (by omega) hs.i29
    (e_storeqd (mem' := mem2) (by simpa [hrsi, hr10, e10] using h2))) ?_
  refine ex_head (stepC hN (o := o + 33) (l := 8) hl2 (by simp [hrip, rip_add]) (by omega) hs.i33
    (e_storeidx8d (mem' := mem3) (by simpa [hr8, hrax, hr10, e80] using h3))) ?_
  refine ex_head (stepC hN (o := o + 41) (l := 5) hl3 (by simp [hrip, rip_add]) (by omega) hs.i41
    (e_storew (mem' := mem4) (by
      simpa [hr8, hrax, hrcx, Silmaril.X86.Ext.AluOp.resultN, e01] using h4))) ?_
  refine ex_head (stepC hN (o := o + 46) (l := 5) hl4 (by simp [hrip, rip_add]) (by omega) hs.i46
    e_jmp) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, rfl, hl4, mem1, mem2, mem3, h1, h2, h3, h4⟩
  · simp [hrip, rip_add]
  · intro r a b; simp [a, b]

end Silmaril.Libc.Ptmalloc.X86sim

module

public import Silmaril.Apps.Sha256sum.TV.HexBody

/-! # The inlined `out_putc` append, once for every site

Status: **VERIFIED** (no `sorry`, standard axioms only).

Every inlined `out_putc(c)` of `sha256sum-min` ends with the same three instructions

```
lea  1(%OL),%N              -- N = olen + 1
mov  %SRC8,obuf(%OL)        -- obuf[olen] = c
mov  %N,olen(%rip)          -- olen = N
```

for some registers `OL` (holding `olen`), `N`, `SRC`. `run_append` executes them at **any**
listed address, for any choice of the three registers: the output layer goes from
`Obuf buf` to `Obuf (buf ++ [c])`, `N` holds the new length, the other registers are kept and
only the output layer is written (`ObufFoot`). The per-site translation validation only adds
the site's own tests around it (`TV.Suffix`, `TV.HexPutc`).

The full-buffer branch of a site is dead in this segment: the coupling has `Coalesced`, so the
buffer is never longer than the IR output, which `TVIR.Sim` bounds by the final output `F`
(68 bytes): `buf_lt`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Apps.Sha256sum.TV

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Apps.Sha256sum.Stdout
open Silmaril.X86 (State Reg)
open Silmaril.X86.TVIR
open Silmaril.Process (Memory Byte)
open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev stdinRead out)

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

set_option maxRecDepth 200000

/-- The bytes an append writes: `olen` and `obuf`. -/
def ObufFoot (a : Nat) : Prop := (0x412130 ≤ a ∧ a < 0x412138) ∨ (0x412140 ≤ a ∧ a < 0x412140 + 4096)

/-- After an append: `Obuf buf'`, `N = |buf'|`, the other registers kept, only the output layer
written. -/
structure Appended (s : XState) (pc : X86.Word) (N : Reg) (buf' : Bytes) (t : XState) : Prop where
  faulted : t.faulted = false
  code : Lift.Code t.memory
  rip : t.core.rip = pc
  obuf : Obuf t.memory buf'
  rN : t.core.read N = BitVec.ofNat 64 buf'.length
  regs : ∀ r, r ≠ N → t.core.read r = s.core.read r
  foot : Memory.WritesWithin s.memory t.memory ObufFoot

/-- **The append of an inlined `out_putc`** at any listed address `a` (see the module
docstring). -/
theorem run_append {s : XState} (hf : s.faulted = false) (hc : Lift.Code s.memory) {a : Nat}
    {OL N SRC : Reg} {disp : BitVec 32} {buf : Bytes}
    (hl1 : Lift.instrAt a = some (.base (.lea .q N (X86.Ext.Mem.ofReg OL none 1#32)), 4))
    (hl2 : Lift.instrAt (a + 4) =
      some (.base (.store .b (.mem (X86.Ext.Mem.ofReg OL none 0x00412140#32)) SRC), 7))
    (hl3 : Lift.instrAt (a + 11) = some (.base (.mov .q (.mem (X86.Ext.Mem.ofRip disp)) N), 7))
    (hdisp : BitVec.ofNat 64 (a + 18) + disp.signExtend 64 = 0x412130#64)
    (hNOL : N ≠ OL) (hSN : SRC ≠ N)
    (hrip : s.core.rip = BitVec.ofNat 64 a) (hOL : s.core.read OL = BitVec.ofNat 64 buf.length)
    (hob : Obuf s.memory buf) (hlt : buf.length < 4096) :
    RunsTo (Appended s (BitVec.ofNat 64 (a + 18)) N (buf ++ [lowByte (s.core.read SRC)])) s := by
  have hl : buf.length % 18446744073709551616 = buf.length := Nat.mod_eq_of_lt (by omega)
  -- lea
  refine run_instr' hf hc hrip hl1 ?_
  simp only [X86.Ext8.exec, X86.Ext.exec, X86.Ext.retire, X86.Ext.Mem.addr, X86.Ext.Mem.ofReg,
    X86.Ext.Base.value_reg, X86.Ext.Index.value, Option.map_none, Option.getD_none,
    BitVec.add_zero, hOL, hrip, X86.Ext.Sz.write, BitVec.reduceSignExtend, X86.Ext.Sz.bits,
    BitVec.setWidth_eq]
  intro hc1
  -- the byte store
  have hp1 : s.memory.Permitted .write (0x412140 + buf.length) 1 :=
    X86.Ext.Memory.Permitted.sub hob.obufW (by omega) (by omega) (by omega)
  obtain ⟨m1, hw1⟩ : ∃ m', s.memory.writeBytes (0x412140 + buf.length)
      (X86.Ext.leBytes (((s.core.read SRC).setWidth 8).setWidth 64) 1) = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by rw [X86.Ext.length_leBytes]; exact hp1))
  refine run_instr' hf hc1 (addr := a + 4) ?_ hl2 ?_
  · show BitVec.ofNat 64 a + BitVec.ofNat 64 4 = _
    rw [BitVec.ofNat_add_ofNat]
  rw [exec_store_b_ok' (m' := m1) ?_]
  swap
  · simp only [State.read_write_other _ _ _ _ hNOL.symm, State.read_write_other _ _ _ _ hSN,
      Lift.read_mk, Lift.core_regs, hOL]
    convert hw1 using 2
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    show (buf.length % 2 ^ 64 + 0x412140) % 2 ^ 64 = _
    omega
  dsimp only
  intro hc2
  -- the olen store
  have holW1 : m1.Permitted .write 0x412130 8 := perm_wb hw1 hob.olenW
  obtain ⟨m2, hw2⟩ : ∃ m', m1.writeBytes 0x412130
      (X86.Ext.leBytes (BitVec.ofNat 64 buf.length + 1#64) 8) = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by rw [X86.Ext.length_leBytes]; exact holW1))
  refine run_instr' hf hc2 (addr := a + 11) ?_ hl3 ?_
  · show BitVec.ofNat 64 a + BitVec.ofNat 64 4 + BitVec.ofNat 64 7 = _
    rw [BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  have hrip3 : BitVec.ofNat 64 a + BitVec.ofNat 64 4 + BitVec.ofNat 64 7 + BitVec.ofNat 64 7 =
      BitVec.ofNat 64 (a + 18) := by
    rw [BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  simp only [X86.Ext8.exec, X86.Ext.exec, X86.Ext.retire, X86.Ext.writeRM,
    X86.Ext.Sz.read, X86.Ext.Mem.addr, X86.Ext.Mem.ofRip, X86.Ext.Base.value_rip,
    X86.Ext.Index.value, Option.map_none, Option.getD_none, BitVec.add_zero, X86.Ext.storeN,
    X86.Ext.Sz.bytes, State.read_write_same, hrip3, hdisp, BitVec.toNat_ofNat, Nat.reduceMod,
    Nat.reducePow, X86.Ext.Sz.bits, BitVec.setWidth_eq,
    hw2, Option.map_some, Lift.read_mk, Lift.core_regs]
  intro hc3
  -- the result
  have hlen : (buf ++ [lowByte (s.core.read SRC)]).length = buf.length + 1 := by simp
  have hv : BitVec.ofNat 64 buf.length + 1#64 =
      BitVec.ofNat 64 (buf ++ [lowByte (s.core.read SRC)]).length := by
    rw [hlen, BitVec.ofNat_add]
  have holR : s.memory.Permitted .read 0x412130 8 := Memory.readWith_permitted hob.olen
  have hp1r : s.memory.Permitted .read (0x412140 + buf.length) 1 :=
    X86.Ext.Memory.Permitted.sub hob.obufR (by omega) (by omega) (by omega)
  rw [leBytes_lowByte] at hw1
  have hrd1 := read_snoc hob.obuf hw1 hp1r
  refine RunsTo.done ⟨hf, hc3, ?_, ⟨by rw [hlen]; omega, ?_, ?_, ?_,
    perm_wb hw2 (perm_wb hw1 hob.olenW), perm_wb hw2 (perm_wb hw1 hob.obufW),
    perm_wb hw2 (perm_wb hw1 hob.obufR)⟩, ?_, fun r hr => ?_, ?_⟩
  · rfl
  · rw [← hv]
    exact rd_same' hw2 (by simp) (perm_wb hw1 holR)
  · rw [Lift.readWith_wb_disjoint hw2 (Or.inr (by simp)), hlen, List.map_append]
    exact hrd1
  · rw [Lift.readWith_wb_disjoint hw2 (Or.inl (by simp)),
      Lift.readWith_wb_disjoint hw1 (Or.inl (by simp; omega))]
    exact hob.outError
  · simp only [Lift.read_mk, Lift.core_regs, State.read_write_same]
    exact hv
  · simp only [Lift.read_mk, Lift.core_regs, State.read_write_other _ _ _ _ hr]
  · refine ww_store hw2 (ww_store hw1 (Memory.WritesWithin.refl _ _) ?_) ?_
    · intro x h1 h2; (try simp only [List.length_cons, List.length_nil] at h2); simp only [ObufFoot]; omega
    · intro x h1 h2; (try simp only [X86.Ext.length_leBytes] at h2); simp only [ObufFoot]; omega

/-! ## The output layer of the IR -/

/-- `putcBuf` of a byte that is not a newline, into a buffer that is not full. -/
theorem putcBuf_plain {buf : Bytes} {b : UInt8} (hlt : buf.length < 4096) (hb : b ≠ 10) :
    (IOLayer.putcBuf 4096 buf b).2 = buf ++ [b] := by
  simp [IOLayer.putcBuf, show buf.length ≠ 4096 by omega, hb]

/-- `putcBuf` of a newline into a buffer that is not full: everything goes out. -/
theorem putcBuf_nl {buf : Bytes} (hlt : buf.length < 4096) :
    IOLayer.putcBuf 4096 buf 10 = (buf ++ [10], []) := by
  simp [IOLayer.putcBuf, show buf.length ≠ 4096 by omega]

/-- **The full-buffer branch is dead**: with the history coalesced, the buffer is never longer
than the IR output, which stays a prefix of the final output `F`. -/
theorem buf_lt {c : Ctx} {io : Bytes × Bytes} {g : GS} {h : List Ev} (hc : Common c io g h)
    {F : List UInt8} {b : UInt8} (hF : io.2 ++ [b] <+: F) (hF68 : F.length ≤ 68) :
    io.1.length + 1 ≤ 68 := by
  have h1 := congrArg List.length hc.coal
  simp only [List.length_append, List.length_map] at h1
  have h2 := hF.length_le
  simp only [List.length_append, List.length_singleton] at h2
  omega

/-- `Common` after an append (`run_append`) that kept `rsp`. -/
theorem Common.append {c : Ctx} {io : Bytes × Bytes} {g : GS} {h : List Ev} (hc : Common c io g h)
    {t : XState} {pc : X86.Word} {N : Reg} {b : UInt8} (ht : Appended g.x pc N (io.1 ++ [b]) t)
    (hN : N ≠ .rsp) : Common c (io.1 ++ [b], io.2 ++ [b]) { g with x := t } h := by
  refine ⟨hc.exited, ht.faulted, hc.k, ht.code, hc.okh, hc.read, ?_, ht.obuf, ?_, ?_⟩
  · rw [ht.regs .rsp hN.symm]; exact hc.rsp
  · have := hc.coal
    simp only [Coalesced, List.map_append] at this ⊢
    rw [← List.append_assoc, this]
  · exact hc.foot.trans (ht.foot.mono fun a ha => by
      simp only [ObufFoot] at ha; simp only [Foot]; omega)

end Silmaril.Apps.Sha256sum.TV

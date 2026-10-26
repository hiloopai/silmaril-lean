module

public import Silmaril.Apps.Sha256sum.Stdout.HexHi
public import Silmaril.X86.Stencils.HexLoop
public import Silmaril.X86.SegVC.Ext8

/-! # The hex output loop of `sha256sum-min` (`output_file`, inlined in `cmain`)

```
404541: mov olen,%rax ; lea 0x70(%rsp),%r15 ; mov %ebx,0x18(%rsp) ; mov %bpl,0x20(%rsp)
        mov %r15,%rbx ; jmp 4045ae
4045ae: movzbl (%rbx),%r15d ; mov %r15d,%edx ; shr $4,%dl ; and $0xf,%edx
        movzbl 0x4072c0(%rdx),%ebp                 -- hexd[digest[i] >> 4]
4045c2: out_putc(%bpl)        (site `hiSite`, exit 404578)
404578: and $0xf,%r15d ; movzbl 0x4072c0(%r15),%r15d   -- hexd[digest[i] & 0xf]
404584: out_putc(%r15b)       (site `loSite`, exit 4045a5)
4045a5: add $1,%rbx ; cmp %rbx,%r14 ; je 404605 ; (4045ae)
```

From `0x404541` (after `sha_final`: the 32 digest bytes `d` in `bin[]` at `rsp + 0x70`, `r14 =
rsp + 0x90`, the `hexd` table in `.rodata`) to `0x404605`, the loop appends `hexLower d` to
the output stream through 64 inlined `out_putc`s: the buffer becomes
`(putsBuf 4096 buf (hexLower d)).2` and the coalescing invariant `Coalesced h buf emitted`
becomes `Coalesced h' _ (emitted ++ hexLower d)`. Stated in `Leads` form over `GStep`, so it
composes with the segments before and after it (`Release.Open.format`).

The loop is an instance of the hex-loop stencil (`X86.Stencils.HexLoop.loop`, emit primitive
`Stdout.PutcSite`), with the two sites `hiSite_verified`/`loSite_verified`.

Pieces: `run_start` (`0x404541 → 0x4045ae`), `run_hi` (`0x4045ae → 0x4045c2`, the load and the
high-digit lookup), `run_lo` (`0x404578 → 0x404584`), `run_next` (`0x4045a5 →` head or exit),
`body` (one iteration as a stencil step: `run_hi`, `hiSite_verified`, `run_lo`,
`loSite_verified`, `run_next`), `hex_loop` (`X86.Stencils.HexLoop.loop` over `Inv`).

Status: **VERIFIED** (no `sorry`, standard axioms only; `hex_loop` has no hypotheses beyond its
entry conditions: the two sites and the `out_flush` contract are proved, `Stdout.HexHi`,
`Stdout.HexLo`).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.X86 (Word)
open Silmaril.Process (Memory Byte)
open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev out stdinRead expected)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)
open Silmaril.X86.Stencils.HexLoop (hexTable hexPair)
open Silmaril.X86 (State Reg)

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

set_option maxRecDepth 200000

/-! ## Instruction forms -/

/-- A zero-extending byte load `movzbl disp(%base),%dst32` from readable memory retires. -/
theorem exec_movzb_ok {c : State} {mem : Memory} {len : Nat} {dst base : Reg} {d : BitVec 32}
    {b : Byte} (h : mem.readWith .read (c.read base + d.signExtend 64).toNat 1 = some [b]) :
    X86.Ext8.exec (.base (.movx false .d .b dst (.mem (X86.Ext.Mem.ofReg base none d)))) c mem len =
      .ok { (c.write dst (b.setWidth 64)) with rip := c.rip + BitVec.ofNat 64 len } mem := by
  simp only [X86.Ext8.exec_base, X86.Ext.exec, X86.Ext.readNarrow, X86.Ext.loadN,
    X86.Ext.Mem.addr, X86.Ext.Mem.ofReg]
  change X86.Ext.retire _ (Option.map _ (Option.map _ (Option.map _
    (mem.readBytes (c.read base + 0#64 + d.signExtend 64).toNat 1)))) = _
  rw [BitVec.add_zero, Memory.readBytes, h]
  simp only [X86.Ext.retire, X86.Ext.Sz.write, X86.Ext.leValue, Option.map_some]
  simp only [X86.Ext.Sz.bits, X86.Ext.Narrow.bits, Bool.false_eq_true, ite_false, Nat.mul_zero,
    Nat.add_zero]
  have e : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 b.toNat))) =
      BitVec.setWidth 64 b := by
    apply BitVec.eq_of_toNat_eq
    have := b.isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [e]

theorem toNat_ofU8 (b : UInt8) : (ofU8 b).toNat = b.toNat := by
  have := b.toNat_lt
  simp only [ofU8, BitVec.toNat_ofNat]
  omega

/-! ## Nibble and table facts (checked over all bytes) -/

theorem hi_nib_fin : ∀ n : Fin 256,
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.ofNat 8 n.val))) &&& ~~~255#64 |||
      BitVec.setWidth 64 (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.setWidth 64 (BitVec.ofNat 8 n.val)))) >>> 4)) &&& 15#32) =
      BitVec.ofNat 64 (n.val / 16) := by decide

theorem hi_nib (x : BitVec 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 x)) &&& ~~~255#64 |||
      BitVec.setWidth 64 (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.setWidth 64 x))) >>> 4)) &&& 15#32) =
      BitVec.ofNat 64 (x.toNat / 16) := by
  have := hi_nib_fin ⟨x.toNat, x.isLt⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using this

theorem lo_nib_fin : ∀ n : Fin 256,
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 8 n.val)) &&& 15#32) =
      BitVec.ofNat 64 (n.val % 16) := by decide

theorem lo_nib (x : BitVec 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 x) &&& 15#32) =
      BitVec.ofNat 64 (x.toNat % 16) := by
  have := lo_nib_fin ⟨x.toNat, x.isLt⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using this

theorem table_take : ∀ k : Fin 16,
    ((hexTable.map ofU8).drop k.val).take 1 = [ofU8 (hexTable.getD k.val 0)] := by decide

theorem lowByte_table : ∀ k : Fin 16,
    lowByte (BitVec.setWidth 64 (ofU8 (hexTable.getD k.val 0))) =
      Silmaril.Apps.Sha256sum.hexDigit k.val := by decide

theorem table_read {m : Memory} (h : m.readWith .read 0x4072c0 16 = some (hexTable.map ofU8))
    {k : Nat} (hk : k < 16) :
    m.readWith .read (0x4072c0 + k) 1 = some [ofU8 (hexTable.getD k 0)] := by
  rw [Memory.readWith_sub_range h hk (by omega)]
  exact congrArg some (table_take ⟨k, hk⟩)

/-! ## The straight-line pieces -/

/-- The state at the high-digit site `0x4045c2`, from the loop head `t`. -/
structure AtHi (t : XState) (b : UInt8) (u : XState) : Prop where
  faulted : u.faulted = false
  code : Lift.Code u.memory
  rip : u.core.rip = 0x4045c2#64
  mem : u.memory = t.memory
  rsp : u.core.read .rsp = t.core.read .rsp
  rbx : u.core.read .rbx = t.core.read .rbx
  rax : u.core.read .rax = t.core.read .rax
  r12 : u.core.read .r12 = t.core.read .r12
  r13 : u.core.read .r13 = t.core.read .r13
  r14 : u.core.read .r14 = t.core.read .r14
  r15 : u.core.read .r15 = BitVec.setWidth 64 (ofU8 b)
  digit : lowByte (u.core.read .rbp) = Silmaril.Apps.Sha256sum.hexDigit (b.toNat / 16)

/-- `0x4045ae → 0x4045c2`: load `digest[i]`, look up its high digit. -/
theorem run_hi {t : XState} {b : UInt8} (hf : t.faulted = false) (hc : Lift.Code t.memory)
    (hrip : t.core.rip = 0x4045ae#64)
    (hd : t.memory.readWith .read (t.core.read .rbx).toNat 1 = some [ofU8 b])
    (htab : t.memory.readWith .read 0x4072c0 16 = some (hexTable.map ofU8)) :
    RunsTo (AtHi t b) t := by
  have hk : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
  refine run_instr' hf hc hrip (by rfl) ?_
  rw [exec_movzb_ok (b := ofU8 b) ?_]
  swap
  · simpa using hd
  intro hc1
  simp only [hrip, BitVec.reduceAdd]
  rstep
  rstep
  rstep
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  rw [exec_movzb_ok (b := ofU8 (hexTable.getD (b.toNat / 16) 0)) ?_]
  swap
  · simp only [State.read_write_same, Silmaril.X86.SegVC.bread_low,
      Silmaril.X86.SegVC.bwrite_low, X86.Ext.ShiftOp.result, X86.Ext.Count.raw,
      X86.Ext.writeByte, BitVec.reduceToNat, Nat.reduceMod, hi_nib, BitVec.reduceSignExtend]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, toNat_ofU8,
      show (b.toNat / 16 % 2 ^ 64 + 4223680 % 2 ^ 64) % 2 ^ 64 = 0x4072c0 + b.toNat / 16 by omega]
    exact table_read htab hk
  intro hc5
  refine RunsTo.done ⟨hf, hc5, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true, Lift.read_mk, Lift.core_regs, Silmaril.X86.SegVC.bwrite_low,
      X86.Ext.writeByte]
  exact lowByte_table ⟨_, hk⟩

/-- What the hex loop may write: the sites' footprint and the two spill slots
`0x18(%rsp)` (4 bytes) and `0x20(%rsp)` (1 byte). -/
def HexFoot (sp : Nat) (a : Nat) : Prop :=
  SiteFoot sp a ∨ (sp + 0x18 ≤ a ∧ a < sp + 0x1c) ∨ a = sp + 0x20

/-- The state at the low-digit site `0x404584`, from the high site's exit `t`. -/
structure AtLo (t : XState) (b : UInt8) (u : XState) : Prop where
  faulted : u.faulted = false
  code : Lift.Code u.memory
  rip : u.core.rip = 0x404584#64
  mem : u.memory = t.memory
  rsp : u.core.read .rsp = t.core.read .rsp
  rbx : u.core.read .rbx = t.core.read .rbx
  rdx : u.core.read .rdx = t.core.read .rdx
  r12 : u.core.read .r12 = t.core.read .r12
  r13 : u.core.read .r13 = t.core.read .r13
  r14 : u.core.read .r14 = t.core.read .r14
  digit : lowByte (u.core.read .r15) = Silmaril.Apps.Sha256sum.hexDigit (b.toNat % 16)

/-- `0x404578 → 0x404584`: look up the low digit of `digest[i]` (kept in `r15`). -/
theorem run_lo {t : XState} {b : UInt8} (hf : t.faulted = false) (hc : Lift.Code t.memory)
    (hrip : t.core.rip = 0x404578#64) (hr15 : t.core.read .r15 = BitVec.setWidth 64 (ofU8 b))
    (htab : t.memory.readWith .read 0x4072c0 16 = some (hexTable.map ofU8)) :
    RunsTo (AtLo t b) t := by
  have hk : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  rstep [hrip, hr15]
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  rw [exec_movzb_ok (b := ofU8 (hexTable.getD (b.toNat % 16) 0)) ?_]
  swap
  · simp only [State.read_write_same, lo_nib, BitVec.reduceSignExtend]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, toNat_ofU8,
      show (b.toNat % 16 % 2 ^ 64 + 4223680 % 2 ^ 64) % 2 ^ 64 = 0x4072c0 + b.toNat % 16 by omega]
    exact table_read htab hk
  intro hc2
  refine RunsTo.done ⟨hf, hc2, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true, Lift.read_mk, Lift.core_regs]
  exact lowByte_table ⟨_, hk⟩

/-- After the loop control `0x4045a5 → 0x4045ae / 0x404605` of iteration `i`. -/
structure AtNext (t : XState) (i : Nat) (u : XState) : Prop where
  faulted : u.faulted = false
  code : Lift.Code u.memory
  rip : u.core.rip = if i + 1 < 32 then 0x4045ae#64 else 0x404605#64
  mem : u.memory = t.memory
  rsp : u.core.read .rsp = t.core.read .rsp
  rax : u.core.read .rax = t.core.read .rax
  rbp : u.core.read .rbp = t.core.read .rbp
  r12 : u.core.read .r12 = t.core.read .r12
  r13 : u.core.read .r13 = t.core.read .r13
  r14 : u.core.read .r14 = t.core.read .r14
  rbx : u.core.read .rbx = t.core.read .rbx + 1#64

theorem next_eq_iff (X : Word) {i : Nat} (hi : i < 32) :
    (X + 0x90#64 = X + BitVec.ofNat 64 (0x70 + i) + 1#64) ↔ i + 1 = 32 := by
  rw [BitVec.add_assoc, BitVec.add_right_inj]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- `0x4045a5 → 0x4045ae / 0x404605`: `rbx + 1`, compare with `r14 = bin + 32`. -/
theorem run_next {t : XState} {i : Nat} {X : Word} (hf : t.faulted = false)
    (hc : Lift.Code t.memory) (hrip : t.core.rip = 0x4045a5#64)
    (hrbx : t.core.read .rbx = X + BitVec.ofNat 64 (0x70 + i)) (hr14 : t.core.read .r14 = X + 0x90#64)
    (hi : i < 32) : RunsTo (AtNext t i) t := by
  rstep [hrip, hrbx]
  rstep [hr14]
  have hiff := next_eq_iff X hi
  by_cases hlast : i + 1 = 32
  · have hb : ((X + 144#64) == (X + BitVec.ofNat 64 (112 + i) + 1#64)) = true := by
      simpa using hiff.mpr hlast
    rstep [X86.Ext.Cond.afterCmp, hb]
    refine RunsTo.done ⟨hf, by assumption, by simp [hlast], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true, Lift.read_mk, Lift.core_regs, hrbx]
  · have hb : ((X + 144#64) == (X + BitVec.ofNat 64 (112 + i) + 1#64)) = false := by
      simpa using mt hiff.mp hlast
    rstep [X86.Ext.Cond.afterCmp, hb]
    refine RunsTo.done ⟨hf, by assumption, by simp [show i + 1 < 32 by omega], rfl, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    all_goals simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true, Lift.read_mk, Lift.core_regs, hrbx]

/-- The entry `0x404541` of the hex loop. -/
structure HexEntry (s : XState) (d : Bytes) : Prop where
  len : d.length = 32
  sp : 0x414028 ≤ (s.core.read .rsp).toNat ∧ (s.core.read .rsp).toNat < 2 ^ 47
  /-- The stack: the `out_flush` frame below `rsp` up to the end of `bin[]`. -/
  stackR : s.memory.Permitted .read ((s.core.read .rsp).toNat - 40) (40 + 0x90)
  stackW : s.memory.Permitted .write ((s.core.read .rsp).toNat - 40) (40 + 0x90)
  r14 : s.core.read .r14 = s.core.read .rsp + 0x90#64
  digest : s.memory.readWith .read ((s.core.read .rsp).toNat + 0x70) 32 = some (d.map ofU8)
  table : s.memory.readWith .read 0x4072c0 16 = some (hexTable.map ofU8)

/-- The spill slots `0x18(%rsp)` (4 bytes) and `0x20(%rsp)`. -/
def SpillFoot (sp : Nat) (a : Nat) : Prop := (sp + 0x18 ≤ a ∧ a < sp + 0x1c) ∨ a = sp + 0x20

/-- After the setup `0x404541 → 0x4045ae` from `s`. -/
structure AtStart (s : XState) (buf : Bytes) (u : XState) : Prop where
  faulted : u.faulted = false
  code : Lift.Code u.memory
  rip : u.core.rip = 0x4045ae#64
  rsp : u.core.read .rsp = s.core.read .rsp
  rbp : u.core.read .rbp = s.core.read .rbp
  r12 : u.core.read .r12 = s.core.read .r12
  r13 : u.core.read .r13 = s.core.read .r13
  r14 : u.core.read .r14 = s.core.read .r14
  rax : u.core.read .rax = BitVec.ofNat 64 buf.length
  rbx : u.core.read .rbx = s.core.read .rsp + 0x70#64
  spillB : u.memory.readWith .read ((s.core.read .rsp).toNat + 0x18) 4 =
    some (X86.Ext.leBytes (((s.core.read .rbx).setWidth 32).setWidth 64) 4)
  spillP : u.memory.readWith .read ((s.core.read .rsp).toNat + 0x20) 1 =
    some (X86.Ext.leBytes (((s.core.read .rbp).setWidth 8).setWidth 64) 1)
  foot : Memory.WritesWithin s.memory u.memory (SpillFoot (s.core.read .rsp).toNat)

/-- `0x404541 → 0x4045ae`: load `olen`, point `rbx` at `bin[]`, spill `ebx` and `bpl`. -/
theorem run_start {s : XState} {buf d : Bytes} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x404541#64) (hob : Obuf s.memory buf) (hE : HexEntry s d) :
    RunsTo (AtStart s buf) s := by
  have holen := hob.olen
  have hcap := hob.cap
  have hl : buf.length % 18446744073709551616 = buf.length := Nat.mod_eq_of_lt (by omega)
  rstep [hrip, hl]
  rstep
  have hsp := hE.sp
  have hW := hE.stackW
  have hsp8 : (s.core.read .rsp).toNat - 40 + (40 + 0x90) < 2 ^ 64 := by omega
  obtain ⟨m1, hw1⟩ : ∃ m', s.memory.writeBytes ((s.core.read .rsp).toNat + 0x18)
      (X86.Ext.leBytes (BitVec.setWidth 64 (BitVec.setWidth 32 (s.core.read .rbx))) 4) = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by
      rw [X86.Ext.length_leBytes]
      exact X86.Ext.Memory.Permitted.sub hW (by omega) (by omega) (by omega)))
  have ha1 : (s.core.read .rsp + 24#64).toNat = (s.core.read .rsp).toNat + 0x18 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  x86_simp [ha1, hw1]
  intro hc3
  obtain ⟨m2, hw2⟩ : ∃ m', m1.writeBytes ((s.core.read .rsp).toNat + 0x20)
      (X86.Ext.leBytes (((s.core.read .rbp).setWidth 8).setWidth 64) 1) = some m' :=
    Option.ne_none_iff_exists'.mp (writeBytes_ne_none (by
      rw [X86.Ext.length_leBytes]
      exact perm_wb hw1 (X86.Ext.Memory.Permitted.sub hW (by omega) (by omega) (by omega))))
  refine run_instr' hf (by assumption) rfl (by rfl) ?_
  rw [exec_store_b_ok' (m' := m2) ?_]
  swap
  · simp only [State.read_write_other, ne_eq, reduceCtorEq, not_false_eq_true, Lift.read_mk,
      Lift.core_regs, BitVec.reduceSignExtend]
    convert hw2 using 2
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  dsimp only
  intro hc4
  rstep
  rstep
  have hR := hE.stackR
  refine RunsTo.done ⟨hf, by assumption, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
    not_false_eq_true, Lift.read_mk, Lift.core_regs]; done)
  · rw [Lift.readWith_wb_disjoint hw2 (Or.inl (by simp))]
    exact rd_same' hw1 (by simp) (X86.Ext.Memory.Permitted.sub hR (by omega) (by omega) (by omega))
  · exact rd_same' hw2 (by simp)
      (perm_wb hw1 (X86.Ext.Memory.Permitted.sub hR (by omega) (by omega) (by omega)))
  · xfoot [SpillFoot]

/-- The exit `0x404605`: `rsp`, `r12`–`r14` kept, the spills of `ebx`/`bpl` in place, and
memory changed only in `HexFoot`. -/
structure HexExit (s s' : XState) : Prop where
  rsp : s'.core.read .rsp = s.core.read .rsp
  r12 : s'.core.read .r12 = s.core.read .r12
  r13 : s'.core.read .r13 = s.core.read .r13
  r14 : s'.core.read .r14 = s.core.read .r14
  spillB : s'.memory.readWith .read ((s.core.read .rsp).toNat + 0x18) 4 =
    some (X86.Ext.leBytes (((s.core.read .rbx).setWidth 32).setWidth 64) 4)
  spillP : s'.memory.readWith .read ((s.core.read .rsp).toNat + 0x20) 1 =
    some (X86.Ext.leBytes (((s.core.read .rbp).setWidth 8).setWidth 64) 1)
  foot : Memory.WritesWithin s.memory s'.memory (HexFoot (s.core.read .rsp).toNat)

/-! ## Bookkeeping -/

theorem putsBuf_append_snd (cap : Nat) (b xs ys : Bytes) :
    (Sys.IOLayer.putsBuf cap b (xs ++ ys)).2 =
      (Sys.IOLayer.putsBuf cap (Sys.IOLayer.putsBuf cap b xs).2 ys).2 := by
  induction xs generalizing b with
  | nil => rfl
  | cons c cs ih => simp only [List.cons_append, Sys.IOLayer.putsBuf]; exact ih _

theorem putsBuf_pair (cap : Nat) (b : Bytes) (c1 c2 : UInt8) :
    (Sys.IOLayer.putsBuf cap b [c1, c2]).2 =
      (Sys.IOLayer.putcBuf cap (Sys.IOLayer.putcBuf cap b c1).2 c2).2 := rfl

theorem hexDigit_ne_nl : ∀ k : Fin 16, Silmaril.Apps.Sha256sum.hexDigit k.val ≠ 10 := by decide

theorem hexLower_take_prefix (d : Bytes) (j : Nat) : hexLower (d.take j) <+: hexLower d :=
  ⟨hexLower (d.drop j), by
    rw [← Silmaril.X86.Stencils.HexLoop.hexLower_append, List.take_append_drop]⟩

theorem map_drop_take_one {α β : Type} (f : α → β) (l : List α) (i : Nat) (hi : i < l.length) :
    ((l.map f).drop i).take 1 = [f l[i]] := by
  rw [List.drop_eq_getElem_cons (by simpa using hi)]
  simp

/-- The buffer after the first `i` bytes' digits. -/
def Bof (buf0 d : Bytes) (i : Nat) : Bytes :=
  (Sys.IOLayer.putsBuf 4096 buf0 (hexLower (d.take i))).2

theorem Bof_succ (buf0 d : Bytes) (i : Nat) (hi : i < d.length) :
    Bof buf0 d (i + 1) = (Sys.IOLayer.putcBuf 4096 (Sys.IOLayer.putcBuf 4096 (Bof buf0 d i)
      (Silmaril.Apps.Sha256sum.hexDigit (d[i].toNat / 16))).2
      (Silmaril.Apps.Sha256sum.hexDigit (d[i].toNat % 16))).2 := by
  unfold Bof
  rw [Silmaril.X86.Stencils.HexLoop.hexLower_take_succ d i hi, putsBuf_append_snd]
  rfl

theorem notSite_of_spill {sp a : Nat} (hsp : 0x414028 ≤ sp) (h : SpillFoot sp a) :
    ¬ SiteFoot sp a := by
  unfold SpillFoot at h; unfold SiteFoot; omega

/-- `Obuf` survives writes outside `out_error`, `olen` and `obuf`. -/
theorem obuf_keep {m m' : Memory} {buf : Bytes} {F : Nat → Prop} (hob : Obuf m buf)
    (hw : Memory.WritesWithin m m' F) (hF : ∀ a, F a → a < 0x41212c ∨ 0x413140 ≤ a) :
    Obuf m' buf := by
  have hcap := hob.cap
  refine ⟨hcap, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw.readWith fun o ho hf => by have := hF _ hf; omega]; exact hob.olen
  · rw [hw.readWith fun o ho hf => by have := hF _ hf; omega]; exact hob.obuf
  · rw [hw.readWith fun o ho hf => by have := hF _ hf; omega]; exact hob.outError
  · exact (hw.permitted_iff _ _ _).mpr hob.olenW
  · exact (hw.permitted_iff _ _ _).mpr hob.obufW
  · exact (hw.permitted_iff _ _ _).mpr hob.obufR

/-- The loop state at iteration `i`: the head `0x4045ae` for `i < 32`, the exit `0x404605` for
`i = 32`. -/
structure HexAt (s0 : XState) (i : Nat) (buf : Bytes) (t : XState) : Prop where
  faulted : t.faulted = false
  code : Lift.Code t.memory
  rip : t.core.rip = if i < 32 then 0x4045ae#64 else 0x404605#64
  rsp : t.core.read .rsp = s0.core.read .rsp
  rbx : i < 32 → t.core.read .rbx = s0.core.read .rsp + BitVec.ofNat 64 (0x70 + i)
  rax : t.core.read .rax = BitVec.ofNat 64 buf.length
  r12 : t.core.read .r12 = s0.core.read .r12
  r13 : t.core.read .r13 = s0.core.read .r13
  r14 : t.core.read .r14 = s0.core.read .r14
  obuf : Obuf t.memory buf
  spillB : t.memory.readWith .read ((s0.core.read .rsp).toNat + 0x18) 4 =
    some (X86.Ext.leBytes (((s0.core.read .rbx).setWidth 32).setWidth 64) 4)
  spillP : t.memory.readWith .read ((s0.core.read .rsp).toNat + 0x20) 1 =
    some (X86.Ext.leBytes (((s0.core.read .rbp).setWidth 8).setWidth 64) 1)
  foot : Memory.WritesWithin s0.memory t.memory (HexFoot (s0.core.read .rsp).toNat)

section Leads

open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev out stdinRead expected)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)
open Silmaril.X86.Stencils.HexLoop (Triple)

theorem ok_with {message : List Byte} {g : GS} {h : List Ev} {t : XState}
    (hok : Ok message g h) (hf : t.faulted = false) : Ok message { g with x := t } h :=
  ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hf⟩

/-- The loop invariant of the stencil (`X86.Stencils.HexLoop.loop`), over `GS × List Ev`. -/
def Inv (message : List Byte) (g0 : GS) (h0 : List Ev) (buf0 emitted0 d : Bytes) (i : Nat)
    (e : Bytes) (p : GS × List Ev) : Prop :=
  e = emitted0 ++ hexLower (d.take i) ∧ p.1.k = g0.k ∧ stdinRead p.2 = stdinRead h0 ∧
    Ok message p.1 p.2 ∧ Coalesced p.2 (Bof buf0 d i) e ∧ HexAt g0.x i (Bof buf0 d i) p.1.x

/-- **One iteration** of the hex loop (two inlined `out_putc`s), as a stencil step. -/
theorem body {w : World} {message : List Byte} {K : GS → List Ev → Prop} {g0 : GS}
    {h0 : List Ev} {buf0 emitted0 d : Bytes}
    (hfull : w.stdoutFull = false) (hfd : g0.k.fds 1 = some .stdout)
    (hrd0 : stdinRead h0 = message) (hE : HexEntry g0.x d)
    (hpre : (emitted0 ++ hexLower d).map UInt8.toBitVec <+: expected message)
    (i : Nat) (hi : i < 32) (e : Bytes) :
    Triple (fun p : GS × List Ev => Leads (GStep w) (Ok message) K p.1 p.2)
      (Inv message g0 h0 buf0 emitted0 d i e)
      (Inv message g0 h0 buf0 emitted0 d (i + 1)
        (e ++ hexPair (d[i]'(by rw [hE.len]; exact hi)))) := by
  intro p hInv k
  obtain ⟨he, hk, hrd', hok, hco, hL⟩ := hInv
  have hlen := hE.len
  have hsp := hE.sp
  have hdi : i < d.length := by omega
  have hsp0 : (g0.x.core.read .rsp).toNat + 0x90 < 2 ^ 64 := by omega
  have hb16 : d[i].toNat / 16 < 16 := by have := d[i].toNat_lt; omega
  have hb16' : d[i].toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  -- the two digits and the prefixes
  have hpair : emitted0 ++ hexLower (d.take (i + 1)) =
      e ++ [Silmaril.Apps.Sha256sum.hexDigit (d[i].toNat / 16),
        Silmaril.Apps.Sha256sum.hexDigit (d[i].toNat % 16)] := by
    rw [Silmaril.X86.Stencils.HexLoop.hexLower_take_succ d i hdi, he, List.append_assoc]; rfl
  have hpref : ∀ y, y <+: emitted0 ++ hexLower (d.take (i + 1)) →
      y.map UInt8.toBitVec <+: expected message := fun y hy =>
    ((hy.trans ((List.prefix_append_right_inj emitted0).mpr
      (hexLower_take_prefix d (i + 1)))).map _).trans hpre
  -- the loop head
  have hrip : p.1.x.core.rip = 0x4045ae#64 := by simpa [hi] using hL.rip
  have hrbx := hL.rbx hi
  have hrax := hL.rax
  have hdig : p.1.x.memory.readWith .read (p.1.x.core.read .rbx).toNat 1 = some [ofU8 d[i]] := by
    rw [hrbx, show (g0.x.core.read .rsp + BitVec.ofNat 64 (0x70 + i)).toNat =
      (g0.x.core.read .rsp).toNat + 0x70 + i by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
    rw [hL.foot.readWith (fun o ho hf => by unfold HexFoot SiteFoot at hf; omega),
      Memory.readWith_sub_range hE.digest (offset := i) (len := 1) hi (by omega)]
    exact congrArg some (map_drop_take_one ofU8 d i hdi)
  have htab : p.1.x.memory.readWith .read 0x4072c0 16 = some (hexTable.map ofU8) := by
    rw [hL.foot.readWith (fun o ho hf => by unfold HexFoot SiteFoot at hf; omega)]
    exact hE.table
  have hR : g0.x.memory.Permitted .read ((g0.x.core.read .rsp).toNat - 40) 40 :=
    X86.Ext.Memory.Permitted.sub hE.stackR (by omega) (by omega) (by omega)
  have hW : g0.x.memory.Permitted .write ((g0.x.core.read .rsp).toNat - 40) 40 :=
    X86.Ext.Memory.Permitted.sub hE.stackW (by omega) (by omega) (by omega)
  refine (run_hi hL.faulted hL.code hrip hdig htab).leads hok.1 hok fun u hu => ?_
  have hum : Memory.WritesWithin g0.x.memory u.memory (HexFoot (g0.x.core.read .rsp).toNat) := by
    rw [hu.mem]; exact hL.foot
  have husp : u.core.read .rsp = g0.x.core.read .rsp := hu.rsp.trans hL.rsp
  -- the high digit
  refine hiSite_verified w message K { p.1 with x := u } p.2 (Bof buf0 d i) e hfull
    (by rw [show ({ p.1 with x := u } : GS).k = g0.k from hk]; exact hfd) hu.rip hu.code
    (by rw [hu.mem]; exact hL.obuf)
    ⟨by rw [hu.rax, hrax], by rw [hu.digit]; exact hexDigit_ne_nl ⟨_, hb16⟩,
      ⟨by rw [husp]; omega, by rw [husp]; exact (hum.permitted_iff _ _ _).mpr hR,
        by rw [husp]; exact (hum.permitted_iff _ _ _).mpr hW⟩⟩
    hco (ok_with hok hu.faulted) (by rw [hrd', hrd0])
    (by
      show List.map UInt8.toBitVec (e ++ [lowByte (u.core.read .rbp)]) <+: expected message
      rw [hu.digit]; exact hpref _ (by rw [hpair]; exact ⟨[Silmaril.Apps.Sha256sum.hexDigit (d[i].toNat % 16)], by simp⟩)) ?_
  intro g1 h1 r1 f1 ex1 k1 x1 o1 co1 rd1 ok1 post1
  simp only [hu.digit] at o1 co1 post1
  obtain ⟨kp1, rdx1⟩ := post1
  have h1m : Memory.WritesWithin g0.x.memory g1.x.memory (HexFoot (g0.x.core.read .rsp).toNat) :=
    hum.trans (by rw [← husp]; exact kp1.foot.mono fun _ ha => Or.inl ha)
  have h1sp : g1.x.core.read .rsp = g0.x.core.read .rsp := kp1.rsp.trans husp
  have htab1 : g1.x.memory.readWith .read 0x4072c0 16 = some (hexTable.map ofU8) := by
    rw [h1m.readWith (fun o ho hf => by unfold HexFoot SiteFoot at hf; omega)]
    exact hE.table
  -- the low digit
  refine (run_lo (b := d[i]) f1 x1 r1 (kp1.r15.trans hu.r15) htab1).leads ok1.1 ok1 fun v hv => ?_
  have hvm : Memory.WritesWithin g0.x.memory v.memory (HexFoot (g0.x.core.read .rsp).toNat) := by
    rw [hv.mem]; exact h1m
  have hvsp : v.core.read .rsp = g0.x.core.read .rsp := hv.rsp.trans h1sp
  refine loSite_verified w message K { g1 with x := v } h1 _ _ hfull
    (by rw [show ({ g1 with x := v } : GS).k = g0.k from k1.trans hk]; exact hfd) hv.rip hv.code
    (by rw [hv.mem]; exact o1)
    ⟨by rw [hv.rdx, rdx1], by rw [hv.digit]; exact hexDigit_ne_nl ⟨_, hb16'⟩,
      ⟨by rw [hvsp]; omega, by rw [hvsp]; exact (hvm.permitted_iff _ _ _).mpr hR,
        by rw [hvsp]; exact (hvm.permitted_iff _ _ _).mpr hW⟩⟩
    co1 (ok_with ok1 hv.faulted) (by rw [rd1, hrd', hrd0])
    (by
      show List.map UInt8.toBitVec (e ++ [Silmaril.Apps.Sha256sum.hexDigit (d[i].toNat / 16)] ++
        [lowByte (v.core.read .r15)]) <+: expected message
      rw [hv.digit]; exact hpref _ (by rw [hpair]; exact ⟨[], by simp⟩)) ?_
  intro g2 h2 r2 f2 ex2 k2 x2 o2 co2 rd2 ok2 post2
  simp only [hv.digit] at o2 co2 post2
  obtain ⟨kp2, rax2⟩ := post2
  have h2m : Memory.WritesWithin g0.x.memory g2.x.memory (HexFoot (g0.x.core.read .rsp).toNat) :=
    hvm.trans (by rw [← hvsp]; exact kp2.foot.mono fun _ ha => Or.inl ha)
  have h2sp : g2.x.core.read .rsp = g0.x.core.read .rsp := kp2.rsp.trans hvsp
  have h2rbx : g2.x.core.read .rbx = g0.x.core.read .rsp + BitVec.ofNat 64 (0x70 + i) :=
    kp2.rbx.trans (hv.rbx.trans (kp1.rbx.trans (hu.rbx.trans hrbx)))
  have h2r14 : g2.x.core.read .r14 = g0.x.core.read .rsp + 0x90#64 :=
    kp2.r14.trans (hv.r14.trans (kp1.r14.trans (hu.r14.trans (hL.r14.trans hE.r14))))
  -- the loop control
  refine (run_next (X := g0.x.core.read .rsp) f2 x2 r2 h2rbx h2r14 hi).leads ok2.1 ok2
    fun y hy => ?_
  have hBs := Bof_succ buf0 d i hdi
  -- the spills survive the two sites
  have hspill : ∀ {m m' : Memory}, Memory.WritesWithin m m'
      (SiteFoot (g0.x.core.read .rsp).toNat) → ∀ {a n : Nat} {xs : List Byte},
      (∀ o < n, SpillFoot (g0.x.core.read .rsp).toNat (a + o)) →
      m.readWith .read a n = some xs → m'.readWith .read a n = some xs := by
    intro m m' hw a n xs hin hr
    rw [hw.readWith fun o ho => notSite_of_spill (by omega) (hin o ho)]; exact hr
  have hk1 : Memory.WritesWithin u.memory g1.x.memory (SiteFoot (g0.x.core.read .rsp).toNat) := by
    rw [← husp]; exact kp1.foot
  have hk2 : Memory.WritesWithin v.memory g2.x.memory (SiteFoot (g0.x.core.read .rsp).toNat) := by
    rw [← hvsp]; exact kp2.foot
  have hinB : ∀ o < 4, SpillFoot (g0.x.core.read .rsp).toNat ((g0.x.core.read .rsp).toNat + 0x18 + o) :=
    fun o ho => Or.inl ⟨by omega, by omega⟩
  have hinP : ∀ o < 1, SpillFoot (g0.x.core.read .rsp).toNat ((g0.x.core.read .rsp).toNat + 0x20 + o) :=
    fun o ho => Or.inr (by omega)
  refine k ⟨{ g2 with x := y }, h2⟩ ⟨by rw [hpair]; rfl, k2.trans (k1.trans hk),
    rd2.trans (rd1.trans hrd'), ok_with ok2 hy.faulted,
    by rw [hBs]; simp only [List.append_assoc, List.singleton_append] at co2; exact co2, ?_⟩
  refine ⟨hy.faulted, hy.code, hy.rip, hy.rsp.trans h2sp, fun _ => ?_, ?_,
    hy.r12.trans (kp2.r12.trans (hv.r12.trans (kp1.r12.trans (hu.r12.trans hL.r12)))),
    hy.r13.trans (kp2.r13.trans (hv.r13.trans (kp1.r13.trans (hu.r13.trans hL.r13)))),
    hy.r14.trans (kp2.r14.trans (hv.r14.trans (kp1.r14.trans (hu.r14.trans hL.r14)))),
    by rw [hy.mem, hBs]; exact o2, ?_, ?_, by rw [hy.mem]; exact h2m⟩
  · rw [hy.rbx, h2rbx, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [hy.rax, rax2, hBs]
  · rw [hy.mem]
    exact hspill hk2 hinB (by rw [hv.mem]; exact hspill hk1 hinB (by rw [hu.mem]; exact hL.spillB))
  · rw [hy.mem]
    exact hspill hk2 hinP (by rw [hv.mem]; exact hspill hk1 hinP (by rw [hu.mem]; exact hL.spillP))

/-- **The hex output loop** `0x404541 → 0x404605` of `sha256sum-min`: it emits
`hexLower d` (`Apps.Sha256sum.hexLower`, the hex of `(sha256sum w).stdout`) through 64 inlined
`out_putc`s (`hiSite_verified`, `loSite_verified`). -/
theorem hex_loop :
    ∀ (w : World) (message : List Byte) (K : GS → List Ev → Prop) (g : GS) (h : List Ev)
      (buf emitted d : Bytes),
      w.stdoutFull = false → g.k.fds 1 = some .stdout →
      g.x.core.rip = 0x404541#64 → Lift.Code g.x.memory → Obuf g.x.memory buf →
      HexEntry g.x d → Coalesced h buf emitted → Ok message g h → stdinRead h = message →
      (emitted ++ hexLower d).map UInt8.toBitVec <+: expected message →
      (∀ (g' : GS) (h' : List Ev), g'.x.core.rip = 0x404605#64 → g'.x.faulted = false →
        g'.exited = none → g'.k = g.k → Lift.Code g'.x.memory →
        Obuf g'.x.memory (Sys.IOLayer.putsBuf 4096 buf (hexLower d)).2 →
        Coalesced h' (Sys.IOLayer.putsBuf 4096 buf (hexLower d)).2 (emitted ++ hexLower d) →
        stdinRead h' = stdinRead h → Ok message g' h' → HexExit g.x g'.x →
        g'.x.core.read .rax =
          BitVec.ofNat 64 (Sys.IOLayer.putsBuf 4096 buf (hexLower d)).2.length →
        Leads (GStep w) (Ok message) K g' h') →
      Leads (GStep w) (Ok message) K g h := by
  intro w message K g h buf emitted d hfull hfd hrip hcode hobuf hE hco hok hrd hpre k
  have hsp := hE.sp
  refine (run_start hok.2.2.2.2.2 hcode hrip hobuf hE).leads hok.1 hok fun u hu => ?_
  have L := Silmaril.X86.Stencils.HexLoop.loop
    (K := fun p : GS × List Ev => Leads (GStep w) (Ok message) K p.1 p.2) d
    (Inv message g h buf emitted d) emitted 32 (by rw [hE.len])
    (fun i hi e => body hfull hfd hrd hE hpre i hi e)
  have htake : d.take 32 = d := by rw [← hE.len, List.take_length]
  refine L ⟨{ g with x := u }, h⟩ ?_ ?_
  · -- the invariant at the head of iteration 0
    have hB : Bof buf d 0 = buf := rfl
    refine ⟨by simp [Silmaril.X86.Stencils.HexLoop.hexLower_nil], rfl, rfl,
      ok_with hok hu.faulted, by rw [hB]; simpa using hco, ?_⟩
    rw [hB]
    exact ⟨hu.faulted, hu.code, by simp [hu.rip], hu.rsp, fun _ => by simpa using hu.rbx,
      hu.rax, hu.r12, hu.r13, hu.r14,
      obuf_keep hobuf hu.foot (fun a ha => by unfold SpillFoot at ha; omega),
      hu.spillB, hu.spillP, hu.foot.mono fun _ ha => Or.inr ha⟩
  · -- the exit
    rintro ⟨g', h'⟩ ⟨he, hk, hrd', hok', hco', hL⟩
    have hrip' : g'.x.core.rip = 0x404605#64 := by simpa using hL.rip
    exact k g' h' hrip' hL.faulted hok'.1 hk hL.code
      (by simpa [Bof, htake] using hL.obuf) (by simpa [Bof, htake] using hco') hrd' hok'
      ⟨hL.rsp, hL.r12, hL.r13, hL.r14, hL.spillB, hL.spillP, hL.foot⟩
      (by simpa [Bof, htake] using hL.rax)

end Leads

end Silmaril.Apps.Sha256sum.Stdout

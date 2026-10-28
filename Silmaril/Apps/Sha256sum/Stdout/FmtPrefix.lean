module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Wire
public import Silmaril.Apps.Sha256sum.Stdout.HexLoop

/-! # The format segment's prefix: `Digested` (`0x40310a`) to the hex loop (`0x404541`)

```
40310a: xor %ebx,%ebx ; jmp 402fec
402fec: cmp %r13b,%bpl ; je 403015            -- rbp = r13 = '-': standard input, no close
403015: test %ebx,%ebx ; jne … ; mov $1,%eax ; add $0x98,%rsp
        pop %rbx ; pop %rbp ; pop %r12 ; pop %r13 ; pop %r14 ; pop %r15 ; ret   (→ 40419f)
40419f: test %eax,%eax ; jne 404514           -- digest_file succeeded
404514: mov prefix_tag,%eax ; movzbl digest_delim,%ebp ; mov binary,%r13d
        mov %eax,0x10(%rsp) ; cmp $0xa,%bpl ; je 404c49
404c49: mov %r12,%rdx ; jmp 404c56            -- needs_escape scan of the file name "-"
404c56: movzbl (%rdx),%eax ; test %al,%al ; je 404536 ; cmp '\\' / '\n' ; … ; cmp '\r' ;
        je … ; add $1,%rdx ; (404c56)
404536: cmpl $0,0x10(%rsp) ; jne …            -- untagged
404541: (the hex loop)
```

* `pfx_ret`: `0x40310a → 0x40419f`, `digest_file`'s success return (`PfxRet`).
* `pfx_decide`: `0x40419f → 0x404c56`, `cmain`'s output decision (`output_file` inlined:
  untagged, delimiter `'\n'`, text mode; `PfxScan`).
* `pfx_scan`: `0x404c56 → 0x404541`, the `needs_escape` scan of `"-"` and the tag test
  (`PfxOut`).

`GnuSha256sum.FormatGlue.prefixSeg` assembles them into `Seg _ Wire.Digested HexEntryCutP`.

Status: **VERIFIED** (no `sorry`, standard axioms only).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.X86 (Word State Reg)
open Silmaril.Process (Memory Byte)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Process.LPS.Problems.GnuSha256sum.Wire (Caller CMain)
open Silmaril.Apps.Sha256sum.Binary.Digest (Loop)

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

theorem bv_add_add {w : Nat} (x : BitVec w) (a b : Nat) :
    x + BitVec.ofNat w a + BitVec.ofNat w b = x + BitVec.ofNat w (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem readNarrow_mem (n : X86.Ext.Narrow) (a : X86.Ext.Mem) (st : State) (mem : Memory)
    (next : Word) : X86.Ext.readNarrow n (.mem a) st mem next =
      (X86.Ext.loadN mem (a.addr st next) n.bytes).map fun v => v.setWidth n.bits := rfl

theorem breg_write_low (s : State) (r : Reg) (v : BitVec 8) :
    (X86.Ext8.BReg.low r).write s v = s.write r ((s.read r &&& ~~~(0xFF#64)) ||| v.setWidth 64) :=
  rfl

theorem writeByte_eq (s : State) (r : Reg) (v : BitVec 8) :
    X86.Ext.writeByte s r v = s.write r ((s.read r &&& ~~~(0xFF#64)) ||| v.setWidth 64) := rfl

theorem low8_zero (x : Word) : (x &&& ~~~255#64 ||| 0#64).setWidth 8 = 0#8 := by
  ext i hi; simp

theorem low8_mask (x : Word) (v : BitVec 8) :
    ((x &&& ~~~(0xFF#64)) ||| v.setWidth 64).setWidth 8 = v := by
  ext i hi; simp

theorem breg_low (s : State) (r : Reg) : (X86.Ext8.BReg.low r).read s = (s.read r).setWidth 8 :=
  rfl

/-- Back in `cmain` at `0x40419f` from `digest_file` (frame `e`): `rax = 1`, `rsp` the caller's,
the callee-saved registers restored (`rbx = 0`, `r12 = "-"`, `r14 = rsp + 0x90`), memory
unchanged. -/
structure PfxRet (e : Loop) (m : Memory) (t : XState) : Prop where
  faulted : t.faulted = false
  code : Lift.Code t.memory
  rip : t.core.rip = 0x40419f#64
  rsp : t.core.read .rsp = e.sp + 0xd0#64
  rax : t.core.read .rax = 1#64
  rbx : t.core.read .rbx = 0#64
  r12 : t.core.read .r12 = 0x406052#64
  r14 : t.core.read .r14 = e.sp + 0xd0#64 + 0x90#64
  mem : t.memory = m

/-- **`digest_file`'s return** `0x40310a → 0x40419f`. -/
theorem pfx_ret {e : Loop} {s : XState} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x40310a#64) (hrsp : s.core.read .rsp = e.sp)
    (hrbp : s.core.read .rbp = e.rbp) (hr13 : s.core.read .r13 = e.rbp)
    (hcl : Caller e s.memory) : RunsTo (PfxRet e s.memory) s := by
  obtain ⟨-, -, hfr, hbx, ⟨vbp, hbp⟩, ⟨h12, -⟩, ⟨v13, h13⟩, h14, ⟨v15, h15⟩, hra, -⟩ := hcl
  rstep [hrip]
  rstep
  rstep [hrbp, hr13, breg_low]
  rstep [hrbp, hr13, breg_low, State.read_write_other]
  rstep
  rstep
  rstep
  rstep [hrsp, bv_add_add, Nat.reduceAdd]
  rstep [hrsp, bv_add_add, Nat.reduceAdd]
  rstep [hrsp, bv_add_add, Nat.reduceAdd]
  rstep [hrsp, bv_add_add, Nat.reduceAdd]
  rstep [hrsp, bv_add_add, Nat.reduceAdd]
  rstep [hrsp, bv_add_add, Nat.reduceAdd]
  rstep [hrsp, bv_add_add, Nat.reduceAdd]
  rstep [hrsp, bv_add_add, Nat.reduceAdd]
  refine RunsTo.done ⟨hf, by assumption, rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
      not_false_eq_true, bv_add_add, Nat.reduceAdd]


/-- The bytes of `"-"` at `0x406052`, one at a time. -/
theorem dash_bytes {m : Memory} (h : m.readWith .read 0x406052 2 = some [0x2d#8, 0#8]) :
    m.readWith .read 0x406052 1 = some [0x2d#8] ∧ m.readWith .read 0x406053 1 = some [0#8] :=
  ⟨by simpa using Memory.readWith_sub_range h (offset := 0) (len := 1) (by omega) (by omega),
    by simpa using Memory.readWith_sub_range h (offset := 1) (len := 1) (by omega) (by omega)⟩

/-- At the hex loop `0x404541`, from `cmain`'s `rsp = sp` and memory `m0` at `0x40419f`: the
output-format registers (`rbx = needs_escape = 0`, `rbp = digest_delim = '\n'`,
`r12 = "-"`, `r13 = binary = 0`, `r14 = rsp + 0x90`), `prefix_tag = 0` spilled to
`0x10(%rsp)`, and nothing else written. -/
structure PfxOut (sp : Word) (m0 : Memory) (t : XState) : Prop where
  faulted : t.faulted = false
  code : Lift.Code t.memory
  rip : t.core.rip = 0x404541#64
  rsp : t.core.read .rsp = sp
  rbx : t.core.read .rbx = 0#64
  rbp : t.core.read .rbp = 0x0a#64
  r12 : t.core.read .r12 = 0x406052#64
  r13 : t.core.read .r13 = 0#64
  r14 : t.core.read .r14 = sp + 0x90#64
  tag : t.memory.readWith .read (sp + 0x10#64).toNat 4 = some (X86.Ext.leBytes 0#64 4)
  foot : Memory.WritesWithin m0 t.memory (fun a => (sp + 0x10#64).toNat ≤ a ∧ a < (sp + 0x10#64).toNat + 4)

/-- At `0x404c56`, the `needs_escape` scan at its start (`rdx = "-"`). -/
structure PfxScan (sp : Word) (m0 : Memory) (t : XState) : Prop where
  faulted : t.faulted = false
  code : Lift.Code t.memory
  rip : t.core.rip = 0x404c56#64
  rsp : t.core.read .rsp = sp
  rbx : t.core.read .rbx = 0#64
  rbp : t.core.read .rbp = 0x0a#64
  rdx : t.core.read .rdx = 0x406052#64
  r12 : t.core.read .r12 = 0x406052#64
  r13 : t.core.read .r13 = 0#64
  r14 : t.core.read .r14 = sp + 0x90#64
  tag : t.memory.readWith .read (sp + 0x10#64).toNat 4 = some (X86.Ext.leBytes 0#64 4)
  foot : Memory.WritesWithin m0 t.memory (fun a => (sp + 0x10#64).toNat ≤ a ∧ a < (sp + 0x10#64).toNat + 4)

/-- `0x40419f → 0x404c56`: success, the output format read (untagged, `'\n'`, text). -/
theorem pfx_decide {sp : Word} {s : XState} (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x40419f#64) (hrsp : s.core.read .rsp = sp)
    (hrax : s.core.read .rax = 1#64) (hrbx : s.core.read .rbx = 0#64)
    (hr12 : s.core.read .r12 = 0x406052#64) (hr14 : s.core.read .r14 = sp + 0x90#64)
    (hcm : CMain sp s.memory) : RunsTo (PfxScan sp s.memory) s := by
  obtain ⟨-, -, hspb, hsr, hsw, -, -, -, hpt, hdl, hbin, -, -⟩ := hcm
  rstep [hrip, hrax]
  rstep
  rstep
  rstep [readNarrow_mem, X86.Ext.Narrow.bytes, X86.Ext.Narrow.bits, X86.Ext.leValue]
  rstep
  rstep [hrsp]
  rstep [breg_low]
  rstep [breg_low]
  rstep [hr12]
  rstep
  refine RunsTo.done ⟨hf, by assumption, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rfin [hrsp, hrbx, hr12, hr14] [Bool.false_eq_true]

/-- `0x404c56 → 0x404541`: `"-"` needs no escape; untagged. -/
theorem pfx_scan {sp : Word} {m0 : Memory} {s : XState} (hp : PfxScan sp m0 s)
    (hdash : s.memory.readWith .read 0x406052 2 = some [0x2d#8, 0#8]) :
    RunsTo (PfxOut sp m0) s := by
  obtain ⟨hf, hc, hrip, hrsp, hrbx, hrbp, hrdx, hr12, hr13, hr14, htag, hfoot⟩ := hp
  obtain ⟨hd0, hd1⟩ := dash_bytes hdash
  have e1 : (45#8 == 92#8) = false := by decide
  have e2 : (45#8 == 10#8) = false := by decide
  have e3 : (45#8 == 13#8) = false := by decide
  rstep [hrip, hrdx, readNarrow_mem, X86.Ext.Narrow.bytes, X86.Ext.Narrow.bits, X86.Ext.leValue]
  rstep [e1, e2, e3, breg_low, breg_write_low, writeByte_eq, low8_mask]
  rstep [e1, e2, e3, breg_low, breg_write_low, writeByte_eq, low8_mask]
  rstep [e1, e2, e3, breg_low, breg_write_low, writeByte_eq, low8_mask]
  rstep [e1, e2, e3, breg_low, breg_write_low, writeByte_eq, low8_mask]
  rstep [e1, e2, e3, breg_low, breg_write_low, writeByte_eq, low8_mask]
  rstep [e1, e2, e3, breg_low, breg_write_low, writeByte_eq, low8_mask]
  rstep [e1, e2, e3, breg_low, breg_write_low, writeByte_eq, low8_mask]
  simp (config := {zeta := true}) only [breg_low, breg_write_low, State.read_write_same,
    State.read_write_other, ne_eq, reduceCtorEq, not_false_eq_true, low8_zero]
  rstep [e1, e2, e3, breg_low, breg_write_low, writeByte_eq, low8_mask, low8_zero]
  rstep [e1, e2, e3, breg_low]
  rstep [e1, e2, e3, breg_low]
  rstep [hrdx]
  rstep [readNarrow_mem, X86.Ext.Narrow.bytes, X86.Ext.Narrow.bits, X86.Ext.leValue]
  rstep [breg_low]
  rstep [breg_low]
  rstep [hrsp]
  rstep
  refine RunsTo.done ⟨hf, by assumption, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rfin [hrsp, hrbx, hrbp, hr12, hr13, hr14] [Bool.false_eq_true]

end Silmaril.Apps.Sha256sum.Stdout

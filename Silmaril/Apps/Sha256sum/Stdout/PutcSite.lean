module

public import Silmaril.Apps.Sha256sum.Stdout.Putc
public import Silmaril.Apps.Sha256sum.Stdout.OutFlush

/-! # Inlined buffered `out_putc` sites, with a register precondition

`Stdout.PutcContract` states the `out_putc` contract at an inlined site with no precondition
on the entry registers. The compiled sites of the hex loop of `sha256sum-min` keep `olen` in a
register across the loop (`cmp $0x1000,%rax` at `0x4045c2`, `cmp $0x1000,%rdx` at
`0x404584`), and the exit hands the new `olen` back in a register, so that contract is false
there. `PutcSite entry exit Pre byteOf Post` adds

* `Pre buf s`: a precondition of the entry state (e.g. `rax = |buf|`, the stack frame the
  `out_flush` call needs), and
* `Post buf' s s'`: the exit relation, which may name the new buffer `buf'` (e.g.
  `rdx = |buf'|`, the registers and frame kept).

`PutcContract.site`: every `PutcContract` is a `PutcSite` (with `Pre := True`).

`FlushContract`: the contract of a call of `out_flush` (`0x401100`) in `Leads` form, over the
entry and exit shapes of `Stdout.OutFlush` (`FlushEntry`, `FlushExit`): from a call with
`obuf[0, olen) = buf`, `out_error = 0`, every execution writes `buf` to standard output (any
kernel split) and returns with `olen = 0`, `out_error = 0`. It is a hypothesis here, proved by
the `out_flush` prover (`Stdout.OutFlush`).

The two hex sites are proved in `Stdout.HexHi` (`hiSite_verified`) and `Stdout.HexLo`
(`loSite_verified`, `flushContract`): the buffer-full branch calls `out_flush` and reloads
`olen`; the appended byte is not a newline (`Pre`), so the newline branch (a second flush) is
not taken.

Status: definitions (statements) and `PutcContract.site` (VERIFIED).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.X86 (Word)
open Silmaril.Process (Memory Byte)
open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev out stdinRead expected)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-- **An inlined buffered `out_putc` site** with an entry precondition `Pre` and an exit
relation `Post` (see the module docstring). -/
def PutcSite (entry exit : Word) (Pre : Bytes → XState → Prop) (byteOf : XState → UInt8)
    (Post : Bytes → XState → XState → Prop) : Prop :=
  ∀ (w : World) (message : List Byte) (K : GS → List Ev → Prop) (g : GS) (h : List Ev)
    (buf emitted : Bytes),
    w.stdoutFull = false → g.k.fds 1 = some .stdout →
    g.x.core.rip = entry → Lift.Code g.x.memory → Obuf g.x.memory buf → Pre buf g.x →
    Coalesced h buf emitted → Ok message g h → stdinRead h = message →
    (emitted ++ [byteOf g.x]).map UInt8.toBitVec <+: expected message →
    (∀ (g' : GS) (h' : List Ev), g'.x.core.rip = exit → g'.x.faulted = false →
      g'.exited = none → g'.k = g.k → Lift.Code g'.x.memory →
      Obuf g'.x.memory (Sys.IOLayer.putcBuf 4096 buf (byteOf g.x)).2 →
      Coalesced h' (Sys.IOLayer.putcBuf 4096 buf (byteOf g.x)).2 (emitted ++ [byteOf g.x]) →
      stdinRead h' = stdinRead h → Ok message g' h' →
      Post (Sys.IOLayer.putcBuf 4096 buf (byteOf g.x)).2 g.x g'.x →
      Leads (GStep w) (Ok message) K g' h') →
    Leads (GStep w) (Ok message) K g h

/-- Every `PutcContract` is a `PutcSite` (VERIFIED). -/
theorem PutcContract.site {entry exit : Word} {byteOf : XState → UInt8}
    {Keep : XState → XState → Prop} (hc : PutcContract entry exit byteOf Keep)
    (Pre : Bytes → XState → Prop) :
    PutcSite entry exit Pre byteOf (fun _ => Keep) :=
  fun w message K g h buf emitted hfull hfd hrip hcode hobuf _ hco hok hrd hpre k =>
    hc w message K g h buf emitted hfull hfd hrip hcode hobuf hco hok hrd hpre k

/-- `out_error` is 0. -/
def OutErrorZero (m : Memory) : Prop :=
  m.readWith .read 0x41212c 4 = some (X86.Ext.leBytes 0#64 4)

/-- **The `out_flush` call contract** (statement; a hypothesis of this file). From a call of
`out_flush` (`FlushEntry`, return address `ra`) with `obuf[0, olen) = buf`, `out_error = 0`,
and `emitted` the bytes emitted so far, every execution keeps `Ok` and returns
(`FlushExit`: `olen = 0`, return value 0, the callee-saved registers, the footprint) with
`out_error = 0` and `buf` written to standard output. -/
def FlushContract : Prop :=
  ∀ (w : World) (message : List Byte) (K : GS → List Ev → Prop) (g : GS) (h : List Ev)
    (buf emitted : Bytes) (ra : Word),
    w.stdoutFull = false → g.k.fds 1 = some .stdout →
    FlushEntry g.x buf ra → OutErrorZero g.x.memory →
    Coalesced h buf emitted → Ok message g h → stdinRead h = message →
    emitted.map UInt8.toBitVec <+: expected message →
    (∀ (g' : GS) (h' : List Ev), FlushExit g.x ra g'.x → g'.exited = none → g'.k = g.k →
      OutErrorZero g'.x.memory → Coalesced h' [] emitted → stdinRead h' = stdinRead h →
      Ok message g' h' → Leads (GStep w) (Ok message) K g' h') →
    Leads (GStep w) (Ok message) K g h

/-! ## The two sites of the hex loop -/

/-- The byte in the low 8 bits of a register (`%bpl`, `%r15b`). -/
def lowByte (r : Word) : UInt8 := UInt8.ofBitVec (r.setWidth 8)

/-- What a hex site may write: the `out_flush` call frame below `rsp`, and `out_error`, `olen`,
`obuf`. -/
def SiteFoot (sp : Nat) (a : Nat) : Prop :=
  (sp - 40 ≤ a ∧ a < sp) ∨ (0x41212c ≤ a ∧ a < 0x412140 + 4096)

/-- The stack a hex site needs (the `out_flush` call frame below `rsp`). -/
structure SiteStack (s : XState) : Prop where
  sp : 0x414028 ≤ (s.core.read .rsp).toNat ∧ (s.core.read .rsp).toNat < 2 ^ 47
  frameR : s.memory.Permitted .read ((s.core.read .rsp).toNat - 40) 40
  frameW : s.memory.Permitted .write ((s.core.read .rsp).toNat - 40) 40

/-- What a hex site keeps: `rsp`, the callee-saved registers, and memory outside `SiteFoot`. -/
structure SiteKept (s s' : XState) : Prop where
  rsp : s'.core.read .rsp = s.core.read .rsp
  rbx : s'.core.read .rbx = s.core.read .rbx
  rbp : s'.core.read .rbp = s.core.read .rbp
  r12 : s'.core.read .r12 = s.core.read .r12
  r13 : s'.core.read .r13 = s.core.read .r13
  r14 : s'.core.read .r14 = s.core.read .r14
  r15 : s'.core.read .r15 = s.core.read .r15
  foot : Memory.WritesWithin s.memory s'.memory (SiteFoot (s.core.read .rsp).toNat)

/-- The entry of the high-digit site `0x4045c2`: `rax = olen`, `%bpl` the digit, not a
newline. -/
def hiPre (buf : Bytes) (s : XState) : Prop :=
  s.core.read .rax = BitVec.ofNat 64 buf.length ∧ lowByte (s.core.read .rbp) ≠ 10 ∧ SiteStack s

/-- The exit `0x404578`: `rdx = olen`. -/
def hiPost (buf' : Bytes) (s s' : XState) : Prop :=
  SiteKept s s' ∧ s'.core.read .rdx = BitVec.ofNat 64 buf'.length

/-- The entry of the low-digit site `0x404584`: `rdx = olen`, `%r15b` the digit, not a
newline. -/
def loPre (buf : Bytes) (s : XState) : Prop :=
  s.core.read .rdx = BitVec.ofNat 64 buf.length ∧ lowByte (s.core.read .r15) ≠ 10 ∧ SiteStack s

/-- The exit `0x4045a5`: `rax = olen`. -/
def loPost (buf' : Bytes) (s s' : XState) : Prop :=
  SiteKept s s' ∧ s'.core.read .rax = BitVec.ofNat 64 buf'.length

end Silmaril.Apps.Sha256sum.Stdout

module

public import Silmaril.Apps.Sha256sum.Stdout.Run
public import Silmaril.Apps.Sha256sum.IOLayer.Write

/-! # The `out_putc` contract (statement), in `GStep`/`Leads` form

Status: **statement only** (definitions; nothing is assumed or proved here). The proof is the
`out_flush` contract (`Stdout.OutFlush`) plus the inlined append; it is in progress.

`out_putc` is inlined at every site of `sha256sum-min` (the hex loop at `0x4045ae…0x4045a5`,
`print_filename`, `out_puts`, the separators), so the contract is stated for an arbitrary site:
an entry address, an exit address, the byte the site appends (`byteOf`, read from the entry
state), and what the site keeps (`Keep`, its registers and frame).

* `Obuf m buf`: the layer state in memory (`olen = |buf|`, `obuf[0, olen) = buf`,
  `out_error = 0`, the buffer and `olen` writable).
* `Coalesced h buf emitted`: **the LPS form of `putsBuf_inv`**: the bytes written to standard
  output in the history (`GnuSha256sum.out`) followed by the buffered bytes are the bytes
  emitted so far. Since `out h` is then a prefix of `emitted`, the `Ok` condition
  `out h <+: expected message` follows from `emitted <+: expected` (`putsBuf_prefix`).
* `PutcContract entry exit byteOf Keep`: from the site entry with `Obuf buf` and
  `Coalesced h buf emitted`, every execution keeps `Ok` and reaches the site exit with
  `Obuf (putcBuf 4096 buf c).2` and `Coalesced h' _ (emitted ++ [c])`, after zero or more
  `write(1, …)` events (one `out_flush`, any kernel split) and no read.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.X86 (Word)
open Silmaril.Process (Memory Byte)
open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev out stdinRead expected)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-- The output buffer `obuf`/`olen`/`out_error` of `sha256sum-min` holds `buf`. -/
structure Obuf (m : Memory) (buf : Bytes) : Prop where
  cap : buf.length ≤ 4096
  olen : m.readWith .read 0x412130 8 = some (X86.Ext.leBytes (BitVec.ofNat 64 buf.length) 8)
  obuf : m.readWith .read 0x412140 buf.length = some (buf.map ofU8)
  outError : m.readWith .read 0x41212c 4 = some (X86.Ext.leBytes 0#64 4)
  olenW : m.Permitted .write 0x412130 8
  obufW : m.Permitted .write 0x412140 4096
  obufR : m.Permitted .read 0x412140 4096

/-- **Coalescing, trace form**: written to stdout, then buffered, is what was emitted. -/
def Coalesced (h : List Ev) (buf emitted : Bytes) : Prop :=
  out h ++ buf.map UInt8.toBitVec = emitted.map UInt8.toBitVec

/-- **The `out_putc` contract** at an inlined site (statement). -/
def PutcContract (entry exit : Word) (byteOf : XState → UInt8)
    (Keep : XState → XState → Prop) : Prop :=
  ∀ (w : World) (message : List Byte) (Post : GS → List Ev → Prop) (g : GS) (h : List Ev)
    (buf emitted : Bytes),
    w.stdoutFull = false → g.k.fds 1 = some .stdout →
    g.x.core.rip = entry → Lift.Code g.x.memory → Obuf g.x.memory buf →
    Coalesced h buf emitted → Ok message g h → stdinRead h = message →
    (emitted ++ [byteOf g.x]).map UInt8.toBitVec <+: expected message →
    (∀ (g' : GS) (h' : List Ev), g'.x.core.rip = exit → g'.x.faulted = false →
      g'.exited = none → g'.k = g.k → Lift.Code g'.x.memory →
      Obuf g'.x.memory (Sys.IOLayer.putcBuf 4096 buf (byteOf g.x)).2 →
      Coalesced h' (Sys.IOLayer.putcBuf 4096 buf (byteOf g.x)).2 (emitted ++ [byteOf g.x]) →
      stdinRead h' = stdinRead h → Ok message g' h' → Keep g.x g'.x →
      Leads (GStep w) (Ok message) Post g' h') →
    Leads (GStep w) (Ok message) Post g h

end Silmaril.Apps.Sha256sum.Stdout

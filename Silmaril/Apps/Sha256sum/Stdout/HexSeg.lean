module

public import Silmaril.Apps.Sha256sum.Stdout.FormatSuffix

/-! # The hex loop of the format segment as a `Seg` between cut points

```
Digested ──prefix──▶ HexEntryCut (0x404541) ──hex_loop──▶ HexExitCut (0x404605) ──suffix──▶ Formatted
```

`HexEntryCut` is the cut at the hex loop's entry `0x404541`: what `Stdout.hex_loop` needs
(`HexEntry`, the stdout layer, `Ok`) together with what `HexExitCut` records of the loop's entry
state (the output-format registers and `SufMem`), and the answer (`hexLower d ++ "  -\n"` after
what was emitted so far). The format prefix (`0x40310a → 0x404541`, `Stdout.FmtPrefix`) ends at
this cut.

`hexSeg_of` turns a hex loop whose exit also reports `rax = olen` (`HexLoopRax`, which
`HexExitAt.rax` needs) into `Seg _ HexEntryCut HexExitCut`; `hex_loop` is one
(`hexLoopRax`), so `hexSeg` is unconditional.

Status: **VERIFIED** (no `sorry`, standard axioms only).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.X86 (Word State Reg)
open Silmaril.Process (Memory Byte)
open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev out stdinRead expected Cut Seg)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-- **At the hex loop's entry** `0x404541`, with stdout buffer `buf`, the bytes `emitted` so far
and the digest `d`. -/
structure HexEntryAt (message : List Byte) (buf emitted d : Bytes) (g : GS) (h : List Ev) :
    Prop where
  ok : Ok message g h
  rip : g.x.core.rip = 0x404541#64
  code : Lift.Code g.x.memory
  fd0 : ∃ s, g.k.fds 0 = some s
  fd1 : g.k.fds 1 = some .stdout
  fd2 : ∃ s, g.k.fds 2 = some s
  entry : HexEntry g.x d
  rbx : (g.x.core.read .rbx).setWidth 32 = 0#32
  rbp : (g.x.core.read .rbp).setWidth 8 = 0x0a#8
  r12 : g.x.core.read .r12 = 0x406052#64
  r13 : (g.x.core.read .r13).setWidth 32 = 0#32
  mem : SufMem (g.x.core.read .rsp) g.x.memory
  obuf : Obuf g.x.memory buf
  co : Coalesced h buf emitted
  read : stdinRead h = message
  answer : (emitted ++ hexLower d ++ recordTail).map UInt8.toBitVec = expected message

/-- **The cut at the hex loop's entry** (`0x404541`). -/
def HexEntryCut : Cut := fun _ message g h => ∃ buf emitted d, HexEntryAt message buf emitted d g h

/-- `hex_loop`'s statement, with the exit also reporting `rax = olen` (the length of the
buffer after the 64 digits). -/
def HexLoopRax : Prop :=
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
    Leads (GStep w) (Ok message) K g h

/-- **The hex loop as a segment** `HexEntryCut → HexExitCut` (VERIFIED, from `HexLoopRax`). -/
theorem hexSeg_of (hl : HexLoopRax) (domain : List Byte → Prop) :
    Seg domain HexEntryCut HexExitCut := by
  intro prog posix fs message g h _ ⟨buf, emitted, d, hA⟩
  have hpre : (emitted ++ hexLower d).map UInt8.toBitVec <+: expected message := by
    rw [← hA.answer]
    exact ⟨recordTail.map UInt8.toBitVec, by rw [← List.map_append]⟩
  refine hl _ message _ g h buf emitted d rfl hA.fd1 hA.rip hA.code hA.obuf hA.entry hA.co hA.ok
    hA.read hpre ?_
  intro g' h' hrip _ _ hk hc hob hco hrd hok hex hrax
  refine Leads.done ?_
  unfold HexExitCut
  refine ⟨g.x, (Sys.IOLayer.putsBuf 4096 buf (hexLower d)).2, emitted ++ hexLower d, ?_⟩
  exact
    { ok := hok
      rip := hrip
      code := hc
      fd0 := hk ▸ hA.fd0
      fd1 := hk ▸ hA.fd1
      fd2 := hk ▸ hA.fd2
      exit := hex
      rbx := hA.rbx
      rbp := hA.rbp
      r12 := hA.r12
      r13 := hA.r13
      mem := hA.mem
      rax := hrax
      obuf := hob
      co := hco
      read := hrd.trans hA.read
      answer := by rw [← hA.answer, List.append_assoc] }

/-- `hex_loop` is a `HexLoopRax` (VERIFIED). -/
theorem hexLoopRax : HexLoopRax := hex_loop

/-- **The hex loop as a segment** `HexEntryCut → HexExitCut` (VERIFIED). -/
theorem hexSeg (domain : List Byte → Prop) : Seg domain HexEntryCut HexExitCut :=
  hexSeg_of hexLoopRax domain

end Silmaril.Apps.Sha256sum.Stdout

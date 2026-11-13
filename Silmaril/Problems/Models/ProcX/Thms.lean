module

public import Silmaril.Problems.Models.ProcX.Defs
public import Silmaril.Process.CLI.GapSim
public import Silmaril.X86.Str9FsXN.Thms
import Silmaril.Proofs.Problems.Models.ProcX.Lift

/-!
# `musl-str9fsxn`: the gap simulation from `musl-str9`, transfer, listing laws, gzip vectors

* `userStep_of_proc`: every `musl-str9` user step that is not the `unmodeled` fault is a step
  here, with the XMM file as a frame (`liftStep`); `isa_step_of_proc` adds the startup arms.
* `gapLe : Proc.model.GapLe model`, hence `agrees_proc`, `halts_proc`, `bounded_proc`
  (statements move down to `musl-str9`) and `exitsOn_of_proc` (nonvacuity moves up).
* `isa_step_of_step`, `isa_step_of_listed_sse`, `isa_step_of_listed`: the listing laws of
  `Str9FsXN` lifted to the process step, for a non-trapping `rip`.
* Kernel-checked vectors: every SSE, atomic and narrow-shift byte string of the statically
  linked `h-gz-api` zlib harnesses (zlib 1.3.1, 1.3.2 and the dev builds, musl) that `Str9`
  rejects is decoded here at its full length (`gz_sse_decoded`, `gz_atomic_decoded`,
  `gz_narrow_decoded`), and `musl-str9` rejects them (`gz_str9_rejects`).
-/

@[expose] public section

namespace Silmaril.Problems.Models.ProcX

open Silmaril.Process.CLI
open Silmaril.X86 (State MState Word Byte)
open Silmaril.X86.Sse9 (XState XFile)
open Silmaril.Process (Memory)

/-! ## Conservative extension, up to the gaps of `musl-str9` -/

theorem userStep_of_proc {c : State} (x : XFile) {m : Memory}
    (h : Proc.userStep c m ≠ .fault .unmodeled) :
    userStep ⟨c, x⟩ m = liftStep x (Proc.userStep c m) :=
  Silmaril.Proofs.Problems.Models.ProcX.userStep_of_proc x h

theorem isa_step_of_proc {c : State} (x : XFile) {m : Memory} {o : Step State}
    (h : Proc.isa.step c m o) (ho : o ≠ .fault .unmodeled) :
    isa.step ⟨c, x⟩ m (liftStep x o) :=
  Silmaril.Proofs.Problems.Models.ProcX.isa_step_of_proc x h ho

/-- **`musl-str9fsxn` fills the gaps of `musl-str9`.** -/
theorem gapLe : Proc.model.GapLe model := ⟨Silmaril.Proofs.Problems.Models.ProcX.gapSim⟩

theorem agrees_proc {image : Image} {S : CliSpec} (h : Agrees model image S) :
    Agrees Proc.model image S := Agrees.of_gapLe gapLe h

theorem halts_proc {image : Image} {domain : ProcInput → Prop} (h : Halts model image domain) :
    Halts Proc.model image domain := Halts.of_gapLe gapLe h

theorem bounded_proc {image : Image} {domain : ProcInput → Prop} {budget : ProcInput → Nat}
    {perRefusal : Nat} (h : Bounded model image domain budget perRefusal) :
    Bounded Proc.model image domain budget perRefusal := Bounded.of_gapLe gapLe h

/-- **Nonvacuity moves up**: a `musl-str9` witness is a `musl-str9fsxn` witness. -/
theorem exitsOn_of_proc {image : Image} {stdin : List Silmaril.Process.Byte}
    (h : Proc.ExitsOn Proc.model image stdin) : Proc.ExitsOn model image stdin :=
  Silmaril.Proofs.Problems.Models.ProcX.exitsOn_of_proc h

/-! ## Listing laws -/

/-- A non-trapping `Str9FsXN` step is a step of the model. -/
theorem isa_step_of_step {c : Core} {m : Memory} {y : XState}
    (nontrap : m.fetchBytes c.core.rip.toNat 2 ≠ some X86Linux.syscallBytes)
    (h : Silmaril.X86.Str9FsXN.step ⟨⟨c.core, m⟩, c.xmm⟩ = some y) :
    isa.step c m (.retired ⟨y.m.core, y.xmm⟩ y.m.memory) :=
  Silmaril.Proofs.Problems.Models.ProcX.isa_step_of_step nontrap h

/-- **The SSE listing law** at the process step. -/
theorem isa_step_of_listed_sse {c : Core} {m : Memory} {base : Word} {code : List Byte}
    {o l : Nat} {i : Silmaril.X86.Sse9.Instr} {c' : State} {xs : XFile} {m' : Memory}
    (nontrap : m.fetchBytes c.core.rip.toNat 2 ≠ some X86Linux.syscallBytes)
    (hl : Silmaril.X86.Ext.Loaded m base code) (hrip : c.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length)
    (hdec : Silmaril.X86.Str9FsX.decodeSseL ((code.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Sse9.exec i c.core c.xmm m (c.core.rip + BitVec.ofNat 64 l) =
      .ok c' xs m') :
    isa.step c m (.retired ⟨c', xs⟩ m') :=
  isa_step_of_step (y := ⟨⟨c', m'⟩, xs⟩) nontrap
    (Silmaril.X86.Str9FsXN.step_of_listed_sse (x := ⟨⟨c.core, m⟩, c.xmm⟩) hl hrip hfit hdec hx)

/-- **The integer listing law** at the process step (`Str9Fs`'s instructions, `rep stosd`,
the `Narrow9` forms). -/
theorem isa_step_of_listed {c : Core} {m : Memory} {base : Word} {code : List Byte}
    {o l : Nat} {i : Silmaril.X86.Str9FsXN.Instr} {c' : State} {m' : Memory}
    (nontrap : m.fetchBytes c.core.rip.toNat 2 ≠ some X86Linux.syscallBytes)
    (hl : Silmaril.X86.Ext.Loaded m base code) (hrip : c.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length)
    (hdec : Silmaril.X86.Str9FsXN.decode ((code.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Str9FsXN.exec i c.core m l = .ok c' m') :
    isa.step c m (.retired ⟨c', c.xmm⟩ m') :=
  isa_step_of_step (y := ⟨⟨c', m'⟩, c.xmm⟩) nontrap
    (Silmaril.X86.Str9FsXN.step_of_listed (x := ⟨⟨c.core, m⟩, c.xmm⟩) hl hrip hfit hdec hx)

/-! ## The gzip vectors (kernel-checked)

The byte strings are every SSE and atomic instruction of the four `h-gz-api` harness builds
that `Str9` rejects, from `objdump -d` of `.init`/`.text`/`.fini`: `vfprintf`'s prologue
(`pxor xmm0, xmm0`; `movaps`/`movups` stores; `movdqu xmm1, [rdx]`), `snprintf`'s varargs
saves, `printf_core`'s positional-argument copy (`movdqa`), and `__lock`, `__lockfile`,
`__unlockfile` (`lock cmpxchg`, `lock xadd`, `xchg`), and the compressor's narrow forms
(`shr r/m16, imm8` in `deflate_fast`, `deflate_slow`, `_tr_align`, `_tr_flush_bits`;
`sbb cl, 0xff` in `deflate`). -/

/-- The SSE byte strings. -/
def gzSse : List (List Byte) :=
  [[0x66, 0x0F, 0xEF, 0xC0],
   [0x0F, 0x29, 0x04, 0x24],
   [0x0F, 0x29, 0x44, 0x24, 0x20], [0x0F, 0x29, 0x44, 0x24, 0x30],
   [0x0F, 0x29, 0x44, 0x24, 0x50], [0x0F, 0x29, 0x44, 0x24, 0x60],
   [0x0F, 0x29, 0x4C, 0x24, 0x60], [0x0F, 0x29, 0x54, 0x24, 0x70],
   [0x0F, 0x29, 0x9C, 0x24, 0x80, 0x00, 0x00, 0x00],
   [0x0F, 0x29, 0xA4, 0x24, 0x90, 0x00, 0x00, 0x00],
   [0x0F, 0x29, 0xAC, 0x24, 0xA0, 0x00, 0x00, 0x00],
   [0x0F, 0x29, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00],
   [0x0F, 0x29, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00],
   [0x0F, 0x11, 0x4C, 0x24, 0x08],
   [0xF3, 0x0F, 0x6F, 0x0A],
   [0x66, 0x0F, 0x6F, 0x04, 0x3E]]

/-- The atomic byte strings. -/
def gzAtomic : List (List Byte) :=
  [[0xF0, 0x0F, 0xB1, 0x17], [0xF0, 0x0F, 0xB1, 0x37],
   [0xF0, 0x44, 0x0F, 0xB1, 0x07], [0xF0, 0x44, 0x0F, 0xB1, 0x82, 0x8C, 0x00, 0x00, 0x00],
   [0xF0, 0x44, 0x0F, 0xC1, 0x07],
   [0x87, 0x82, 0x8C, 0x00, 0x00, 0x00]]

/-- The narrow integer byte strings. -/
def gzNarrow : List (List Byte) :=
  [[0x66, 0xC1, 0xE8, 0x0F], [0x66, 0xC1, 0xED, 0x07], [0x66, 0x41, 0xC1, 0xEC, 0x07],
   [0x66, 0xC1, 0xA8, 0x30, 0x17, 0x00, 0x00, 0x08],
   [0x66, 0xC1, 0xAF, 0x30, 0x17, 0x00, 0x00, 0x08], [0x80, 0xD9, 0xFF]]

/-- Each SSE string is an SSE form of `Str9FsX`, read at its full length. -/
theorem gz_sse_decoded :
    gzSse.all (fun w => (Silmaril.X86.Str9FsX.decodeSseL w).map (·.2) == some w.length) = true := by
  decide

/-- Each atomic string is an integer form of `Str9FsXN`, read at its full length. -/
theorem gz_atomic_decoded :
    gzAtomic.all (fun w => (Silmaril.X86.Str9FsXN.decode w).map (·.2) == some w.length) = true := by
  decide

/-- Each narrow string is an integer form of `Str9FsXN`, read at its full length. -/
theorem gz_narrow_decoded :
    gzNarrow.all (fun w => (Silmaril.X86.Str9FsXN.decode w).map (·.2) == some w.length) = true := by
  decide

/-- `Str9`'s listing decoder rejects all of them (so `musl-str9` stops there). -/
theorem gz_str9_rejects :
    (gzSse ++ gzAtomic ++ gzNarrow).all (fun w => (Silmaril.X86.Str9.decode w).isNone) = true := by
  decide

end Silmaril.Problems.Models.ProcX

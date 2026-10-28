module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.DigestFinal
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Release
public import Silmaril.Process.LPS.Problems.GnuSha256sum.ReadLoop
public import Silmaril.Apps.Sha256sum.Stdout.Putc
public import Silmaril.Apps.Sha256sum.Stdout.Tail
public import Silmaril.Apps.Sha256sum.Stdout.OutFlush
public import Silmaril.X86.Stencils.HexLoop

/-! # GNU `sha256sum`: the two inner cut points of the tail (`Release.Open`)

`Release.Open Digested Formatted` leaves the two inner cut points of the tail as parameters.
This file fixes them (**the contract between the `final`, `format` and `exit` segments**):

```
AtLoopPadW ──finalW──▶ Digested (0x40310a) ──format──▶ Formatted (0x40464d) ──exitW──▶ DoneCut
```

* `Digested`: `0x40310a` inside `digest_file`, right after `sha_final` (`Digest.AtOut`, the
  end of `Digest.final_digest`): the 32 bytes of `bin[]` (`cmain`'s `rsp + 0x70`, passed as
  `digest_file`'s `out`) are `SHA256.digest` of the whole message, the whole message read
  (stdin at end of file), nothing written yet, descriptors 0, 1, 2 the standard streams, and
  `Caller e`: `digest_file`'s saved registers and return address `0x40419f` (the stdin call
  site `0x40419a` of `cmain`), and `CMain`: what `cmain` and the output layer hold (`obuf`
  empty, flags, the `hexd` table, the argument loop at its last operand).
* `Formatted`: `0x40464d`, back in `cmain` after the record, before the operand loop's exit
  and `close(0)`: `Stdout.FormattedCut` (`gnu-r3-output`). The record's `'\n'` `out_putc`
  flushed the output layer, so the 68 bytes `hex ++ "  -\n"` are all written
  (`out h = expected message`, `olen = 0`).

The format segment (hex helpers, `sha256sum/gnu-r3-hex`, `gnu-r3-hexlo`, `gnu-r3-fmtglue`)
proves `Seg _ Digested Formatted` against exactly these definitions.

**`Release.AtLoopPad` is too weak for `final`.** It does not record end of file (a padding
state need not have read the whole message, while `Done` needs `stdinRead h = message`), nor
anything about `digest_file`'s caller or the `sha_final` code. So the read loop's cuts are
strengthened here: `AtLoopHeadW` (`HeadK` with `Entry e`: `Caller e` at the loop's entry
memory `e.m0`, and the `out` slot) and `AtLoopPadW` (`PadK`, the whole message read, `Entry`).

* `read_step_eof`, `update_step_eof`, `loop_leads_eof`, `readLoopW` (VERIFIED): the read
  loop of `ReadLoop`, also recording end of file (a `read` returning nothing saw the end of
  standard input: `Sys.Chunk`).
* `Caller.of_writes`, `CMain.of_writes` (VERIFIED): the caller's facts survive writes in
  `Free` / `Scratch` (the loop's `loopSpan`, `sha_final`'s `finSpan`).
* `final_digest_w`, `finalW` (VERIFIED): `Seg _ AtLoopPadW Digested`, from
  `Digest.Final.final_runs` (with `Digest.FinalSpec`'s `outBytes_digest`/`hfin_hash`), moved
  to `GStep` (any `r11`) by `Silent.leads_of_reaches`.
* `exitW` (VERIFIED): `Stdout.exitSegment` (`gnu-r3-output`).
* `OpenW`, `sysTotal_of_W`, `lpsTotal_of_W`, `lpsBounded_of_W`, `lpsPartial_of_W`,
  `agree_of_W` (VERIFIED): the release theorems from `startup : Seg _ LaunchCut AtLoopHeadW`
  and `format : Seg _ Digested Formatted`.

Everything proved here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum.Wire

open Silmaril.Process.LPS.Problems.GnuSha256sum
open Silmaril.Apps.Sha256sum.X86Sys (XState ofU8)
open Silmaril.Apps.Sha256sum.Binary.Digest (Loop AtOut OutBuf)
open Silmaril.X86 (Word)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Apps.Sha256sum.X86Sys (Core)
open Silmaril.Apps.Sha256sum.Sys (Call Ret KState WorldStep Src Chunk)
open Silmaril.Apps.Sha256sum.Binary.Digest (AfterRead AtHead AtPad LoopFrame)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)
open Silmaril.X86.Ext (Loaded loadN)

/-- The kernel side of the tail: descriptors 0, 1, 2 are the standard streams and standard
input is at end of file. -/
structure KTail (g : GS) : Prop where
  fd0 : g.k.fds 0 = some .stdin
  fd1 : g.k.fds 1 = some .stdout
  fd2 : g.k.fds 2 = some .stderr
  eof : g.k.stdin = .bytes []

/-- **`cmain`'s state the tail reads**, for `cmain`'s stack pointer `sp` (its `rsp` at the
stdin call site `0x40419a` and after the return to `0x40419f`):

* the text (`Lift.Code`, read-only) and the `hexd` table `"0123456789abcdef"` (`0x4072c0`);
* `sp` above `.bss`, and the stack readable and writable from `sp - 128` (the frames of
  `close_stdout`, `out_flush` and the inlined `out_putc` calls) to `sp + 0x98` (`bin[]` at
  `sp + 0x70` included);
* the locals: `ok = 1` (`0x2c(%rsp)`), the operand index `0` (`0x8(%rsp)`, 8 bytes) of the
  operand count `1` (`0x50(%rsp)`, 4 bytes; so the operand loop ends after `"-"`);
* the globals: `have_read_stdin = 1` (`0x40a0a0`), `prefix_tag = 0` (`0x409020`),
  `digest_delim = '\n'` (`0x409014`), `binary = 0` (`0x409010`), `err_error = 0`
  (`0x412128`);
* the output layer empty: `Stdout.Obuf m []` (`olen = 0`, `out_error = 0`, `obuf`
  writable). -/
structure CMain (sp : Word) (m : Memory) : Prop where
  code : Apps.Sha256sum.Lift.Code m
  table : m.readWith .read 0x4072c0 16 = some (Silmaril.X86.Stencils.HexLoop.hexTable.map ofU8)
  spBound : 0x414100 ≤ sp.toNat ∧ sp.toNat + 0x100 < 2 ^ 47
  stackR : m.Permitted .read (sp.toNat - 128) (128 + 0x98)
  stackW : m.Permitted .write (sp.toNat - 128) (128 + 0x98)
  okFlag : m.readWith .read (sp + 0x2c#64).toNat 4 = some (X86.Ext.leBytes 1#64 4)
  /-- The operand loop at its only operand: index `0` (`0x8(%rsp)`, 8 bytes) of
  `n_operands = 1` (`0x50(%rsp)`, 4 bytes): `argv = [prog]` gives the default operand `"-"`. -/
  argLast : m.readWith .read (sp + 8#64).toNat 8 = some (X86.Ext.leBytes 0#64 8) ∧
    m.readWith .read (sp + 0x50#64).toNat 4 = some (X86.Ext.leBytes 1#64 4)
  haveStdin : m.readWith .read 0x40a0a0 4 = some (X86.Ext.leBytes 1#64 4)
  prefixTag : m.readWith .read 0x409020 4 = some (X86.Ext.leBytes 0#64 4)
  delim : m.readWith .read 0x409014 1 = some [0x0a#8]
  binary : m.readWith .read 0x409010 4 = some (X86.Ext.leBytes 0#64 4)
  errError : m.readWith .read 0x412128 4 = some (X86.Ext.leBytes 0#64 4)
  obuf : Apps.Sha256sum.Stdout.Obuf m []

/-- **`digest_file`'s caller**, for the read loop's frame `e` (`digest_file`'s `rsp` after
its prologue): `cmain`'s `rsp` is `e.sp + 0xd0`; the six callee-saved registers pushed by the
prologue (`rbx` at `e.sp + 0x98` up to `r15` at `e.sp + 0xc0`) with `rbx = 0` (`do_check`)
and `r12` the operand `"-"` (the literal at `0x406052` in `.rodata`); the return address
`0x40419f` at `e.sp + 0xc8`; the frame readable up to `cmain`'s `rsp`; `rbp = r13` (both `0`
after `digest_file`'s comparison of the operand with `"-"`: the test `cmp %r13b,%bpl` at
`0x402fec` then skips `close`, since standard input is read); `out = bin[] = cmain's rsp + 0x70`
(`Digest.OutBuf`); and `CMain` at `cmain`'s `rsp`. -/
structure Caller (e : Loop) (m : Memory) : Prop where
  spRange : 0x420000 ≤ e.sp.toNat ∧ e.sp.toNat + 0x1000 < 2 ^ 64
  rbpR13 : e.rbp = e.r13
  frameR : m.Permitted .read (e.sp.toNat + 0x98) 0x38
  savedRbx : m.readWith .read (e.sp + 0x98#64).toNat 8 = some (encodeWords [0#64])
  savedRbp : ∃ v, m.readWith .read (e.sp + 0xa0#64).toNat 8 = some (encodeWords [v])
  savedR12 : m.readWith .read (e.sp + 0xa8#64).toNat 8 = some (encodeWords [0x406052#64]) ∧
    m.readWith .read 0x406052 2 = some [0x2d#8, 0#8]
  savedR13 : ∃ v, m.readWith .read (e.sp + 0xb0#64).toNat 8 = some (encodeWords [v])
  /-- `r14 = cmain's rsp + 0x90` (`missing`, `lea 0x90(%rsp),%r14` at `0x40397c`): the hex
  loop's end pointer (`HexEntry.r14`). -/
  savedR14 : m.readWith .read (e.sp + 0xb8#64).toNat 8 =
    some (encodeWords [e.sp + 0xd0#64 + 0x90#64])
  savedR15 : ∃ v, m.readWith .read (e.sp + 0xc0#64).toNat 8 = some (encodeWords [v])
  ret : m.readWith .read (e.sp + 0xc8#64).toNat 8 = some (encodeWords [0x40419f#64])
  cmain : CMain (e.sp + 0xd0#64) m

/-- `bin[]`, the caller's digest buffer: `cmain`'s `rsp + 0x70`. -/
def bin (e : Loop) : Word := e.sp + 0xd0#64 + 0x70#64

/-! ## Transport across writes elsewhere (VERIFIED) -/

theorem keep_read {m m' : Memory} {F : Nat → Prop} (hw : Memory.WritesWithin m m' F)
    {acc : Silmaril.Process.Access} {addr len : Nat} {v : Option (List Byte)}
    (hout : ∀ o < len, ¬ F (addr + o)) (h : m.readWith acc addr len = v) :
    m'.readWith acc addr len = v :=
  (hw.readWith hout).trans h

theorem Code.of_writes {m m' : Memory} {F : Nat → Prop} (hc : Apps.Sha256sum.Lift.Code m)
    (hw : Memory.WritesWithin m m' F) (hF : ∀ a, F a → 0x40a0c0 ≤ a) :
    Apps.Sha256sum.Lift.Code m' := by
  refine ⟨?_, fun a h1 h2 => by rw [hw.permits]; exact hc.ro a h1 h2⟩
  rw [hw.fetchBytes]; · exact hc.textAt
  intro o ho hin
  have := hF _ hin
  simp only [Apps.Sha256sum.Lift.textBase, Apps.Sha256sum.Lift.textSize] at ho this
  omega

theorem Obuf.of_writes {m m' : Memory} {F : Nat → Prop} (hc : Apps.Sha256sum.Stdout.Obuf m [])
    (hw : Memory.WritesWithin m m' F)
    (hF : ∀ a, F a → ¬ (0x412128 ≤ a ∧ a < 0x412138)) :
    Apps.Sha256sum.Stdout.Obuf m' [] := by
  refine ⟨hc.cap, ?_, ?_, ?_, (hw.permitted_iff _ _ _).mpr hc.olenW,
    (hw.permitted_iff _ _ _).mpr hc.obufW, (hw.permitted_iff _ _ _).mpr hc.obufR⟩
  · exact keep_read hw (fun o ho hin => hF _ hin (by omega)) hc.olen
  · exact keep_read hw (fun o ho => by simp at ho) hc.obuf
  · exact keep_read hw (fun o ho hin => hF _ hin (by omega)) hc.outError

/-- Where the read loop and `sha_final` may write, seen from `cmain`'s `rsp = sp`: the stack
from `.bss`'s end up to `digest_file`'s saved registers, `bin[]`, and `iobuf`. -/
def Scratch (sp : Word) (a : Nat) : Prop :=
  (0x413140 ≤ a ∧ a < sp.toNat - 0x38) ∨ (sp.toNat + 0x70 ≤ a ∧ a < sp.toNat + 0x90) ∨
    (0x40a0c0 ≤ a ∧ a < 0x4120c0)

theorem CMain.of_writes {sp : Word} {m m' : Memory} {F : Nat → Prop} (hc : CMain sp m)
    (hw : Memory.WritesWithin m m' F) (hF : ∀ a, F a → Scratch sp a) : CMain sp m' := by
  obtain ⟨hcode, htab, ⟨hb1, hb2⟩, hsr, hsw, hok, ⟨hi1, hi2⟩, hhs, hpt, hdl, hbn, hee,
    hob⟩ := hc
  have k : ∀ a, F a → (0x413140 ≤ a ∧ a < sp.toNat - 0x38) ∨
      (sp.toNat + 0x70 ≤ a ∧ a < sp.toNat + 0x90) ∨ (0x40a0c0 ≤ a ∧ a < 0x4120c0) := hF
  have e8 : (sp + 8#64).toNat = sp.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2c : (sp + 0x2c#64).toNat = sp.toNat + 0x2c := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e50 : (sp + 0x50#64).toNat = sp.toNat + 0x50 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨Code.of_writes hcode hw (fun a ha => by have := k a ha; omega),
    keep_read hw (fun o ho hin => by have := k _ hin; omega) htab, ⟨hb1, hb2⟩,
    (hw.permitted_iff _ _ _).mpr hsr, (hw.permitted_iff _ _ _).mpr hsw,
    keep_read hw (fun o ho hin => by have := k _ hin; rw [e2c] at this; omega) hok,
    ⟨keep_read hw (fun o ho hin => by have := k _ hin; rw [e8] at this; omega) hi1,
      keep_read hw (fun o ho hin => by have := k _ hin; rw [e50] at this; omega) hi2⟩,
    keep_read hw (fun o ho hin => by have := k _ hin; omega) hhs,
    keep_read hw (fun o ho hin => by have := k _ hin; omega) hpt,
    keep_read hw (fun o ho hin => by have := k _ hin; omega) hdl,
    keep_read hw (fun o ho hin => by have := k _ hin; omega) hbn,
    keep_read hw (fun o ho hin => by have := k _ hin; omega) hee,
    Obuf.of_writes hob hw (fun a ha h => by have := k a ha; omega)⟩

/-- What the read loop and `sha_final` may write, for the loop frame `e`. -/
def Free (e : Loop) (a : Nat) : Prop :=
  (e.sp.toNat - 400 ≤ a ∧ a < e.sp.toNat + 0x98) ∨
    (e.sp.toNat + 0x140 ≤ a ∧ a < e.sp.toNat + 0x160) ∨ (0x40a0c0 ≤ a ∧ a < 0x4120c0)

theorem Caller.of_writes {e : Loop} {m m' : Memory} {F : Nat → Prop} (hc : Caller e m)
    (hw : Memory.WritesWithin m m' F) (hF : ∀ a, F a → Free e a) : Caller e m' := by
  obtain ⟨⟨lo, hi⟩, hrbp, hfr, hsbx, ⟨vbp, hsbp⟩, ⟨hp1, hp3⟩, ⟨v13, hs13⟩,
    hs14, ⟨v15, hs15⟩, hret, hcm⟩ := hc
  have k : ∀ a, F a → (e.sp.toNat - 400 ≤ a ∧ a < e.sp.toNat + 0x98) ∨
      (e.sp.toNat + 0x140 ≤ a ∧ a < e.sp.toNat + 0x160) ∨ (0x40a0c0 ≤ a ∧ a < 0x4120c0) := hF
  have ex : ∀ c : Nat, c < 0x1000 → (e.sp + BitVec.ofNat 64 c).toNat = e.sp.toNat + c := by
    intro c hc; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨⟨lo, hi⟩, hrbp, (hw.permitted_iff _ _ _).mpr hfr,
    keep_read hw (fun o ho hin => by have := k _ hin; rw [ex _ (by omega)] at this; omega) hsbx,
    ⟨vbp, keep_read hw (fun o ho hin => by have := k _ hin; rw [ex _ (by omega)] at this; omega)
      hsbp⟩,
    ⟨keep_read hw (fun o ho hin => by have := k _ hin; rw [ex _ (by omega)] at this; omega)
      hp1, keep_read hw (fun o ho hin => by have := k _ hin; omega) hp3⟩,
    ⟨v13, keep_read hw (fun o ho hin => by have := k _ hin; rw [ex _ (by omega)] at this; omega)
      hs13⟩,
    keep_read hw (fun o ho hin => by have := k _ hin; rw [ex _ (by omega)] at this; omega)
      hs14,
    ⟨v15, keep_read hw (fun o ho hin => by have := k _ hin; rw [ex _ (by omega)] at this; omega)
      hs15⟩,
    keep_read hw (fun o ho hin => by have := k _ hin; rw [ex _ (by omega)] at this; omega) hret,
    hcm.of_writes hw fun a ha => ?_⟩
  have := k a ha
  show (0x413140 ≤ a ∧ a < (e.sp + 0xd0#64).toNat - 0x38) ∨
    ((e.sp + 0xd0#64).toNat + 0x70 ≤ a ∧ a < (e.sp + 0xd0#64).toNat + 0x90) ∨ _
  rw [ex _ (by omega)]; omega

/-! ## The read loop, recording end of file (VERIFIED) -/

theorem read_step_eof {prog : List Byte} {posix : Bool}
    {fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult} {message : List Byte} {e : Loop}
    {g : GS} {h : List Ev} (hd : HeadK e (world [prog] posix fs message) message g h) :
    Leads (GStep (world [prog] posix fs message)) (Ok message)
      (fun g' h' => AfterReadN e (stdinRead h) (world [prog] posix fs message) message g' h' ∧
        (stdinRead h' = stdinRead h → stdinRead h' = message)) g h := by
  obtain ⟨⟨ok, hl, hat⟩, K, hfd0⟩ := hd
  have hF := hat.2.1
  obtain ⟨t, r, hlvt, hlt, hsct, trap⟩ :=
    Apps.Sha256sum.Binary.Digest.ReadCall.head_runs ok.2.2.2.2.2 hl hat
  refine leads_seq (Apps.Sha256sum.X86Sys.reaches_rStep8 r) ok.1 ok ?_
  have ok1 : Ok message { g with x := t } h :=
    ⟨ok.1, ok.2.1, ok.2.2.1, ok.2.2.2.1, ok.2.2.2.2.1, hlvt⟩
  have lo := hF.spLow
  have e8 : (e.sp - 8#64).toNat = e.sp.toNat - 8 := Apps.Sha256sum.Binary.Digest.toNat_sp_sub lo (by decide)
  have hW1 : Silmaril.Process.Memory.WritesWithin g.x.memory t.memory
      (Apps.Sha256sum.Binary.Digest.ReadCall.callSpan e.sp) := by
    have := (Silmaril.Process.Memory.writesOnly_iff_writesWithin _ _ _ _).mp
      (Silmaril.Process.Memory.writeBytes_writesOnly trap.pushed)
    refine this.mono fun a ha => ?_
    rw [e8, Apps.Sha256sum.Binary.Digest.ReadCall.retBytes_length] at ha; exact .inl ⟨ha.1, by omega⟩
  have hiobufW : t.memory.Permitted .write Apps.Sha256sum.Binary.Digest.Update.iobuf.toNat 32768 :=
    (hW1.permitted_iff _ _ _).mpr hF.iobufW
  have hiobufR : t.memory.Permitted .read Apps.Sha256sum.Binary.Digest.Update.iobuf.toNat 32768 :=
    (hW1.permitted_iff _ _ _).mpr hF.iobufR
  have htrap : Trap t := by
    unfold Trap
    rw [trap.rip]
    have := Silmaril.X86.Ext.Loaded.fetchBytes_sub hsct (offset := 12) (len := 2) (by decide)
      (by decide)
    exact this
  refine leads_call (c := .read 0 32768) htrap ok.1 hlvt ok1 ?_ ?_ ?_ ?_
  · simp [Apps.Sha256sum.X86Sys.decode, trap.rax, trap.rdi, trap.rdx, hfd0,
      Apps.Sha256sum.X86Sys.fd32]
  · show t.memory.Permitted .write (({ t.core with rip := t.core.rip + 2 } :
      Silmaril.X86.State).read .rsi).toNat 32768
    rw [Silmaril.X86.Ext.read_with_rip, trap.rsi]; exact hiobufW
  · refine ⟨.data ((toSpec (message.drop (stdinRead h).length)).take 32768), _,
      WorldStep.readStdin K.fd0 K.stdin ⟨List.take_prefix _ _, by simp, fun hb => ?_⟩⟩
    rw [List.take_eq_nil_iff] at hb
    rcases hb with hb | hb
    · exact absurd hb (by decide)
    · exact .inl hb
  · intro rep k' r11 ws
    cases ws with
    | readStdinDir _ hst => rw [K.stdin] at hst; cases hst
    | readFile hfd _ => rw [K.fd0] at hfd; cases hfd
    | readPartial hfd _ _ _ => rw [K.fd0] at hfd; cases hfd
    | readFail hfd _ => rw [K.fd0] at hfd; cases hfd
    | readBad hb => rcases hb with hb | hb | hb <;> rw [K.fd0] at hb <;> cases hb
    | @readStdin _ _ _ b rest _ hst hch =>
      have hst' : rest = toSpec (message.drop (stdinRead h).length) := by
        have h1 := hst; simp only at h1; rw [K.stdin] at h1; cases h1; rfl
      subst hst'
      have hblen : b.length ≤ 32768 := hch.2.1
      have hcl : (b.map Apps.Sha256sum.X86Sys.ofU8).length = b.length := List.length_map _
      obtain ⟨m', hwm⟩ := writeBytes_some (bs := b.map Apps.Sha256sum.X86Sys.ofU8) hiobufW
        (by rw [hcl]; exact hblen)
      have hww : Silmaril.Process.Memory.WritesWithin t.memory m'
          (fun a => Apps.Sha256sum.Binary.Digest.Update.iobuf.toNat ≤ a ∧
            a < Apps.Sha256sum.Binary.Digest.Update.iobuf.toNat + 32768) := by
        have := (Silmaril.Process.Memory.writesOnly_iff_writesWithin _ _ _ _).mp
          (Silmaril.Process.Memory.writeBytes_writesOnly hwm)
        exact this.mono fun a ha => ⟨ha.1, by rw [hcl] at ha; omega⟩
      have hres : Apps.Sha256sum.X86Sys.resume (fun _ => r11) t
          { t.core with rip := t.core.rip + 2 } (.read 0 32768) (.data b) =
          { t with core := (Apps.Sha256sum.X86Sys.returnCore (fun _ => r11)
              ({ t.core with rip := t.core.rip + 2 } : Silmaril.X86.State)
              (BitVec.ofNat 64 b.length)), memory := m' } := by
        simp only [Apps.Sha256sum.X86Sys.resume, Silmaril.X86.Ext.read_with_rip, trap.rsi, hwm]
        rfl
      have hres' : Apps.Sha256sum.X86Sys.resume (fun _ => r11) ({ x := t, k := g.k, exited := g.exited } : GS).x
          (trapped { x := t, k := g.k, exited := g.exited }) (Call.read 0 32768) (Ret.data b) =
          { t with core := (Apps.Sha256sum.X86Sys.returnCore (fun _ => r11)
              ({ t.core with rip := t.core.rip + 2 } : Silmaril.X86.State)
              (BitVec.ofNat 64 b.length)), memory := m' } := hres
      rw [hres']
      have hchunk : m'.readBytes Apps.Sha256sum.Binary.Digest.Update.iobuf.toNat
          (b.map Apps.Sha256sum.X86Sys.ofU8).length = some (b.map Apps.Sha256sum.X86Sys.ofU8) :=
        Apps.Sha256sum.Lift.readWith_wb_same hwm (permitted_prefix hiobufR (by rw [hcl]; exact hblen))
      have hsc' : Loaded m' Apps.Sha256sum.Binary.Sc3.base Apps.Sha256sum.Binary.Sc3.code := by
        unfold Loaded; rw [hww.fetchBytes]
        · exact hsct
        intro o ho hin
        simp only [Apps.Sha256sum.Binary.Digest.sc3_length,
          Apps.Sha256sum.Binary.Digest.sc3_toNat, Apps.Sha256sum.Binary.Digest.iobuf_toNat] at ho hin
        omega
      obtain ⟨v, r2, hlv2, hl2, hafter⟩ :=
        Apps.Sha256sum.Binary.Digest.ReadCall.afterRead_of_reply (u := { t with
          core := (Apps.Sha256sum.X86Sys.returnCore (fun _ => r11)
              ({ t.core with rip := t.core.rip + 2 } : Silmaril.X86.State)
              (BitVec.ofNat 64 b.length)), memory := m' })
          hl hat trap hlvt hsc'
          hww hchunk (by rw [hcl]; exact hblen)
          (by rw [returnCore_rip]; show t.core.rip + 2 = _; rw [trap.rip]; decide)
          (by rw [returnCore_rax, hcl])
          (by rw [returnCore_other _ _ _ _ (by decide) (by decide) (by decide),
                Silmaril.X86.Ext.read_with_rip])
          (by rw [returnCore_other _ _ _ _ (by decide) (by decide) (by decide),
                Silmaril.X86.Ext.read_with_rip])
          (by rw [returnCore_other _ _ _ _ (by decide) (by decide) (by decide),
                Silmaril.X86.Ext.read_with_rip])
          (by rw [returnCore_other _ _ _ _ (by decide) (by decide) (by decide),
                Silmaril.X86.Ext.read_with_rip])
      have hpre : stdinRead h ++ b.map UInt8.toBitVec <+: message := by
        have h1 := List.prefix_iff_eq_append.mp ok.2.2.1
        have h2 : b.map UInt8.toBitVec <+: message.drop (stdinRead h).length := by
          have := hch.1.map UInt8.toBitVec
          rwa [toBitVec_toSpec] at this
        have h3 := (List.prefix_append_right_inj (stdinRead h)).mpr h2
        rwa [h1] at h3
      have hallowed : ∀ ev ∈ h ++ [Ev.sys (Call.read 0 32768) (Ret.data b)], Allowed ev := by
        intro ev hev
        rcases List.mem_append.mp hev with hev | hev
        · exact ok.2.1 _ hev
        · simp only [List.mem_singleton] at hev; subst hev
          exact ⟨rfl, by decide, b, rfl⟩
      have hK : ∀ (y : XState), StdinK message
          ⟨y, { fds := g.k.fds, stdin := Apps.Sha256sum.Stdin.bytes (List.drop (List.length b)
            (toSpec (List.drop (stdinRead h).length message))) }, none⟩
          (h ++ [Ev.sys (Call.read 0 32768) (Ret.data b)]) := by
        intro y
        refine ⟨K.fd0, K.fd1, K.fd2, ?_, by rw [out_snoc_read]; exact K.quiet⟩
        simp only [stdinRead_snoc_data, List.length_append, List.length_map, toSpec,
          ← List.map_drop, List.drop_drop]
      have ok2 : ∀ (y : XState), y.faulted = false → Ok message
          ⟨y, { fds := g.k.fds, stdin := Apps.Sha256sum.Stdin.bytes (List.drop (List.length b)
            (toSpec (List.drop (stdinRead h).length message))) }, none⟩
          (h ++ [Ev.sys (Call.read 0 32768) (Ret.data b)]) := fun y hy =>
        ⟨rfl, hallowed, by rw [stdinRead_snoc_data]; exact hpre,
          by rw [out_snoc_read]; exact ok.2.2.2.1, .inl (by rw [out_snoc_read]; exact K.quiet), hy⟩
      refine leads_seq (Apps.Sha256sum.X86Sys.reaches_rStep8 r2) rfl (ok2 _ hlvt)
        (.done ⟨?_, ?_⟩)
      · refine ⟨ok2 v hlv2, hl2, hK v, hfd0, b.map Apps.Sha256sum.X86Sys.ofU8, ?_, hafter⟩
        rw [stdinRead_snoc_data, map_ofU8]
      · intro heq
        rw [stdinRead_snoc_data] at heq ⊢
        have hb0 : b = [] := by simpa using heq
        subst hb0
        rcases hch.2.2 rfl with hr | hr
        · simp only [toSpec, List.map_eq_nil_iff, List.drop_eq_nil_iff] at hr
          simp only [List.map_nil, List.append_nil]
          exact ok.2.2.1.eq_of_length (Nat.le_antisymm ok.2.2.1.length_le hr)
        · exact absurd hr (by decide)

/-- **VERIFIED.** `ReadLoop.update_step`, carrying end of file to the padding. -/
theorem update_step_eof {w : Apps.Sha256sum.World} {message : List Byte} {e : Loop}
    {consumed : List Byte} {g : GS} {h : List Ev} (ha : AfterReadN e consumed w message g h)
    (hx : stdinRead h = consumed → stdinRead h = message) :
    Leads (GStep w) (Ok message)
      (fun g' h' => (HeadK e w message g' h' ∧ consumed.length < (stdinRead h').length) ∨
        (PadK e w message g' h' ∧ stdinRead h' = message)) g h := by
  obtain ⟨ok, hl, K, hfd0, chunk, hread, after⟩ := ha
  obtain ⟨t, hrun, hlv', hl', hpost⟩ :=
    Apps.Sha256sum.Binary.Digest.update_absorbs ok.2.2.2.2.2 hl after
  have ok' : Ok message { g with x := t } h :=
    ⟨ok.1, ok.2.1, ok.2.2.1, ok.2.2.2.1, ok.2.2.2.2.1, hlv'⟩
  have K' : StdinK message { g with x := t } h := ⟨K.fd0, K.fd1, K.fd2, K.stdin, K.quiet⟩
  refine leads_of_reaches (Apps.Sha256sum.X86Sys.reaches_rStep8 hrun) ok.1 ok ?_
  rcases hpost with ⟨head, hne⟩ | ⟨rfl, pad⟩
  · refine .inl ⟨⟨⟨ok', hl', by rw [hread]; exact head⟩, K', hfd0⟩, ?_⟩
    rw [hread, List.length_append]
    have := List.length_pos_of_ne_nil hne
    omega
  · exact .inr ⟨⟨⟨ok', hl', by rw [hread, List.append_nil]; exact pad⟩, K', hfd0⟩,
      hx (by rw [hread, List.append_nil])⟩

/-- **VERIFIED.** `ReadLoop.loop_leads`, reaching the padding with the whole message read. -/
theorem loop_leads_eof {prog : List Byte} {posix : Bool}
    {fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult} {message : List Byte} {e : Loop} :
    ∀ (left : Nat) (g : GS) (h : List Ev), message.length - (stdinRead h).length = left →
      HeadK e (world [prog] posix fs message) message g h →
      Leads (GStep (world [prog] posix fs message)) (Ok message)
        (fun g' h' => PadK e (world [prog] posix fs message) message g' h' ∧
          stdinRead h' = message) g h := by
  intro left
  induction left using Nat.strong_induction_on with
  | _ left ih =>
  intro g h hleft hd
  refine (read_step_eof hd).trans fun g1 h1 ⟨a1, x1⟩ => (update_step_eof a1 x1).trans
    fun g2 h2 post => ?_
  rcases post with ⟨hd2, more⟩ | pad
  · have hle : (stdinRead h2).length ≤ message.length := hd2.1.1.2.2.1.length_le
    exact ih _ (by omega) g2 h2 rfl hd2
  · exact .done pad

/-- **The cut `Digested`** (`0x40310a`, after `sha_final`): `Ok`; the whole message read and
nothing written; descriptors 0, 1, 2 the standard streams, standard input at end of file;
for some loop frame `e` (descriptor slot `0`): `Digest.AtOut e message (bin e)` (the
32 bytes of `bin[]` are `SHA256.digest message`, `rsp`/`rbp`/`r13` of the frame, the code
regions), and `Caller e`. -/
def Digested : Cut := fun _ message g h =>
  Ok message g h ∧ stdinRead h = message ∧ out h = [] ∧ KTail g ∧
    ∃ e : Loop, e.fd = 0 ∧ AtOut e message (bin e) g.x ∧ Caller e g.x.memory

/-! ## The final segment (VERIFIED) -/

/-- What the startup fixes at the read loop's entry (the memory `e.m0` that
`LoopFrame.keep` is relative to), kept by the loop: `Caller e`, and `digest_file`'s `out`
slot (`[sp + 0x10]`) holding `bin e`. -/
def Entry (e : Loop) : Prop :=
  Caller e e.m0 ∧ loadN e.m0 (e.sp + 0x10#64) 8 = some (bin e)

/-- The read loop's head with `Entry` (the startup's target). -/
def AtLoopHeadW : Cut := fun w message g h => ∃ e, HeadK e w message g h ∧ Entry e

/-- The read loop's padding with the whole message read and `Entry`. -/
def AtLoopPadW : Cut := fun w message g h =>
  ∃ e, (PadK e w message g h ∧ stdinRead h = message) ∧ Entry e

/-- **VERIFIED. The read loop**, from `AtLoopHeadW` to `AtLoopPadW` (`loop_leads_eof`). -/
theorem readLoopW (domain : List Byte → Prop) : Seg domain AtLoopHeadW AtLoopPadW := by
  intro prog posix fs message g h _ ⟨e, hd, he⟩
  exact (loop_leads_eof _ g h rfl hd).trans fun g' h' pad => .done ⟨e, pad, he⟩

theorem loaded_final {m : Memory} (hc : Apps.Sha256sum.Lift.Code m) :
    Loaded m Apps.Sha256sum.Binary.Digest.Final.base Apps.Sha256sum.Binary.Digest.Final.code := by
  unfold Loaded
  rw [Apps.Sha256sum.Binary.Digest.Final.code_length]
  have := hc.fetch (a := 0x403034) (n := 570) (by decide) (by decide) (by decide)
  exact this.trans (congrArg some Apps.Sha256sum.Binary.Digest.Final.seg1_code)

open Silmaril.Apps.Sha256sum.Binary.Digest in
open Silmaril.Crypto.X86.Sha256O2 (compressBlock) in
set_option maxRecDepth 100000 in
/-- **VERIFIED.** `Digest.final_digest`, also giving what `sha_final` wrote
(`Final.finSpan`: the callee frames below `sp`, `[sp + 0x18, sp + 0x88)`, the buffer). -/
theorem final_digest_w {e : Loop} {consumed : List Byte} {s : XState} {out : Word}
    (hlv : s.faulted = false) (hl : Loaded s.memory Final.base Final.code)
    (hl0 : Loaded s.memory base code) (h : AtPad e consumed s) (hout : OutBuf s.memory e.sp out) :
    ∃ t, Silmaril.Machine.Execution.Reaches Apps.Sha256sum.X86Sys.rStep8 s t ∧
      t.faulted = false ∧ AtOut e consumed out t ∧
      Memory.WritesWithin s.memory t.memory (fun a =>
        (e.sp.toNat - 400 ≤ a ∧ a < e.sp.toNat) ∨ (e.sp.toNat + 0x18 ≤ a ∧ a < e.sp.toNat + 0x88) ∨
          (out.toNat ≤ a ∧ a < out.toNat + 32)) := by
  obtain ⟨hrip, hF, hdx, blocks, tail, hr, hb⟩ := h
  let c : Final.Ctx := ⟨e.sp, out, blocks.foldl compressBlock IV, tail,
    BitVec.ofNat 64 consumed.length, s.core.read, s.memory⟩
  have hg : Final.Geo c := ⟨hF.spAlign, hF.spLow, hF.spHigh, hF.stackW, hF.stackR, hF.code,
    hF.kTable, hl, hout.slot, hout.writable, hout.readable, hout.low, hout.high, hout.apart,
    hb.hRoom⟩
  have hpre : Final.pre c s :=
    ⟨⟨hF.rsp, rfl, rfl, Memory.WritesWithin.refl _ _⟩, rfl, hdx, hb.hState, hb.hTail,
      hb.hBlen⟩
  have hrip0 : s.core.rip = Final.base + BitVec.ofNat 64 0 := by rw [hrip]; rfl
  obtain ⟨t, hrun, hlv', hlt, hript, ⟨hFt, sb, hsb, hst, hdig⟩⟩ :=
    Final.final_runs c hg s hlv hl hrip0 hpre
  refine ⟨t, hrun, hlv', ⟨hript, hFt.rsp, hFt.rbp.trans hF.rbp, hFt.r13.trans hF.r13, ?_,
    Final.ccode_of_writes hg hFt.writes, Final.kTable_of_writes hg hFt.writes, ?_, hlt⟩,
    hFt.writes⟩
  · rw [hdig, outBytes_digest sb consumed (by rw [hst]; exact hfin_hash hr)]
  · unfold Loaded; rw [hFt.writes.fetchBytes]; · exact hl0
    intro o ho hin; have := hg.codeApart hin
    rw [Update.code_length] at ho; rw [Update.base_toNat] at this; omega

/-- **VERIFIED. The final segment**: from the padding with the whole message read and
`Entry`, `sha_final` (`Digest.Final.final_runs`, retiring steps of the `Ext8` machine, moved
to `GStep` with any `r11` by `leads_of_reaches`) reaches `Digested`. -/
theorem finalW (domain : List Byte → Prop) : Seg domain AtLoopPadW Digested := by
  intro prog posix fs message g h _ ⟨e, ⟨⟨⟨ok, hl0, pad⟩, K, hfd⟩, hall⟩, hc0, hslot0⟩
  have hF := pad.2.1
  have lo := hF.spLow
  have hi := hF.spHigh
  have ex : ∀ c : Nat, c < 0x1000 → (e.sp + BitVec.ofNat 64 c).toNat = e.sp.toNat + c := by
    intro c hc; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hc : Caller e g.x.memory := hc0.of_writes hF.keep fun a ha => by
    simp only [Apps.Sha256sum.Binary.Digest.loopSpan, Apps.Sha256sum.Binary.Digest.Update.stackSpan,
      Apps.Sha256sum.Binary.Digest.iobuf_toNat] at ha
    simp only [Free]; omega
  have hslot : loadN g.x.memory (e.sp + 0x10#64) 8 = some (bin e) := by
    rw [Apps.Sha256sum.Binary.Digest.loadN_transfer hF.keep]; · exact hslot0
    intro o ho hin
    rw [ex _ (by omega)] at hin
    simp only [Apps.Sha256sum.Binary.Digest.loopSpan, Apps.Sha256sum.Binary.Digest.Update.stackSpan,
      Apps.Sha256sum.Binary.Digest.iobuf_toNat] at hin
    omega
  have ebin : (bin e).toNat = e.sp.toNat + 0x140 := by
    simp only [bin, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ecs : (e.sp + 0xd0#64).toNat = e.sp.toNat + 0xd0 := ex _ (by omega)
  have hsw := hc.cmain.stackW
  have hsr := hc.cmain.stackR
  rw [ecs] at hsw hsr
  have hout : OutBuf g.x.memory e.sp (bin e) :=
    ⟨hslot, Silmaril.X86.Ext.Memory.Permitted.sub hsw (by decide) (by rw [ebin]; omega) (by rw [ebin]; omega),
      Silmaril.X86.Ext.Memory.Permitted.sub hsr (by decide) (by rw [ebin]; omega) (by rw [ebin]; omega), by rw [ebin]; omega,
      by rw [ebin]; omega, .inr (by rw [ebin]; omega)⟩
  have pad' : AtPad e message g.x := hall ▸ pad
  obtain ⟨t, hrun, hlv', hat, hw⟩ :=
    final_digest_w ok.2.2.2.2.2 (loaded_final hc.cmain.code) hl0 pad' hout
  have ok' : Ok message { g with x := t } h :=
    ⟨ok.1, ok.2.1, ok.2.2.1, ok.2.2.2.1, ok.2.2.2.2.1, hlv'⟩
  refine leads_of_reaches hrun ok.1 ok ⟨ok', hall, K.quiet, ⟨K.fd0, K.fd1, K.fd2, ?_⟩, e, hfd,
    hat, hc.of_writes hw fun a ha => ?_⟩
  · rw [K.stdin, hall, List.drop_length]; rfl
  · rw [ebin] at ha; simp only [Free]; omega

/-- **The cut `Formatted`** (`0x40464d`, back in `cmain` after the record, before the operand
loop's exit and `close(0)`): `Stdout.FormattedCut` of `gnu-r3-output`. The record's `'\n'`
(`digest_delim`) `out_putc` flushes the output layer, so the 68 bytes `hex ++ "  -\n"` are
**all written** (`out h = expected message`, `olen = 0`, `out_error = 0`), the whole message
read, `ok = 1`, `have_read_stdin = 1`, `err_error = 0`, operand index `0` of `1`,
descriptors 0, 1, 2 open (`Stdout.AtFormatted`). -/
def Formatted : Cut := Apps.Sha256sum.Stdout.FormattedCut

/-- **VERIFIED. The exit segment**: `Stdout.exitSegment` of `gnu-r3-output` (`close(0)`,
`close_stdout`, `exit_group(0)`, any `r11`). -/
theorem exitW (domain : List Byte → Prop) : Seg domain Formatted DoneCut :=
  Apps.Sha256sum.Stdout.exitSegment domain

/-! ## The release theorems from the remaining segments (VERIFIED) -/

/-- **The segments still open, against the wired cuts**: `Release.Open` with the read loop's
cuts strengthened (`AtLoopHeadW`: `Entry`, i.e. the caller's frame and `cmain`'s state at
the loop's entry; `AtLoopPadW`: also the whole message read, which `Release.AtLoopPad`
does not record), with `final` (`finalW`) and `exit` (`exitW`) discharged. -/
structure OpenW : Prop where
  startup : Seg (fun _ => True) LaunchCut AtLoopHeadW
  format : Seg (fun _ => True) Digested Formatted

/-- **`sys-total` from `OpenW`** (VERIFIED; the read loop by `readLoopW`, `final` by
`finalW`, `exit` by `exitW`). -/
theorem sysTotal_of_W (o : OpenW) : Registry.sysTotal :=
  sysTotalOn_of_segments o.startup (readLoopW _) (finalW _) o.format (exitW _)

/-- `lps-total` from `OpenW` (VERIFIED; `lps-bridge` is solved). -/
theorem lpsTotal_of_W (o : OpenW) : Registry.lpsTotal :=
  Registry.lpsTotal_of (sysTotal_of_W o) Registry.lpsBridge_solution

/-- `lps-bounded-1024` from `OpenW` (VERIFIED). -/
theorem lpsBounded_of_W (o : OpenW) : Registry.lpsBounded :=
  Registry.lpsBounded_link ⟨lpsTotal_of_W o, trivial⟩

/-- `lps-partial` from `OpenW` (VERIFIED). -/
theorem lpsPartial_of_W (o : OpenW) : Registry.lpsPartial :=
  Registry.lpsPartial_link ⟨lpsTotal_of_W o, trivial⟩

/-- `agree-sha256-cli` from `OpenW` (VERIFIED). -/
theorem agree_of_W (o : OpenW) : Registry.agree :=
  Registry.agree_of_lpsTotal (lpsTotal_of_W o)

end Silmaril.Process.LPS.Problems.GnuSha256sum.Wire

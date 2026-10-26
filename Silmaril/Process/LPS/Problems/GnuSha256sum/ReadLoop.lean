module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.DigestLoop
public import Silmaril.Process.LPS.Problems.GnuSha256sum.SysGlue
public import Silmaril.Process.LPS.Problems.GnuSha256sum.ReadWrite
public import Silmaril.Apps.Sha256sum.Binary.Digest.ReadCall

/-! # The read loop of `digest_file` as a `GStep` segment

`ReadLoopSegment` of the stdin tier, between the loop head and the padding:

* `StdinK`: the kernel side during the loop: descriptors 0, 1, 2 open on standard input,
  output and error, standard input holding the message after the bytes read so far, and
  nothing written yet;
* `HeadK e`, `PadK e`: `DigestLoop.HeadCut`/`PadCut` with `StdinK` and the descriptor slot
  `0` (the stdin tier reads descriptor 0); `AfterReadN e consumed`: `AfterReadCut` with
  `StdinK`, where the bytes consumed before the last `read` are `consumed`;
* `read_step` (VERIFIED): from `HeadK e`, across `sc3`'s `read(0, iobuf, 32768)` with every
  reply the kernel allows and every `r11`, to `AfterReadN e (stdinRead h)`;
* `update_step` (VERIFIED): from `AfterReadN e consumed` to `HeadK e` with more than
  `consumed.length` bytes read,
  or to `PadK e` (`Digest.update_absorbs`: a nonempty chunk returns to the head);
* `readLoopSeg` (VERIFIED): `ReadLoopSegment domain (AtLoopHead) (AtLoopPad)` for every
  domain, by induction on the bytes left in the message.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.X86Sys (XState Core)
open Silmaril.Apps.Sha256sum.Sys (Call Ret KState WorldStep Src Chunk)
open Silmaril.Apps.Sha256sum.Binary.Digest (Loop AfterRead AtHead AtPad LoopFrame)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)
open Silmaril.X86.Ext (Loaded)

/-- The kernel side of the stdin tier during the read loop. -/
structure StdinK (message : List Byte) (g : GS) (h : List Ev) : Prop where
  fd0 : g.k.fds 0 = some .stdin
  fd1 : g.k.fds 1 = some .stdout
  fd2 : g.k.fds 2 = some .stderr
  stdin : g.k.stdin = .bytes (toSpec (message.drop (stdinRead h).length))
  quiet : out h = []

/-- The loop head, with the kernel side, reading descriptor 0. -/
def HeadK (e : Loop) : Cut := fun w message g h =>
  HeadCut e w message g h ∧ StdinK message g h ∧ e.fd = 0

/-- The padding, with the kernel side. -/
def PadK (e : Loop) : Cut := fun w message g h =>
  PadCut e w message g h ∧ StdinK message g h ∧ e.fd = 0

/-- After a `read`, with the kernel side; the bytes consumed before it are `consumed`. -/
def AfterReadN (e : Loop) (consumed : List Byte) : Cut := fun _ message g h =>
  Ok message g h ∧ Loaded g.x.memory Apps.Sha256sum.Binary.Digest.base
    Apps.Sha256sum.Binary.Digest.code ∧ StdinK message g h ∧ e.fd = 0 ∧
    ∃ chunk, stdinRead h = consumed ++ chunk ∧ AfterRead e consumed chunk g.x

/-- Some loop head (the cut `ReadLoopSegment` starts from). -/
def AtLoopHead : Cut := fun w message g h => ∃ e, HeadK e w message g h

/-- Some padding (the cut `ReadLoopSegment` ends at). -/
def AtLoopPad : Cut := fun w message g h => ∃ e, PadK e w message g h

/-! ## Small facts -/

theorem ofU8_eq_toBitVec (b : UInt8) : Apps.Sha256sum.X86Sys.ofU8 b = b.toBitVec := by
  simp [Apps.Sha256sum.X86Sys.ofU8]

theorem map_ofU8 (b : List UInt8) : b.map Apps.Sha256sum.X86Sys.ofU8 = b.map UInt8.toBitVec :=
  List.map_congr_left fun x _ => ofU8_eq_toBitVec x

theorem stdinRead_snoc_data (h : List Ev) (n : Nat) (b : List UInt8) :
    stdinRead (h ++ [.sys (.read 0 n) (.data b)]) = stdinRead h ++ b.map UInt8.toBitVec := by
  simp [stdinRead, readBytes]

theorem out_snoc_read (h : List Ev) (n : Nat) (r : Ret) :
    out (h ++ [.sys (.read 0 n) r]) = out h := by
  simp [out, outBytes]

theorem permitted_prefix {m : Silmaril.Process.Memory} {acc : Silmaril.Process.Access}
    {a n k : Nat} (h : m.Permitted acc a n) (hk : k ≤ n) : m.Permitted acc a k := by
  unfold Silmaril.Process.Memory.Permitted at h ⊢
  rw [Silmaril.Process.Memory.checkSpan_iff] at h ⊢
  exact ⟨h.1, by omega, fun o ho => h.2.2 o (by omega)⟩

theorem writeBytes_some {m : Silmaril.Process.Memory} {a n : Nat} {bs : List Byte}
    (h : m.Permitted .write a n) (hk : bs.length ≤ n) : ∃ m', m.writeBytes a bs = some m' := by
  have := permitted_prefix h hk
  unfold Silmaril.Process.Memory.Permitted at this
  exact ⟨{ m with bytes := Silmaril.Process.Memory.install m.bytes a bs }, by
    unfold Silmaril.Process.Memory.writeBytes; simp only [this, ↓reduceIte]⟩


theorem returnCore_rip (f : Core → Silmaril.X86.Word) (c : Core) (v : Silmaril.X86.Word) :
    (Apps.Sha256sum.X86Sys.returnCore f c v).rip = c.rip := rfl

theorem returnCore_rax (f : Core → Silmaril.X86.Word) (c : Core) (v : Silmaril.X86.Word) :
    (Apps.Sha256sum.X86Sys.returnCore f c v).read .rax = v := by
  simp [Apps.Sha256sum.X86Sys.returnCore, Silmaril.X86.State.read_write_other,
    Silmaril.X86.State.read_write_same]

theorem returnCore_other (f : Core → Silmaril.X86.Word) (c : Core) (v : Silmaril.X86.Word)
    (r : Silmaril.X86.Reg) (h1 : r ≠ .r11) (h2 : r ≠ .rcx) (h3 : r ≠ .rax) :
    (Apps.Sha256sum.X86Sys.returnCore f c v).read r = c.read r := by
  simp only [Apps.Sha256sum.X86Sys.returnCore]
  rw [Silmaril.X86.State.read_write_other _ _ _ _ h1, Silmaril.X86.State.read_write_other _ _ _ _ h2,
    Silmaril.X86.State.read_write_other _ _ _ _ h3]

/-! ## One `read` -/

/-- **VERIFIED. The system-call half of a loop iteration.** From the loop head, across
`read(0, iobuf, 32768)` through `sc3` (every reply the kernel of the world allows, every
`r11`), every execution keeps `Ok` and reaches `AfterReadN e n`, `n` the bytes read so far. -/
theorem read_step {prog : List Byte} {posix : Bool}
    {fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult} {message : List Byte} {e : Loop}
    {g : GS} {h : List Ev} (hd : HeadK e (world [prog] posix fs message) message g h) :
    Leads (GStep (world [prog] posix fs message)) (Ok message)
      (AfterReadN e (stdinRead h) (world [prog] posix fs message) message) g h := by
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
      refine leads_seq (Apps.Sha256sum.X86Sys.reaches_rStep8 r2) rfl (ok2 _ hlvt) (.done ?_)
      refine ⟨ok2 v hlv2, hl2, hK v, hfd0, b.map Apps.Sha256sum.X86Sys.ofU8, ?_, hafter⟩
      rw [stdinRead_snoc_data, map_ofU8]


/-! ## One iteration's hashing, and the loop -/

/-- **VERIFIED. The hashing half of a loop iteration**, with the kernel side: from
`AfterReadN e n`, to the loop head with more than `n` bytes read, or to the padding. -/
theorem update_step {w : Apps.Sha256sum.World} {message : List Byte} {e : Loop}
    {consumed : List Byte} {g : GS} {h : List Ev} (ha : AfterReadN e consumed w message g h) :
    Leads (GStep w) (Ok message)
      (fun g' h' => (HeadK e w message g' h' ∧ consumed.length < (stdinRead h').length) ∨
        PadK e w message g' h') g h := by
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
  · exact .inr ⟨⟨ok', hl', by rw [hread, List.append_nil]; exact pad⟩, K', hfd0⟩

/-- **VERIFIED. The read loop**, on one world: from a loop head, every execution keeps `Ok`
and reaches the padding (induction on the bytes left in the message: each iteration that
returns to the head has read a nonempty chunk). -/
theorem loop_leads {prog : List Byte} {posix : Bool}
    {fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult} {message : List Byte} {e : Loop} :
    ∀ (left : Nat) (g : GS) (h : List Ev), message.length - (stdinRead h).length = left →
      HeadK e (world [prog] posix fs message) message g h →
      Leads (GStep (world [prog] posix fs message)) (Ok message)
        (PadK e (world [prog] posix fs message) message) g h := by
  intro left
  induction left using Nat.strong_induction_on with
  | _ left ih =>
  intro g h hleft hd
  refine (read_step hd).trans fun g1 h1 a1 => (update_step a1).trans fun g2 h2 post => ?_
  rcases post with ⟨hd2, more⟩ | pad
  · have hle : (stdinRead h2).length ≤ message.length := hd2.1.1.2.2.1.length_le
    exact ih _ (by omega) g2 h2 rfl hd2
  · exact .done pad

/-- **VERIFIED. `ReadLoopSegment`** from some loop head to some padding, for every domain. -/
theorem readLoopSeg (domain : List Byte → Prop) :
    ReadLoopSegment domain AtLoopHead AtLoopPad := by
  intro prog posix fs message g h _ ⟨e, hd⟩
  exact (loop_leads _ g h rfl hd).trans fun g' h' pad => .done ⟨e, pad⟩


/-! ## In the integrator's form (`SysTotal.ReadCall _ StdinJ` on `gnu-release`) -/

/-- **VERIFIED. The system-call half of an iteration, in the shape of
`SysTotal.ReadCall domain StdinJ`** (`gnu-release`), with `StdinJ e` unfolded: from the loop
head with the standard invariant, every execution keeps `Ok` and reaches `0x402f06` right
after the `read`, having read exactly `chunk`, the struct holding what was read before, with
the invariant kept. -/
theorem readCall_stdin (e : Loop) (prog : List Byte) (posix : Bool)
    (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult) (message : List Byte) (g : GS)
    (h : List Ev) (head : HeadCut e (world [prog] posix fs message) message g h)
    (j : e.fd = 0#64 ∧ g.k.fds 0 = some .stdin ∧ g.k.fds 1 = some .stdout ∧
      g.k.fds 2 = some .stderr ∧
      g.k.stdin = .bytes (toSpec (message.drop (stdinRead h).length)) ∧ out h = []) :
    Leads (GStep (world [prog] posix fs message)) (Ok message)
      (fun g' h' => ∃ chunk, stdinRead h' = stdinRead h ++ chunk ∧
        (Ok message g' h' ∧ Loaded g'.x.memory Apps.Sha256sum.Binary.Digest.base
          Apps.Sha256sum.Binary.Digest.code ∧ AfterRead e (stdinRead h) chunk g'.x) ∧
        (e.fd = 0#64 ∧ g'.k.fds 0 = some .stdin ∧ g'.k.fds 1 = some .stdout ∧
          g'.k.fds 2 = some .stderr ∧
          g'.k.stdin = .bytes (toSpec (message.drop (stdinRead h').length)) ∧ out h' = []))
      g h := by
  obtain ⟨fd, f0, f1, f2, st, q⟩ := j
  refine (read_step ⟨head, ⟨f0, f1, f2, st, q⟩, fd⟩).trans fun g' h' a => .done ?_
  obtain ⟨ok, hl, K, _, chunk, hread, after⟩ := a
  exact ⟨chunk, hread, ⟨ok, hl, after⟩, fd, K.fd0, K.fd1, K.fd2, K.stdin, K.quiet⟩

end Silmaril.Process.LPS.Problems.GnuSha256sum

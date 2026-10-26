module

public import Silmaril.Apps.Sha256sum.Binary.Digest.Update
public import Silmaril.Crypto.X86.Sha256O2.Reference
public import Silmaril.Process.CLI.Sha256Cli.Driver
public import Silmaril.Apps.Sha256sum.Binary.Sc3

/-! # The read loop of `digest_file`, against the SHA-256 specification

`Digest.Update` speaks of the `struct sha` as the machine sees it: the chaining value of a
list of 64-byte blocks (`Sha256O2.compressBlock`, the pilot contract's compression) and a
buffered tail. This module states the loop's cut points in terms of **the bytes consumed so
far**, and ties the chaining value to Silmaril's SHA-256 specification
(`Crypto.SHA256.processBlock`, via `Sha256Cli.Driver.StreamInv`, whose `final_hash` gives
`Crypto.SHA256.hash` once the padded blocks are folded):

* `Absorbed m sp consumed`: the struct at `sp` holds `consumed`: its full blocks folded from
  the standard initial value `IV`, the rest buffered, and the total `consumed.length`;
* `Absorbed.stream`: then the chaining value, read as a specification state, is
  `blocks.foldl Driver.compressBlock SHA256.H0` over the full blocks of `consumed`, with
  `consumed = blocks.flatten ++ tail` (`Driver.StreamInv`): **the hash state is the SHA-256
  fold over the bytes consumed so far**;
* the three cut points of one loop iteration, on `X86Sys` states: `AfterRead` (at
  `0x402f06`, `read` returned a chunk), `AtHead` (the loop head `0x402ef0`, before the next
  `read`), `AtPad` (`0x403034`, the padding after `read` returned 0);
* `update_absorbs` (VERIFIED): `AfterRead consumed chunk` reaches, by retiring steps,
  `AtHead (consumed ++ chunk)` with a nonempty chunk, or for an empty chunk `AtPad consumed`.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Crypto.X86.Sha256O2 (StateHolds compressBlock)
open Silmaril.Crypto.SHA256.Kernel (InitHash)
open Silmaril.Process.CLI.Sha256Cli (Driver.ReadInv Driver.StreamInv)
open Update (Buf iobuf)

/-- The SHA-256 initial hash value (FIPS 180-4 §5.3.3), as the machine's `InitHash`. -/
def IV : InitHash := Silmaril.Crypto.SHA256.State.toInitHash Silmaril.Crypto.SHA256.H0

theorem IV_toState : IV.toState = Silmaril.Crypto.SHA256.H0 := rfl

/-- The machine's compression fold, read as a specification state, is the specification's
fold (`Sha256O2.compressBlock_toState`, block by block). -/
theorem fold_toState :
    ∀ (blocks : List (List Byte)) (H : InitHash), (∀ b ∈ blocks, b.length = 64) →
      (blocks.foldl compressBlock H).toState =
        blocks.foldl Silmaril.Process.CLI.Sha256Cli.Driver.compressBlock H.toState
  | [], _, _ => rfl
  | b :: bs, H, full => by
    simp only [List.foldl_cons]
    rw [fold_toState bs _ (fun b' hb' => full b' (List.mem_cons_of_mem _ hb'))]
    congr 1
    exact Silmaril.Crypto.X86.Sha256O2.compressBlock_toState H b (full b List.mem_cons_self)

/-- **The struct at `sp` has absorbed `consumed`.** -/
def Absorbed (m : Memory) (sp : Word) (consumed : List Byte) : Prop :=
  ∃ blocks tail, Driver.ReadInv consumed blocks tail ∧ Buf m sp IV blocks tail consumed.length

/-- **The hash state is the SHA-256 fold over the bytes consumed so far.** -/
theorem Absorbed.stream {m : Memory} {sp : Word} {consumed : List Byte}
    (h : Absorbed m sp consumed) :
    ∃ blocks tail H, StateHolds m (sp + 0x20#64) H ∧ Driver.StreamInv consumed blocks tail H.toState ∧
      m.readBytes (sp + 0x40#64).toNat tail.length = some tail := by
  obtain ⟨blocks, tail, hr, hb⟩ := h
  exact ⟨blocks, tail, _, hb.hState, ⟨hr, by rw [fold_toState _ _ hb.hFull, IV_toState]⟩,
    hb.hTail⟩

/-- Nothing consumed: the initial value and an empty buffer (what `sha_init` leaves). -/
theorem absorbed_nil {m : Memory} {sp : Word} (hst : StateHolds m (sp + 0x20#64) IV)
    (hblen : loadN m (sp + 0x80#64) 8 = some 0#64) (htot : loadN m (sp + 0x88#64) 8 = some 0#64)
    (fit : (sp + 0x40#64).toNat < 2 ^ 64) : Absorbed m sp [] :=
  ⟨[], [], Silmaril.Process.CLI.Sha256Cli.Driver.read_init, hst, Update.readBytes_nil fit, hblen, htot, by simp, by decide⟩

/-- The loop's fixed context: the frame of `digest_file`, two callee-saved registers the
loop keeps, the descriptor it reads (stored at `sp + 8`), and the memory at the loop's entry
(`LoopFrame.keep` is relative to it). -/
structure Loop where
  sp : Word
  rbp : Word
  r13 : Word
  fd : Word
  m0 : Memory

/-- What the loop writes, from its entry: the stack span of `sha_update` (`Update.stackSpan`:
never `[sp, sp + 0x20)` nor anything from `sp + 0x98` up) and `iobuf`, which `read` fills. -/
def loopSpan (sp : Word) (a : Nat) : Prop :=
  Update.stackSpan sp a ∨ (iobuf.toNat ≤ a ∧ a < iobuf.toNat + 32768)

/-- What every cut point of the loop knows about the process, apart from the struct. -/
structure LoopFrame (e : Loop) (s : XState) : Prop where
  rsp : s.core.read .rsp = e.sp
  rbx : s.core.read .rbx = 64#64
  rbp : s.core.read .rbp = e.rbp
  r13 : s.core.read .r13 = e.r13
  spAlign : e.sp.toNat % 16 = 0
  spLow : 0x420000 ≤ e.sp.toNat
  spHigh : e.sp.toNat + 0x1000 < 2 ^ 64
  stackW : s.memory.Permitted .write (e.sp.toNat - 400) 552
  stackR : s.memory.Permitted .read (e.sp.toNat - 400) 552
  code : s.memory.fetchBytes Binary.textBase.toNat Silmaril.Crypto.X86.Sha256O2.size =
    some (Silmaril.Crypto.X86.Sha256O2.image Binary.textBase Binary.rodataBase)
  kTable : s.memory.readBytes Binary.rodataBase.toNat Silmaril.Crypto.X86.Sha256O2.kSize =
    some Silmaril.Crypto.X86.Sha256O2.kBytes
  /-- The descriptor slot of `digest_file`'s frame. -/
  fdSlot : loadN s.memory (e.sp + 8#64) 8 = some e.fd
  /-- `iobuf` is readable and writable (`read`'s buffer). -/
  iobufW : s.memory.Permitted .write iobuf.toNat 32768
  iobufR : s.memory.Permitted .read iobuf.toNat 32768
  /-- The system-call wrapper `sc3` is in memory. -/
  sc3 : Loaded s.memory Sc3.base Sc3.code
  /-- Since the loop's entry, only `loopSpan` was written. -/
  keep : Memory.WritesWithin e.m0 s.memory (loopSpan e.sp)

/-- `0x402f06`: `read(fd, iobuf, 32768)` returned `chunk` (in `iobuf`, its length in `rax`);
the struct holds `consumed`. -/
def AfterRead (e : Loop) (consumed chunk : List Byte) (s : XState) : Prop :=
  s.core.rip = base + BitVec.ofNat 64 22 ∧ LoopFrame e s ∧
    s.memory.readBytes iobuf.toNat chunk.length = some chunk ∧ chunk.length ≤ 32768 ∧
    s.core.read .rax = BitVec.ofNat 64 chunk.length ∧ Absorbed s.memory e.sp consumed

/-- `0x402ef0`, the loop head (before the next `read`): the struct holds `consumed`. -/
def AtHead (e : Loop) (consumed : List Byte) (s : XState) : Prop :=
  s.core.rip = base + BitVec.ofNat 64 0 ∧ LoopFrame e s ∧ Absorbed s.memory e.sp consumed

/-- `0x403034`, the padding (after `read` returned 0): the struct holds `consumed`, and `rdx`
the total (`sha_final` reads it from there). -/
def AtPad (e : Loop) (consumed : List Byte) (s : XState) : Prop :=
  s.core.rip = base + BitVec.ofNat 64 324 ∧ LoopFrame e s ∧
    s.core.read .rdx = BitVec.ofNat 64 consumed.length ∧ Absorbed s.memory e.sp consumed

/-- The context `Digest.Update` runs in, for one iteration. -/
def ctxOf (e : Loop) (consumed chunk : List Byte) (blocks : List (List Byte))
    (tail : List Byte) (s : XState) : Update.Ctx :=
  ⟨e.sp, chunk, IV, blocks, tail, consumed.length, s.core.read, s.memory⟩

theorem sc3_toNat : Sc3.base.toNat = 0x401010 := rfl
theorem sc3_length : Sc3.code.length = 16 := rfl
theorem iobuf_toNat : iobuf.toNat = 0x40a0c0 := rfl

theorem LoopFrame.of_frame {e : Loop} {c : Update.Ctx} {s t : XState} (hc : c.sp = e.sp)
    (hs : LoopFrame e s) (h0 : c.r0 = s.core.read) (hm0 : c.m0 = s.memory)
    (h : Update.Frame c t) : LoopFrame e t := by
  have hk : Memory.WritesWithin s.memory t.memory (Update.stackSpan e.sp) := by
    have := h.keep; rw [hm0, hc] at this; exact this
  have lo := hs.spLow
  have hi := hs.spHigh
  refine ⟨h.rsp.trans hc, h.rbx, h.rbp.trans (by rw [h0]; exact hs.rbp),
    h.r13.trans (by rw [h0]; exact hs.r13), hc ▸ h.spAlign, hc ▸ h.spLow, hc ▸ h.spHigh,
    hc ▸ h.stackW, hc ▸ h.stackR, h.code, h.kTable, ?_, (hk.permitted_iff _ _ _).mpr hs.iobufW,
    (hk.permitted_iff _ _ _).mpr hs.iobufR, ?_, hs.keep.trans (hk.mono fun a ha => .inl ha)⟩
  · rw [loadN_transfer hk]; · exact hs.fdSlot
    intro o ho hin
    rw [toNat_sp_add hi (by decide)] at hin
    simp only [Update.stackSpan] at hin; omega
  · unfold Loaded; rw [hk.fetchBytes]; · exact hs.sc3
    intro o ho hin
    rw [sc3_length] at ho; rw [sc3_toNat] at hin
    simp only [Update.stackSpan] at hin; omega

/-- **VERIFIED. One iteration of the read loop absorbs the chunk.** From `AfterRead consumed
chunk`, the process reaches by retiring steps (no system call) `AtHead (consumed ++ chunk)`,
or, if the chunk is empty, `AtPad consumed`. -/
theorem update_absorbs {e : Loop} {consumed chunk : List Byte} {s : XState}
    (hlv : s.faulted = false) (hl : Loaded s.memory base code)
    (h : AfterRead e consumed chunk s) :
    ∃ t, Silmaril.Machine.Execution.Reaches rStep s t ∧ t.faulted = false ∧
      Loaded t.memory base code ∧
      ((AtHead e (consumed ++ chunk) t ∧ chunk ≠ []) ∨ (chunk = [] ∧ AtPad e consumed t)) := by
  obtain ⟨hrip, hF, hchunk, hlen, hax, blocks, tail, hr, hb⟩ := h
  have hpre : Update.pre (ctxOf e consumed chunk blocks tail s) s :=
    ⟨⟨hF.rsp, hF.rbx, rfl, rfl, hchunk, hlen, hF.spAlign, hF.spLow, hF.spHigh, hF.stackW,
      hF.stackR, hF.code, hF.kTable, .refl _ _⟩, hax, hb⟩
  obtain ⟨t, hrun, hlv', hl', hpost⟩ := Update.update_runs (fun _ => 0) _ s hlv hl hrip hpre
  refine ⟨t, hrun, hlv', hl', ?_⟩
  rcases hpost with ⟨hrip', hF', hpos, blocks', tail', hacc, hb'⟩ | ⟨hrip', hF', hnil, hb'⟩
  · refine .inl ⟨⟨hrip', LoopFrame.of_frame rfl hF rfl rfl hF', blocks', tail', ⟨?_, hb'.hFull,
      hb'.hRoom⟩, by simpa [ctxOf] using hb'⟩, List.ne_nil_of_length_pos hpos⟩
    simp only [ctxOf] at hacc
    rw [hacc, hr.bytes]
  · subst hnil
    exact .inr ⟨rfl, hrip', LoopFrame.of_frame rfl hF rfl rfl hF', hb'.2, blocks, tail, hr, hb'.1⟩

end Silmaril.Apps.Sha256sum.Binary.Digest

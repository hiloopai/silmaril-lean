module

public import Silmaril.Apps.Sha256sum.Stdout.Run
public import Silmaril.Apps.Sha256sum.IOLayer.X86Glue

/-! # The `out_flush` contract (0x401100, `write_all` inlined)

Status: **WIP**. `flush_nil` (empty buffer: returns 0, `olen = 0`) is VERIFIED; `flush_cons`
(entry to the `write_all` loop head `0x401138`) still has a `sorry`; the loop body across
`write(1, …)` is not stated yet. Nothing here is labelled VERIFIED as a whole.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.X86 (Word State Reg)
open Silmaril.Process (Memory Byte)
open Silmaril.Machine.LittleEndian (encodeWords)

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits

/-- The bytes `out_flush` writes when no write fails: its frame below the entry `rsp` (two
saved registers, the alignment slot, the return address of the `sc3` call) and `olen`
(`out_error` is written only after a failed write). -/
def FlushFoot (sp : Nat) (x : Nat) : Prop := (sp - 32 ≤ x ∧ x < sp) ∨ (0x412130 ≤ x ∧ x < 0x412138)

/-- The entry of a call of `out_flush` (`rip = 0x401100`, return address `ra` on the stack)
with `obuf[0, olen) = buf`. -/
structure FlushEntry (s : XState) (buf : Bytes) (ra : Word) : Prop where
  faulted : s.faulted = false
  code : Lift.Code s.memory
  rip : s.core.rip = 0x401100#64
  /-- The stack is above `.bss` (which ends at `0x413140`). -/
  sp : 0x414020 ≤ (s.core.read .rsp).toNat ∧ (s.core.read .rsp).toNat < 2 ^ 47
  frameR : s.memory.Permitted .read ((s.core.read .rsp).toNat - 32) 40
  frameW : s.memory.Permitted .write ((s.core.read .rsp).toNat - 32) 32
  olenW : s.memory.Permitted .write 0x412130 8
  ret : s.memory.readWith .read (s.core.read .rsp).toNat 8 = some (encodeWords [ra])
  olen : s.memory.readWith .read 0x412130 8 = some (X86.Ext.leBytes (BitVec.ofNat 64 buf.length) 8)
  obuf : s.memory.readWith .read 0x412140 buf.length = some (buf.map ofU8)
  cap : buf.length ≤ 4096

/-- The state after `out_flush` returned to `ra` with no error: `olen = 0`, return value 0,
callee-saved registers and `rsp` restored, writes only in the footprint. -/
structure FlushExit (s : XState) (ra : Word) (t : XState) : Prop where
  faulted : t.faulted = false
  code : Lift.Code t.memory
  rip : t.core.rip = ra
  rsp : t.core.read .rsp = s.core.read .rsp + 8#64
  rbx : t.core.read .rbx = s.core.read .rbx
  rbp : t.core.read .rbp = s.core.read .rbp
  r12 : t.core.read .r12 = s.core.read .r12
  r13 : t.core.read .r13 = s.core.read .r13
  r14 : t.core.read .r14 = s.core.read .r14
  r15 : t.core.read .r15 = s.core.read .r15
  rax : t.core.read .rax = 0#64
  olen : t.memory.readWith .read 0x412130 8 = some (X86.Ext.leBytes 0#64 8)
  foot : Memory.WritesWithin s.memory t.memory (FlushFoot (s.core.read .rsp).toNat)

theorem flush_nil {s : XState} {buf : Bytes} {ra : Word} (h : FlushEntry s buf ra) (hnil : buf = []) :
    RunsTo (FlushExit s ra) s := by
  obtain ⟨hf, hc, hrip, hsp, hfr, hfw, how, hret, holen, hobuf, hcap⟩ := h
  subst hnil
  rstep [hrip]
  rstep
  rstep
  rstep
  rstep
  rstep
  rstep
  rstep
  rstep
  rstep
  rstep
  refine RunsTo.done ⟨hf, by assumption, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
    not_false_eq_true, Lift.read_mk, Lift.core_regs]; done)
  all_goals dsimp only
  · repeat rmem [Bool.false_eq_true]
    simp
  · xfoot [FlushFoot]

/-- The loop head `0x401138` of the inlined `write_all`: `sent` written, `rest` left
(`rbp` points at it, `rbx` is its length), the frame of the entry state `s0`. -/
structure LoopAt (s0 : XState) (ra : Word) (sent rest : Bytes) (s : XState) : Prop where
  faulted : s.faulted = false
  code : Lift.Code s.memory
  rip : s.core.rip = 0x401138#64
  rsp : s.core.read .rsp = s0.core.read .rsp - 24#64
  sp : 0x414020 ≤ (s0.core.read .rsp).toNat ∧ (s0.core.read .rsp).toNat < 2 ^ 47
  frameR : s.memory.Permitted .read ((s0.core.read .rsp).toNat - 32) 40
  frameW : s.memory.Permitted .write ((s0.core.read .rsp).toNat - 32) 32
  olenW : s.memory.Permitted .write 0x412130 8
  olenR : s.memory.Permitted .read 0x412130 8
  ret : s.memory.readWith .read (s0.core.read .rsp).toNat 8 = some (encodeWords [ra])
  savedRbp : s.memory.readWith .read (s0.core.read .rsp - 8#64).toNat 8 =
    some (encodeWords [s0.core.read .rbp])
  savedRbx : s.memory.readWith .read (s0.core.read .rsp - 16#64).toNat 8 =
    some (encodeWords [s0.core.read .rbx])
  r12 : s.core.read .r12 = s0.core.read .r12
  r13 : s.core.read .r13 = s0.core.read .r13
  r14 : s.core.read .r14 = s0.core.read .r14
  r15 : s.core.read .r15 = s0.core.read .r15
  ne : rest ≠ []
  cap : sent.length + rest.length ≤ 4096
  rbx : s.core.read .rbx = BitVec.ofNat 64 rest.length
  rbp : s.core.read .rbp = BitVec.ofNat 64 (0x412140 + sent.length)
  buf : s.memory.readWith .read (0x412140 + sent.length) rest.length = some (rest.map ofU8)
  foot : Memory.WritesWithin s0.memory s.memory (FlushFoot (s0.core.read .rsp).toNat)

theorem flush_cons {s : XState} {buf : Bytes} {ra : Word} (h : FlushEntry s buf ra) (hne : buf ≠ []) :
    RunsTo (LoopAt s ra [] buf) s := by
  obtain ⟨hf, hc, hrip, hsp, hfr, hfw, how, hret, holen, hobuf, hcap⟩ := h
  have hl : buf.length % 18446744073709551616 = buf.length := Nat.mod_eq_of_lt (by omega)
  have hpos : 0 < buf.length := List.length_pos_iff.mpr hne
  have hz : (BitVec.ofNat 64 buf.length == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  rstep [hrip]
  rstep
  rstep
  rstep [hl]
  rstep [hl]
  rstep [hl, hz]
  rstep
  rstep
  have hor : s.memory.Permitted .read 0x412130 8 := Memory.readWith_permitted holen
  refine RunsTo.done ⟨hf, by assumption, rfl, ?_, hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hne,
    by simpa using hcap, ?_, ?_, ?_, ?_⟩
  all_goals try (simp only [State.read_write_same, State.read_write_other, ne_eq, reduceCtorEq,
    not_false_eq_true, Lift.read_mk, Lift.core_regs, List.length_nil, Nat.add_zero]; done)
  all_goals dsimp only
  all_goals try xperm
  all_goals try ((repeat rmem [Bool.false_eq_true]); done)
  · simp only [List.length_nil, Nat.add_zero]; repeat rmem [Bool.false_eq_true]
  · xfoot [FlushFoot]

/-- Inside `sc3`, called from the loop with `rest` left: the loop's frame, and the return
address `0x40114d` below it. -/
structure InSc3 (s0 : XState) (ra : Word) (sent rest : Bytes) (t : XState) : Prop where
  faulted : t.faulted = false
  code : Lift.Code t.memory
  rsp : t.core.read .rsp = s0.core.read .rsp - 32#64
  sp : 0x414020 ≤ (s0.core.read .rsp).toNat ∧ (s0.core.read .rsp).toNat < 2 ^ 47
  frameR : t.memory.Permitted .read ((s0.core.read .rsp).toNat - 32) 40
  frameW : t.memory.Permitted .write ((s0.core.read .rsp).toNat - 32) 32
  olenW : t.memory.Permitted .write 0x412130 8
  olenR : t.memory.Permitted .read 0x412130 8
  retSc3 : t.memory.readWith .read (s0.core.read .rsp - 32#64).toNat 8 =
    some (encodeWords [0x40114d#64])
  ret : t.memory.readWith .read (s0.core.read .rsp).toNat 8 = some (encodeWords [ra])
  savedRbp : t.memory.readWith .read (s0.core.read .rsp - 8#64).toNat 8 =
    some (encodeWords [s0.core.read .rbp])
  savedRbx : t.memory.readWith .read (s0.core.read .rsp - 16#64).toNat 8 =
    some (encodeWords [s0.core.read .rbx])
  r12 : t.core.read .r12 = s0.core.read .r12
  r13 : t.core.read .r13 = s0.core.read .r13
  r14 : t.core.read .r14 = s0.core.read .r14
  r15 : t.core.read .r15 = s0.core.read .r15
  ne : rest ≠ []
  cap : sent.length + rest.length ≤ 4096
  rbx : t.core.read .rbx = BitVec.ofNat 64 rest.length
  rbp : t.core.read .rbp = BitVec.ofNat 64 (0x412140 + sent.length)
  buf : t.memory.readWith .read (0x412140 + sent.length) rest.length = some (rest.map ofU8)
  foot : Memory.WritesWithin s0.memory t.memory (FlushFoot (s0.core.read .rsp).toNat)

/-- At the `syscall` of `sc3` with the request `write(1, rest)`. -/
structure AtWrite (s0 : XState) (ra : Word) (sent rest : Bytes) (t : XState) : Prop
    extends InSc3 s0 ra sent rest t where
  rip : t.core.rip = 0x40101c#64
  rax : t.core.read .rax = 1#64
  rdi : t.core.read .rdi = 1#64
  rsi : t.core.read .rsi = BitVec.ofNat 64 (0x412140 + sent.length)
  rdx : t.core.read .rdx = BitVec.ofNat 64 rest.length

theorem loop_call {s0 : XState} {ra : Word} {sent rest : Bytes} {s : XState}
    (h : LoopAt s0 ra sent rest s) : RunsTo (AtWrite s0 ra sent rest) s := by
  obtain ⟨hf, hc, hrip, hrsp, hsp, hfr, hfw, how, hor, hret, hsbp, hsbx, h12, h13, h14, h15, hne,
    hcap, hrbx, hrbp, hbuf, hfoot⟩ := h
  rstep [hrip]
  rstep [hrbx]
  rstep [hrbp]
  rstep
  rstep [hrsp]
  rstep
  rstep
  rstep
  rstep
  refine RunsTo.done ⟨⟨hf, by assumption, ?_, hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hne, hcap, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_, ?_, ?_⟩
  rfin [h12, h13, h14, h15, hrbx, hrbp, hrsp] [FlushFoot]

/-- Back from the `syscall` of `sc3` with `rax = n`, the count the kernel accepted. -/
structure AfterWrite (s0 : XState) (ra : Word) (sent rest : Bytes) (n : Nat) (u : XState) : Prop
    extends InSc3 s0 ra sent rest u where
  rip : u.core.rip = 0x40101e#64
  rax : u.core.read .rax = BitVec.ofNat 64 n

theorem after_write {s0 : XState} {ra : Word} {sent rest : Bytes} {n : Nat} {u : XState}
    (h : AfterWrite s0 ra sent rest n u) (hpos : 0 < n) (hle : n ≤ rest.length) :
    RunsTo (fun v => (n = rest.length ∧ FlushExit s0 ra v) ∨
      (n < rest.length ∧ LoopAt s0 ra (sent ++ rest.take n) (rest.drop n) v)) u := by
  obtain ⟨⟨hf, hc, hrsp, hsp, hfr, hfw, how, hor, hrs, hret, hsbp, hsbx, h12, h13, h14, h15, hne,
    hcap, hrbx, hrbp, hbuf, hfoot⟩, hrip, hrax⟩ := h
  have hmsb : (BitVec.ofNat 64 n).msb = false := raxOf_ok_msb (by omega)
  have hadd : BitVec.ofNat 64 (0x412140 + sent.length) + BitVec.ofNat 64 n =
      BitVec.ofNat 64 (0x412140 + (sent ++ rest.take n).length) := by
    rw [← BitVec.ofNat_add]; congr 1; simp [List.length_take]; omega
  have hsub : BitVec.ofNat 64 rest.length - BitVec.ofNat 64 n =
      BitVec.ofNat 64 (rest.drop n).length := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, List.length_drop]
    omega
  by_cases hn : n = rest.length
  · have hz : (BitVec.ofNat 64 rest.length == BitVec.ofNat 64 n) = true := by simp [hn]
    rstep [hrip, hrsp]
    rstep [hrax, hmsb]
    rstep [hrax, hmsb]
    rstep [hrbp, hrax, hadd]
    rstep [hrbx, hrax, hsub]
    rstep [hz]
    rstep
    rstep
    rstep
    rstep [hrsp]
    rstep
    rstep
    rstep
    refine RunsTo.done (.inl ⟨hn, hf, by assumption, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    rfin [h12, h13, h14, h15] [FlushFoot]
  · have hlt : n < rest.length := by omega
    have hz : (BitVec.ofNat 64 rest.length == BitVec.ofNat 64 n) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    have hbuf' : u.memory.readWith .read (0x412140 + (sent ++ rest.take n).length)
        (rest.drop n).length = some ((rest.drop n).map ofU8) := by
      have := Memory.readWith_sub_range hbuf (offset := n) (len := rest.length - n) hlt (by omega)
      rw [List.length_append, List.length_take, Nat.min_eq_left hle, ← Nat.add_assoc, List.length_drop,
        this, ← List.map_drop, List.take_of_length_le (by simp)]
    have hne' : rest.drop n ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    rstep [hrip, hrsp]
    rstep [hrax, hmsb]
    rstep [hrax, hmsb]
    rstep [hrbp, hrax, hadd]
    rstep [hrbx, hrax, hsub]
    rstep [hz]
    refine RunsTo.done (.inr ⟨hlt, hf, by assumption, rfl, ?_, hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, hne', by simp [List.length_take, List.length_drop]; omega, ?_, ?_, hbuf', hfoot⟩)
    rfin [h12, h13, h14, h15] [FlushFoot]

/-! ## The `out_flush` contract over `GStep` -/

section FlushLeads

open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev Allowed leads_call trapped)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

local notation "hout" => Silmaril.Process.LPS.Problems.GnuSha256sum.out
local notation "hin" => Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead
local notation "hexp" => Silmaril.Process.LPS.Problems.GnuSha256sum.expected

theorem hout_append (h es : List Ev) : hout (h ++ es) = hout h ++ hout es := by
  simp [Silmaril.Process.LPS.Problems.GnuSha256sum.out, List.flatMap_append]

theorem hin_append (h es : List Ev) : hin (h ++ es) = hin h ++ hin es := by
  simp [Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead, List.flatMap_append]

theorem hout_write (bs : Bytes) (n : Nat) :
    hout [Ev.sys (.write 1 bs) (.ok n)] = (bs.take n).map UInt8.toBitVec := by
  simp [Silmaril.Process.LPS.Problems.GnuSha256sum.out,
    Silmaril.Process.LPS.Problems.GnuSha256sum.outBytes]

theorem hin_write (bs : Bytes) (n : Nat) : hin [Ev.sys (.write 1 bs) (.ok n)] = [] := by
  simp [Silmaril.Process.LPS.Problems.GnuSha256sum.stdinRead,
    Silmaril.Process.LPS.Problems.GnuSha256sum.readBytes]

/-- `Ok` depends on the program state only through `faulted`. -/
theorem Ok.with_x {message : List Byte} {g : GS} {h : List Ev} (ok : Ok message g h) {t : XState}
    (hf : t.faulted = false) : Ok message { g with x := t } h :=
  ⟨ok.1, ok.2.1, ok.2.2.1, ok.2.2.2.1, ok.2.2.2.2.1, hf⟩

/-- `Ok` after an accepted `write(1, bs)` of a nonempty prefix of what is left to print, once
the whole message is read. -/
theorem Ok.write {message : List Byte} {g : GS} {h : List Ev} (ok : Ok message g h) {g' : GS}
    (hx : g'.exited = none) (hf : g'.x.faulted = false) {bs : Bytes} {n : Nat} (hne : bs ≠ [])
    (hpre : hout h ++ (bs.take n).map UInt8.toBitVec <+: hexp message)
    (hrd : hin h = message) : Ok message g' (h ++ [Ev.sys (.write 1 bs) (.ok n)]) := by
  obtain ⟨-, hall, -, -, -, -⟩ := ok
  refine ⟨hx, ?_, ?_, ?_, .inr ?_, hf⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hall e he
    · simp only [List.mem_singleton] at he; subst he; exact ⟨rfl, hne, n, rfl⟩
  · rw [hin_append, hin_write, List.append_nil, hrd]
  · rw [hout_append, hout_write]; exact hpre
  · rw [hin_append, hin_write, List.append_nil, hrd]

/-- The kernel's replies to `write(1, …)` on a working standard output. -/
theorem write_inv {w : World} (hw : w.stdoutFull = false) {k : KState} (hfd : k.fds 1 = some .stdout)
    {bs : Bytes} {r : Ret} {k' : KState} (h : WorldStep w k (.write 1 bs) r k') :
    ∃ n, r = .ok n ∧ Accepts bs n ∧ k' = k := by
  cases h with
  | writeOut _ _ ha => exact ⟨_, rfl, ha, rfl⟩
  | writeFull _ hf => rw [hw] at hf; cases hf
  | writeErr he _ => rw [hfd] at he; cases he
  | writeBad hb => rcases hb with hb | hb | ⟨_, _, hb⟩ <;> rw [hfd] at hb <;> cases hb

/-- What a flush of `buf` from `(g0, h0)` leaves at the return. -/
def Flushed (message : List Byte) (g0 : GS) (h0 : List Ev) (buf : Bytes) (ra : Word) (g : GS)
    (h : List Ev) : Prop :=
  Ok message g h ∧ g.k = g0.k ∧ FlushExit g0.x ra g.x ∧
    hout h = hout h0 ++ buf.map UInt8.toBitVec ∧ hin h = hin h0

/-- The return core of a `write` reply keeps every register but `rax`, `rcx`, `r11`. -/
theorem returnCore_read {r11Of : Core → Word} {c : Core} {v : Word} {r : Reg}
    (h1 : r ≠ .rax) (h2 : r ≠ .rcx) (h3 : r ≠ .r11) : (returnCore r11Of c v).read r = c.read r := by
  simp [returnCore, State.read_write_other, h1, h2, h3]

theorem AtWrite.resume {s0 : XState} {ra : Word} {sent rest : Bytes} {t : XState}
    (h : AtWrite s0 ra sent rest t) (r11 : Word) (n : Nat) :
    AfterWrite s0 ra sent rest n
      { t with core := (returnCore (fun _ => r11) { t.core with rip := t.core.rip + 2 }
        (BitVec.ofNat 64 n)) } := by
  obtain ⟨⟨hf, hc, hrsp, hsp, hfr, hfw, how, hor, hrs, hret, hsbp, hsbx, h12, h13, h14, h15, hne,
    hcap, hrbx, hrbp, hbuf, hfoot⟩, hrip, -, -, -, -⟩ := h
  refine ⟨⟨hf, hc, ?_, hsp, hfr, hfw, how, hor, hrs, hret, hsbp, hsbx, ?_, ?_, ?_, ?_, hne, hcap, ?_,
    ?_, hbuf, hfoot⟩, ?_, ?_⟩
  all_goals first
    | (simp only [returnCore]; done)
    | (rw [returnCore_read (by decide) (by decide) (by decide)]; assumption)
    | (simp only [returnCore, State.write_rip, hrip]; rfl)

theorem loop_leads {w : World} (hw : w.stdoutFull = false) {message : List Byte} {g0 : GS}
    {h0 : List Ev} {buf : Bytes} {ra : Word} (hfd : g0.k.fds 1 = some .stdout)
    (hpre : hout h0 ++ buf.map UInt8.toBitVec <+: hexp message) (hrd : hin h0 = message) :
    ∀ (m : Nat) (g : GS) (h : List Ev) (sent rest : Bytes), rest.length ≤ m →
      LoopAt g0.x ra sent rest g.x → sent ++ rest = buf → g.k = g0.k → Ok message g h →
      hout h = hout h0 ++ sent.map UInt8.toBitVec → hin h = hin h0 →
      Leads (GStep w) (Ok message) (Flushed message g0 h0 buf ra) g h := by
  intro m
  induction m with
  | zero =>
    intro g h sent rest hm hl
    exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hm)) hl.ne
  | succ m ih =>
    intro g h sent rest hm hl hsr hk ok hout0 hin0
    refine (loop_call hl).leads ok.1 ok fun t ht => ?_
    have okt := Ok.with_x ok ht.faulted
    have hfd' : t.core.read .rax = 1#64 := ht.rax
    refine leads_call (c := .write 1 rest) (trap_sc3 ht.code ht.rip) ok.1 ht.faulted okt ?_ trivial
      ⟨.ok rest.length, g.k, .writeOut (hk ▸ hfd) hw ⟨le_refl _, fun _ => List.length_pos_iff.mpr hl.ne⟩⟩ ?_
    · have := decode_write (c := { t.core with rip := t.core.rip + 2 }) (m := t.memory) (bs := rest)
        (by show (t.core.read .rax).toNat = 1; rw [ht.rax]; rfl)
        (by
          show t.memory.readWith .read (t.core.read .rsi).toNat (t.core.read .rdx).toNat = _
          rw [ht.rsi, ht.rdx, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by have := ht.cap; omega), Nat.mod_eq_of_lt (by have := ht.cap; omega)]
          exact ht.buf)
      rw [this]
      show some (X86Sys.Req.call (.write (fd32 (t.core.read .rdi)) rest)) = _
      rw [ht.rdi]; rfl
    · intro r k' r11 ws
      obtain ⟨n, rfl, ⟨hle, hpos⟩, rfl⟩ := write_inv hw (hk ▸ hfd) ws
      have hpos := hpos hl.ne
      have hres : X86Sys.resume (fun _ => r11) t { t.core with rip := t.core.rip + 2 }
          (.write 1 rest) (.ok n) =
          { t with core := (returnCore (fun _ => r11) { t.core with rip := t.core.rip + 2 }
            (BitVec.ofNat 64 n)) } := rfl
      simp only [trapped, hres]
      have haw := ht.resume r11 n
      have hpre' : hout h ++ (rest.take n).map UInt8.toBitVec <+: hexp message := by
        rw [hout0, List.append_assoc, ← List.map_append]
        refine List.IsPrefix.trans ?_ hpre
        refine (List.prefix_append_right_inj _).mpr ?_
        rw [← hsr]; exact (List.map_append ..).symm ▸ (List.prefix_append_right_inj _).mpr
          ((List.take_prefix n rest).map _) |>.trans (by rw [List.map_append])
      have ok1 : Ok message ⟨_, g.k, none⟩ (h ++ [Ev.sys (.write 1 rest) (.ok n)]) :=
        Ok.write ok rfl haw.faulted hl.ne hpre' (hin0.trans hrd)
      have hout1 : hout (h ++ [Ev.sys (.write 1 rest) (.ok n)]) =
          hout h0 ++ (sent ++ rest.take n).map UInt8.toBitVec := by
        rw [hout_append, hout_write, hout0, List.map_append, List.append_assoc]
      have hin1 : hin (h ++ [Ev.sys (.write 1 rest) (.ok n)]) = hin h0 := by
        rw [hin_append, hin_write, List.append_nil, hin0]
      refine (after_write haw hpos hle).leads rfl ok1 fun v hv => ?_
      rcases hv with ⟨hn, hx⟩ | ⟨hlt, hv⟩
      · refine .done ⟨Ok.with_x ok1 hx.faulted, hk, hx, ?_, hin1⟩
        rw [hout1, hn, List.take_length, hsr]
      · refine ih _ _ _ _ (by simp [List.length_drop]; omega) hv ?_ hk (Ok.with_x ok1 hv.faulted)
          hout1 hin1
        rw [List.append_assoc, List.take_append_drop, hsr]

/-- **The `out_flush` contract** (`0x401100`, `write_all` inlined), on a working standard
output: from a call with `obuf[0, olen) = buf`, every execution keeps `Ok` and returns to `ra`
with `olen = 0` and `rax = 0`, the kernel unchanged, and exactly `buf` appended to standard
output, in however many pieces the kernel accepted. A nonempty flush needs the whole message
read and `buf` to continue the expected output. -/
theorem flush_leads {w : World} (hw : w.stdoutFull = false) {message : List Byte} {g : GS}
    {h : List Ev} {buf : Bytes} {ra : Word} (hfd : g.k.fds 1 = some .stdout)
    (he : FlushEntry g.x buf ra) (ok : Ok message g h)
    (hpre : hout h ++ buf.map UInt8.toBitVec <+: hexp message)
    (hrd : buf ≠ [] → hin h = message) :
    Leads (GStep w) (Ok message) (Flushed message g h buf ra) g h := by
  by_cases hb : buf = []
  · refine (flush_nil he hb).leads ok.1 ok fun t ht => .done ⟨Ok.with_x ok ht.faulted, rfl, ht, ?_, rfl⟩
    simp [hb]
  · refine (flush_cons he hb).leads ok.1 ok fun t ht => ?_
    exact loop_leads hw hfd hpre (hrd hb) _ { g with x := t } h [] buf (le_refl _) ht rfl rfl
      (Ok.with_x ok ht.faulted) (by simp) rfl

/-- `out_error` (`0x41212c`) survives a flush that did not fail. -/
theorem FlushExit.outError {s t : XState} {ra : Word} (h : FlushExit s ra t) {v : List Byte}
    (hsp : 0x414020 ≤ (s.core.read .rsp).toNat) (hs : s.memory.readWith .read 0x41212c 4 = some v) : t.memory.readWith .read 0x41212c 4 = some v := by
  rw [h.foot.readWith]; · exact hs
  intro off hoff hmem; simp only [FlushFoot] at hmem; omega

/-- **The `out_flush` call contract, continuation form** (`Stdout.PutcSite.FlushContract` of the
hex track, with `OutErrorZero` unfolded and `Coalesced` written out): `flush_leads` composed
with the continuation. -/
theorem flush_cps (w : World) (message : List Byte) (K : GS → List Ev → Prop) (g : GS) (h : List Ev)
    (buf emitted : Bytes) (ra : Word) (hw : w.stdoutFull = false) (hfd : g.k.fds 1 = some .stdout)
    (he : FlushEntry g.x buf ra)
    (hoe : g.x.memory.readWith .read 0x41212c 4 = some (X86.Ext.leBytes 0#64 4))
    (hco : hout h ++ buf.map UInt8.toBitVec = emitted.map UInt8.toBitVec) (ok : Ok message g h)
    (hrd : hin h = message) (hem : emitted.map UInt8.toBitVec <+: hexp message)
    (k : ∀ (g' : GS) (h' : List Ev), FlushExit g.x ra g'.x → g'.exited = none → g'.k = g.k →
      g'.x.memory.readWith .read 0x41212c 4 = some (X86.Ext.leBytes 0#64 4) →
      hout h' ++ ([] : Bytes).map UInt8.toBitVec = emitted.map UInt8.toBitVec →
      hin h' = hin h → Ok message g' h' → Leads (GStep w) (Ok message) K g' h') :
    Leads (GStep w) (Ok message) K g h :=
  (flush_leads hw hfd he ok (hco ▸ hem) (fun _ => hrd)).trans fun g' h' ⟨ok', hk, hx, ho, hi⟩ =>
    k g' h' hx ok'.1 hk (hx.outError he.sp.1 hoe) (by rw [List.map_nil, List.append_nil, ho, hco]) hi ok'

end FlushLeads

end Silmaril.Apps.Sha256sum.Stdout

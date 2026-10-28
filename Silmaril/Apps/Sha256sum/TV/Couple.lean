module

public import Silmaril.Apps.Sha256sum.Stdout.LeadsX
public import Silmaril.Apps.Sha256sum.Stdout.HexLo
public import Silmaril.Apps.Sha256sum.TV.FormatIR
public import Silmaril.X86.TVIR.Flags

/-! # Couplings between `sha256sum-min` states and the record program

Status: **VERIFIED** (no `sorry`, standard axioms only).

The translation validation of `TV.FormatIR.format` against the x86 code of `cmain`'s inlined
`output_file` couples an IR state `σ` with a `GStep` process `g` and history `h`:

* `Common c io g h`: what holds at every block boundary: the process is running, not
  faulted, the kernel is the segment's (`c.k0`), the code is loaded, the history keeps
  `Ok` and has read the whole message, `rsp` is `cmain`'s, the output layer in memory holds
  the IR buffer (`Stdout.Obuf m io.1`), the history and the buffer are **coalesced** with the
  IR output (`Stdout.Coalesced h io.1 io.2`), and memory changed only in `Foot` (the callee
  frames below `rsp` and the output layer) since the segment's base memory `c.m0`;
* `Frame c`: what the base memory and kernel hold (the digest at `bin`, the `hexd` table,
  the stack, the spills and flags `output_file` and the operand loop read later);
* `At c pc P σ g h`: `Common`, `rip = pc`, and the block's register map `P σ g.x`.

The leaf adapters turn machine runs into `TVIR.Sim` judgements: `sim_run` (a retiring run,
`Stdout.RunsTo`), `branch_run` (a run ending at one of two addresses according to an IR
condition).

Reads of the base memory through the footprint: `Frame.digest_byte`, `Frame.table_byte`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Apps.Sha256sum.TV

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Apps.Sha256sum.Stdout
open Silmaril.X86 (State Reg)
open Silmaril.X86.TVIR
open Silmaril.Process (Memory Byte)
open Silmaril.Process.LPS.Problems.GnuSha256sum (GS GStep Ok Ev stdinRead)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)
open Silmaril.X86.Stencils.HexLoop (hexTable)

/-- The fixed data of the record segment: the message, `cmain`'s stack pointer, the digest,
the kernel, the base memory, and the operand pointer (`r12`, the string `"-"`). -/
structure Ctx where
  message : List Byte
  sp : X86.Word
  d : Bytes
  k0 : KState
  m0 : Memory
  file : X86.Word

/-- `bin[]`, `cmain`'s digest buffer at `rsp + 0x70`. -/
def Ctx.bin (c : Ctx) : Nat := c.sp.toNat + 0x70

/-- The bytes the record segment may write: the callee frames below `rsp` (`out_flush`,
`print_filename`, `close`'s `sc3`), and `out_error`, `olen`, `obuf`. -/
def Foot (sp : Nat) (a : Nat) : Prop :=
  (sp - 128 ≤ a ∧ a < sp) ∨ (0x41212c ≤ a ∧ a < 0x412140 + 4096)

/-- What the base memory and the kernel hold. -/
structure Frame (c : Ctx) : Prop where
  len : c.d.length = 32
  spBound : 0x414100 ≤ c.sp.toNat ∧ c.sp.toNat + 0x100 < 2 ^ 47
  stackR : c.m0.Permitted .read (c.sp.toNat - 128) (128 + 0x98)
  stackW : c.m0.Permitted .write (c.sp.toNat - 128) (128 + 0x98)
  digest : c.m0.readWith .read c.bin 32 = some (c.d.map ofU8)
  table : c.m0.readWith .read 0x4072c0 16 = some (hexTable.map ofU8)
  fd0 : c.k0.fds 0 = some .stdin
  fd1 : c.k0.fds 1 = some .stdout
  fd2 : c.k0.fds 2 = some .stderr

/-- The coupling at every block boundary (see the module docstring). -/
structure Common (c : Ctx) (io : Bytes × Bytes) (g : GS) (h : List Ev) : Prop where
  exited : g.exited = none
  faulted : g.x.faulted = false
  k : g.k = c.k0
  code : Lift.Code g.x.memory
  okh : OkH c.message h
  read : stdinRead h = c.message
  rsp : g.x.core.read .rsp = c.sp
  obuf : Obuf g.x.memory io.1
  coal : Coalesced h io.1 io.2
  foot : Memory.WritesWithin c.m0 g.x.memory (Foot c.sp.toNat)

/-- A block boundary at `pc` with register map `P`. -/
def At (c : Ctx) (pc : X86.Word) (P : HSt → XState → Prop) (σ : HSt) (g : GS) (h : List Ev) :
    Prop :=
  Common c σ.io g h ∧ g.x.core.rip = pc ∧ P σ g.x

theorem Common.ok {c : Ctx} {io : Bytes × Bytes} {g : GS} {h : List Ev} (hc : Common c io g h) :
    Ok c.message g h := by
  obtain ⟨x, k, e⟩ := g
  have he : e = none := hc.exited
  subst he
  exact hc.okh.ok hc.faulted k

/-- `Common` after a retiring run that kept `rsp` and wrote nothing. -/
theorem Common.same_mem {c : Ctx} {io : Bytes × Bytes} {g : GS} {h : List Ev}
    (hc : Common c io g h) {t : XState} (hf : t.faulted = false) (hcode : Lift.Code t.memory)
    (hm : t.memory = g.x.memory) (hsp : t.core.read .rsp = c.sp) :
    Common c io { g with x := t } h :=
  ⟨hc.exited, hf, hc.k, hcode, hc.okh, hc.read, hsp, hm ▸ hc.obuf, hc.coal, hm ▸ hc.foot⟩

/-! ## Reads of the base memory -/

theorem Foot.digest {c : Ctx} (hfr : Frame c) {k : Nat} (hk : k < 32) :
    ¬ Foot c.sp.toNat (c.bin + k) := by
  have := hfr.spBound; simp only [Foot, Ctx.bin]; omega

theorem Foot.table {c : Ctx} (hfr : Frame c) {k : Nat} (hk : k < 16) :
    ¬ Foot c.sp.toNat (0x4072c0 + k) := by
  have := hfr.spBound; simp only [Foot]; omega

/-- A digest byte, in any memory of the segment. -/
theorem Frame.digest_byte {c : Ctx} (hfr : Frame c) {m : Memory}
    (hm : Memory.WritesWithin c.m0 m (Foot c.sp.toNat)) {k : Nat} (hk : k < 32) :
    m.readWith .read (c.bin + k) 1 = some [ofU8 (c.d[k]'(by rw [hfr.len]; exact hk))] := by
  rw [hm.readWith (fun o ho => by have : o = 0 := by omega
                                  subst this; exact Foot.digest hfr hk)]
  have := Memory.readWith_sub_range hfr.digest (offset := k) (len := 1) hk (by omega)
  rw [this]
  have hl : k < (c.d.map ofU8).length := by rw [List.length_map, hfr.len]; exact hk
  rw [List.drop_eq_getElem_cons hl]
  simp

/-- A byte of the `hexd` table, in any memory of the segment. -/
theorem Frame.table_byte {c : Ctx} (hfr : Frame c) {m : Memory}
    (hm : Memory.WritesWithin c.m0 m (Foot c.sp.toNat)) {k : Nat} (hk : k < 16) :
    m.readWith .read (0x4072c0 + k) 1 = some [ofU8 (hexTable[k]'hk)] := by
  rw [hm.readWith (fun o ho => by have : o = 0 := by omega
                                  subst this; exact Foot.table hfr hk)]
  have := Memory.readWith_sub_range hfr.table (offset := k) (len := 1) hk (by omega)
  rw [this]
  have hl : k < (hexTable.map ofU8).length := by rw [List.length_map]; exact hk
  rw [List.drop_eq_getElem_cons hl]
  simp only [List.getElem_map, List.take_succ_cons, List.take_zero]
  rfl

/-- The read-only memory of the IR is the machine's, on the digest. -/
theorem Frame.roMem_digest {c : Ctx} (hfr : Frame c) {k : Nat} (hk : k < 32) :
    roMem c.d c.bin (c.bin + k) = c.d[k]'(by rw [hfr.len]; exact hk) :=
  TV.roMem_digest hk hfr.len

/-! ## Leaf adapters -/

variable {c : Ctx} {w : World} {F : List UInt8}

/-- **A retiring run simulates an IR statement**: if from every coupled state the machine
runs, without system calls, to a state coupled to the IR result, the run simulates the
statement. -/
theorem sim_run {s : Stmt HV Buffered} {P Q : HSt → GS → List Ev → Prop}
    (hP : ∀ σ g h, P σ g h → g.exited = none ∧ Ok c.message g h)
    (hrun : ∀ σ σ', Exec (roMem c.d c.bin) s σ σ' → Buffered.out σ'.io <+: F → ∀ g h, P σ g h →
      RunsTo (fun t => Q σ' { g with x := t } h) g.x) :
    Sim (GStep w) (Ok c.message) (roMem c.d c.bin) F P Q s := by
  intro σ σ' e hF K g h hp k
  obtain ⟨hx, ok⟩ := hP σ g h hp
  exact (hrun σ σ' e hF g h hp).leads hx ok fun t q => k _ _ q

/-- **A retiring run decides an IR condition**: from every coupled state the machine runs to
a state coupled by `Rt` if the condition holds, by `Rf` if not. -/
theorem branch_run {cond : BExp HV} {P Rt Rf : HSt → GS → List Ev → Prop}
    (hP : ∀ σ g h, P σ g h → g.exited = none ∧ Ok c.message g h)
    (hrun : ∀ σ g h, P σ g h →
      RunsTo (fun t => (cond.eval (roMem c.d c.bin) σ.env = true ∧ Rt σ { g with x := t } h) ∨
        (cond.eval (roMem c.d c.bin) σ.env = false ∧ Rf σ { g with x := t } h)) g.x) :
    Branch (GStep w) (Ok c.message) (roMem c.d c.bin) P cond Rt Rf := by
  intro σ K g h hp kt kf
  obtain ⟨hx, ok⟩ := hP σ g h hp
  refine (hrun σ g h hp).leads hx ok fun t q => ?_
  rcases q with ⟨hc, r⟩ | ⟨hc, r⟩
  · exact kt hc _ _ r
  · exact kf hc _ _ r

/-- `At` gives the hypotheses of the adapters. -/
theorem At.run {pc : X86.Word} {P : HSt → XState → Prop} {σ : HSt} {g : GS} {h : List Ev}
    (ha : At c pc P σ g h) : g.exited = none ∧ Ok c.message g h :=
  ⟨ha.1.exited, ha.1.ok⟩

end Silmaril.Apps.Sha256sum.TV

module

public import Silmaril.Machine.X86.BlockCert.Calls.Defs
public import Silmaril.Machine.X86.BlockCert.Store.Thms
public import Silmaril.X86.Ext.Store
public import Silmaril.Machine.X86.FnContract.Thms

/-!
# Function certificates with contract calls: steps and assembly

* `runL_push`, `runL_call`: the one-instruction listings `push r` and `call rel32` from a
  state whose return slot is writable, with the successor memory left opaque (`Stored`);
* `call_abiEntry`: after a `call` from a 16-byte-aligned stack pointer whose slot is also
  readable, the System V entry obligations hold and the return address is the instruction
  after the call;
* `from_block`, `total`: strong induction on the block measure. A plain block is a run of
  `Open.step` by `runLW_open`; a call block is the `call` step (`runLW_open` on its
  one-instruction listing) followed by the callee's run, which its contract's `total` gives.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.BlockCert.Calls

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded Stored)
open Silmaril.X86.Lift.Bir (LInstr XState XResult execBlock liftR)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.BlockCert

/-- `push r` as a one-instruction listing of length `l`. -/
theorem runL_push {m : MState} {r : Reg} {l : Nat}
    (hp : m.memory.Permitted .write (m.core.read .rsp - 8#64).toNat 8) :
    ∃ mem', runL [(.ext (.push r), l)] m =
        some ⟨{ m.core.write .rsp (m.core.read .rsp - 8#64) with
          rip := m.core.rip + BitVec.ofNat 64 l }, mem'⟩ ∧
      Stored m.memory mem' (m.core.read .rsp - 8#64).toNat (encodeWords [m.core.read r]) := by
  obtain ⟨mem', hpush, hs⟩ := Silmaril.X86.Ext.pushWord_isSome (v := m.core.read r) hp
  refine ⟨mem', ?_, hs⟩
  simp [runL, execBlock, Silmaril.X86.Ext.exec, hpush, Silmaril.X86.Ext.retire, liftR, ofX, xs]

/-- `call rel32` as a one-instruction listing. -/
theorem runL_call {m : MState} {rel : BitVec 32}
    (hp : m.memory.Permitted .write (m.core.read .rsp - 8#64).toNat 8) :
    ∃ mem', runL [(.ext (.call rel), 5)] m =
        some ⟨{ m.core.write .rsp (m.core.read .rsp - 8#64) with
          rip := m.core.rip + 5#64 + rel.signExtend 64 }, mem'⟩ ∧
      Stored m.memory mem' (m.core.read .rsp - 8#64).toNat (encodeWords [m.core.rip + 5#64]) := by
  obtain ⟨mem', hpush, hs⟩ :=
    Silmaril.X86.Ext.pushWord_isSome (v := m.core.rip + BitVec.ofNat 64 5) hp
  refine ⟨mem', ?_, hs⟩
  simp [runL, execBlock, Silmaril.X86.Ext.exec, hpush, liftR, ofX, xs]

/-- After a `call` from a 16-byte-aligned stack pointer with a readable and writable slot:
the System V entry obligations, and the return address is the next instruction. -/
theorem call_abiEntry {m : MState} {mem' : Memory} {target : Word}
    (hal : (m.core.read .rsp).toNat % 16 = 0) (h8 : 8 ≤ (m.core.read .rsp).toNat)
    (hr : m.memory.Permitted .read (m.core.read .rsp - 8#64).toNat 8)
    (hs : Stored m.memory mem' (m.core.read .rsp - 8#64).toNat (encodeWords [m.core.rip + 5#64])) :
    let c : State := { m.core.write .rsp (m.core.read .rsp - 8#64) with rip := target }
    FnContract.AbiEntry c mem' ∧ Open.retOf c mem' = m.core.rip + 5#64 := by
  intro c
  have hread : mem'.readBytes (c.read .rsp).toNat 8 = some (encodeWords [m.core.rip + 5#64]) := by
    have := hs.readWith_self (access := .read)
      (by simpa [Silmaril.Machine.LittleEndian.encodeWords] using hr)
    simpa [c, Memory.readBytes, Silmaril.Machine.LittleEndian.encodeWords] using this
  have hret := FnContract.retOf_of_readBytes hread
  refine ⟨⟨?_, ?_⟩, hret⟩
  · have hc : c.read .rsp = m.core.read .rsp - 8#64 :=
      Silmaril.X86.State.read_write_same m.core .rsp _
    rw [hc]
    have : (m.core.read .rsp - 8#64).toNat = (m.core.read .rsp).toNat - 8 := by bv_omega
    omega
  · rw [hret]; exact hread

theorem checked_mem {F : CallCert} (hc : F.checked = true) {b : CBlk} (hb : b ∈ F.blocks) :
    listingAtW F.code b.off b.kind.listing = true :=
  List.all_eq_true.mp hc b hb

theorem from_block {F : CallCert} {Q : MState → MState → Prop} (hc : F.checked = true)
    (hvc : F.VC Q) (m0 : MState) :
    ∀ (w : Nat) (b : CBlk) (m : MState), F.measure b.off m0 m = w → b ∈ F.blocks →
      F.ann b.off m0 m → m.core.rip = F.base + BitVec.ofNat 64 b.off →
      Loaded m.memory F.base F.code → ∃ t, Reaches Open.step m t ∧ Q m0 t := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro b m hw hb ha hrip hl
    have hlist := checked_mem hc hb
    have hv := hvc b hb
    -- the continuation, shared by both kinds
    have cont : ∀ t, Reaches Open.step m t → F.NextC Q m0 w t →
        ∃ t', Reaches Open.step m t' ∧ Q m0 t' := by
      intro t hr hn
      rcases hn with hq | ⟨b', hb', hrip', hl', ha', hlt⟩
      · exact ⟨t, hr, hq⟩
      · obtain ⟨t', hr', hq⟩ := ih _ hlt b' t rfl hb' ha' hrip' hl'
        exact ⟨t', hr.trans hr', hq⟩
    obtain ⟨off, kind⟩ := b
    cases kind with
    | plain L =>
      obtain ⟨m', hrun, hnext⟩ := hv m0 m ha hrip hl
      exact cont m' (runLW_open hlist hl hrip hrun) (hw ▸ hnext)
    | call rel C =>
      obtain ⟨⟨m1, hrun⟩, hpost⟩ := hv m0 m ha hrip hl
      obtain ⟨hab, hentry, hnext⟩ := hpost m1 hrun
      have hr1 := runLW_open hlist hl hrip hrun
      obtain ⟨t, hr2, hres⟩ := C.total m1 trivial hab hentry
      exact cont t (hr1.trans hr2) (hw ▸ hnext t hres)

theorem total {F : CallCert} (S : FnContract.Spec MState) {entry : CBlk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa := by
  intro m _ hab he
  obtain ⟨hl, hrip, ha⟩ := hpre m hab he
  exact from_block hc hvc m _ entry m rfl hentry ha hrip hl

end Silmaril.Proofs.Machine.X86.BlockCert.Calls

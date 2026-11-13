module

public import Silmaril.Machine.Abi.CrossAbi.Gcc.Defs
public import Silmaril.Machine.Abi.Win64.Thms
public import Silmaril.X86.Ext.Lemmas
/-!
# GCC's `call_ms` transition implements the System V → `ms_abi` bridge

Proofs for `Silmaril.Machine.Abi.CrossAbi.Gcc.Thms`.

* `enter_run`: the five register instructions and the `call` run under `Ext`
  semantics when the pushed slot is writable, and they establish the moved
  arguments, RSP − 48, and the pushed return address.
* `leave_run`: `add $0x28,%rsp; ret` runs when the caller's return address is
  readable at the restored RSP, and it jumps there.
* `implements`, `progress`: the thunk `callMs` implements `SysvToMs` and
  progresses under `CallMs.Room` and `CallMs.Guar`.
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc

open Silmaril.X86 (Reg Byte MState State pushWord popWord)
open Silmaril.X86.Ext (Instr Sz RM exec_aluI8_reg exec_mov_reg exec_call exec_ret)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi
open Silmaril.Machine.Abi.CrossAbi
open Silmaril.Machine.Abi.CrossAbi.Gcc
open Silmaril.Machine.Abi.Win64 (reg win64)
open Silmaril.Machine.Abi.SystemV (sysv Options Proto callOf)

/-- The core after the five register instructions of `call_ms`. -/
def pre (c : State) : State :=
  let c₁ : State :=
    { Sz.q.write c .rsp (Silmaril.X86.Ext.AluOp.resultN .sub (Sz.q.read c .rsp) ((0x28#8).signExtend 64)) with
        flags := Silmaril.X86.Ext.AluOp.flagsN .sub (Sz.q.read c .rsp) ((0x28#8).signExtend 64)
        rip := c.rip + 4 }
  let c₂ : State := { Sz.q.write c₁ .r8 (Sz.q.read c₁ .rdx) with rip := c₁.rip + 3 }
  let c₃ : State := { Sz.q.write c₂ .r9 (Sz.q.read c₂ .rcx) with rip := c₂.rip + 3 }
  let c₄ : State := { Sz.q.write c₃ .rdx (Sz.q.read c₃ .rsi) with rip := c₃.rip + 3 }
  { Sz.q.write c₄ .rcx (Sz.q.read c₄ .rdi) with rip := c₄.rip + 3 }

theorem run_pre (rest : List Instr) (m : MState) :
    run (callMsPre ++ rest) m = run rest ⟨pre m.core, m.memory⟩ := rfl

theorem pre_read (c : State) :
    (pre c).read .rcx = c.read .rdi ∧ (pre c).read .rdx = c.read .rsi ∧
    (pre c).read .r8 = c.read .rdx ∧ (pre c).read .r9 = c.read .rcx ∧
    (pre c).read .rsp = c.read .rsp - 40#64 ∧
    ∀ r, r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .rsp → (pre c).read r = c.read r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pre, Sz.write, Sz.read]
  · simp [pre, Sz.write, Sz.read]
  · simp [pre, Sz.write, Sz.read]
  · simp [pre, Sz.write, Sz.read]
  · simp [pre, Sz.write, Sz.read, Silmaril.X86.Ext.AluOp.resultN]; rfl
  · intro r h1 h2 h3 h4 h5
    simp [pre, Sz.write, Sz.read, State.read_write_other _ _ _ _ h1,
      State.read_write_other _ _ _ _ h2, State.read_write_other _ _ _ _ h3,
      State.read_write_other _ _ _ _ h4, State.read_write_other _ _ _ _ h5]

/-- What the enter code establishes. -/
structure EnterFacts (m m₁ : MState) : Prop where
  rcx : m₁.core.read .rcx = m.core.read .rdi
  rdx : m₁.core.read .rdx = m.core.read .rsi
  r8 : m₁.core.read .r8 = m.core.read .rdx
  r9 : m₁.core.read .r9 = m.core.read .rcx
  other : ∀ r, r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .rsp →
    m₁.core.read r = m.core.read r
  rsp : (m₁.core.read .rsp).toNat = (m.core.read .rsp).toNat - 48
  frame : Memory.WritesOnly m.memory m₁.memory ((m.core.read .rsp).toNat - 48) 8
  pushed : ∃ exit, m₁.memory.readBytes ((m.core.read .rsp).toNat - 48) 8 = some (encodeWords [exit])

theorem enter_run (m : MState) (rel : BitVec 32) (low : 48 ≤ (m.core.read .rsp).toNat)
    (write : m.memory.Permitted .write ((m.core.read .rsp).toNat - 48) 8)
    (read : m.memory.Permitted .read ((m.core.read .rsp).toNat - 48) 8) :
    ∃ m₁, run (callMsEnter rel) m = some m₁ ∧ EnterFacts m m₁ := by
  obtain ⟨hrcx, hrdx, hr8, hr9, hrsp, hother⟩ := pre_read m.core
  have haddr : ((pre m.core).read .rsp - 8#64).toNat = (m.core.read .rsp).toNat - 48 := by
    rw [hrsp]; bv_omega
  let v := (pre m.core).rip + BitVec.ofNat 64 (Silmaril.X86.Insn.call rel).length
  obtain ⟨⟨t, mem⟩, hp⟩ : ∃ r, pushWord (pre m.core) m.memory v = some r :=
    ⟨_, Silmaril.X86.pushWord_eq_some (by rw [haddr]; exact write)⟩
  have ht := Silmaril.X86.pushWord_state hp
  refine ⟨⟨{ t with rip := v + rel.signExtend 64 }, mem⟩, ?_, ?_⟩
  · show run (callMsPre ++ [.call rel]) m = _
    rw [run_pre]
    simp [run, exec_call, Silmaril.X86.Insn.exec, hp, v]
  · have tread : ∀ r, r ≠ .rsp → t.read r = (pre m.core).read r := by
      intro r hr; rw [ht]; exact State.read_write_other _ _ _ _ hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show t.read .rcx = _; rw [tread _ (by decide), hrcx]
    · show t.read .rdx = _; rw [tread _ (by decide), hrdx]
    · show t.read .r8 = _; rw [tread _ (by decide), hr8]
    · show t.read .r9 = _; rw [tread _ (by decide), hr9]
    · intro r h1 h2 h3 h4 h5
      show t.read r = _
      rw [tread _ h5, hother r h1 h2 h3 h4 h5]
    · show (t.read .rsp).toNat = _
      rw [ht, State.read_write_same, ← haddr]
    · have := Silmaril.X86.pushWord_writesOnly hp
      rwa [haddr] at this
    · refine ⟨v, ?_⟩
      have := Silmaril.X86.pushWord_readBytes hp (by rw [haddr]; exact read)
      rwa [haddr] at this

/-- What the leave code establishes. -/
structure LeaveFacts (exit : BitVec 64) (m₂ m₃ : MState) : Prop where
  pc : m₃.core.rip = exit
  rsp : m₃.core.read .rsp = m₂.core.read .rsp + 40#64 + 8#64
  other : ∀ r, r ≠ .rsp → m₃.core.read r = m₂.core.read r

theorem leave_run (m₂ : MState) (exit : BitVec 64)
    (slot : m₂.memory.readBytes (m₂.core.read .rsp + 40#64).toNat 8 = some (encodeWords [exit])) :
    ∃ m₃, run callMsLeave m₂ = some m₃ ∧ LeaveFacts exit m₂ m₃ := by
  let c' : State :=
    { Sz.q.write m₂.core .rsp
        (Silmaril.X86.Ext.AluOp.resultN .add (Sz.q.read m₂.core .rsp) ((0x28#8).signExtend 64)) with
      flags := Silmaril.X86.Ext.AluOp.flagsN .add (Sz.q.read m₂.core .rsp) ((0x28#8).signExtend 64)
      rip := m₂.core.rip + BitVec.ofNat 64 (Instr.aluI8 .q .add (.reg .rsp) 0x28).length }
  have hc : c'.read .rsp = m₂.core.read .rsp + 40#64 := by
    simp [c', Sz.write, Silmaril.X86.Ext.AluOp.resultN]; rfl
  have hother : ∀ r, r ≠ .rsp → c'.read r = m₂.core.read r := by
    intro r hr; simp [c', Sz.write, State.read_write_other _ _ _ _ hr]
  have hpop := Silmaril.X86.popWord_of_readBytes (s := c') (memory := m₂.memory)
    (by rw [hc]; exact slot)
  refine ⟨⟨{ c'.write .rsp (c'.read .rsp + 8#64) with rip := exit }, m₂.memory⟩, ?_, ?_⟩
  · simp only [callMsLeave, run]
    rw [exec_aluI8_reg _ _ _ _ _ _ (by decide)]
    simp only [exec_ret, Silmaril.X86.Insn.exec]
    erw [hpop]
    rfl
  · refine ⟨rfl, ?_, ?_⟩
    · show (c'.write .rsp (c'.read .rsp + 8#64)).read .rsp = _
      rw [State.read_write_same, hc]
    · intro r hr
      show (c'.write .rsp (c'.read .rsp + 8#64)).read r = _
      rw [State.read_write_other _ _ _ _ hr, hother r hr]

variable {p : Proto} {rel : BitVec 32}

/-- The System V entry facts the transition uses. -/
theorem sysv_entry_facts (options : Options) {a} {s : Ffi.State}
    (entry : (sysv options).Entry p a s) :
    ((reg s .rsp).toNat + 8) % 16 = 0 ∧ ∃ exit,
      s.machine.memory.readBytes (reg s .rsp).toNat 8 = some (encodeWords [exit]) := by
  obtain ⟨exit, h⟩ := entry
  exact ⟨h.alignment, exit, h.returnAddress⟩

theorem mem_enter (options : Options) {s s₁ : Ffi.State}
    (entered : s₁ ∈ (callMs (sysv options) win64 p rel).enter s) :
    ∃ m₁, run (callMsEnter rel) s.machine = some m₁ ∧ s₁ = { s with machine := m₁ } := entered

theorem callMs_enter (options : Options) {a} {s s₁ : Ffi.State}
    (entry : (sysv options).Entry p a s) (room : CallMs.Room s)
    (entered : s₁ ∈ (callMs (sysv options) win64 p rel).enter s) :
    SysvToMs.Enter s s₁ ∧ EnterFacts s.machine s₁.machine := by
  obtain ⟨m₁, hrun, rfl⟩ := mem_enter options entered
  obtain ⟨m₁', hrun', facts⟩ := enter_run s.machine rel room.low room.write room.read
  rw [hrun] at hrun'
  cases hrun'
  obtain ⟨align, -⟩ := sysv_entry_facts options entry
  have hlt := (reg s .rsp).isLt
  refine ⟨⟨facts.rcx, facts.rdx, facts.r8, facts.r9, ?_, ⟨?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩,
    facts⟩
  · intro r mem
    have : r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .rsp := by revert r; decide
    exact facts.other r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2
  · show ((m₁.core.read .rsp).toNat + 8) % 16 = 0
    rw [facts.rsp]
    have := room.low
    simp only [reg] at align this
    omega
  · show (m₁.core.read .rsp).toNat + 8 + 32 ≤ 2 ^ 64
    rw [facts.rsp]
    simp only [reg] at hlt
    omega
  · show ∃ exit, m₁.memory.readBytes (m₁.core.read .rsp).toNat 8 = some (encodeWords [exit])
    rw [facts.rsp]
    exact facts.pushed

/-- On a well-behaved return that keeps the caller's slot, the leave code runs. -/
theorem callMs_leave_run (options : Options) {a} {s s₁ s₂ : Ffi.State}
    (entry : (sysv options).Entry p a s) (room : CallMs.Room s)
    (entered : s₁ ∈ (callMs (sysv options) win64 p rel).enter s)
    (proper : win64.Proper p s₁ s₂) (guar : CallMs.Guar s₁ s₂) :
    ∃ exit, s.machine.memory.readBytes (reg s .rsp).toNat 8 = some (encodeWords [exit]) ∧
      ∃ m₃, run callMsLeave s₂.machine = some m₃ ∧ LeaveFacts exit s₂.machine m₃ ∧
        m₃.core.read .rsp = reg s .rsp + 8#64 := by
  obtain ⟨-, facts⟩ := callMs_enter options entry room entered
  obtain ⟨-, exit, ra⟩ := sysv_entry_facts options entry
  obtain ⟨_e, -, back⟩ := proper.1
  have hstack : reg s₂ .rsp = reg s₁ .rsp + 8 := back.stack
  have low := room.low
  have h1 := facts.rsp
  have hlt := (reg s .rsp).isLt
  simp only [reg] at hstack low h1 hlt
  have haddr : (s₂.machine.core.read .rsp + 40#64).toNat =
      (s₁.machine.core.read .rsp).toNat + 48 := by
    rw [hstack]; bv_omega
  have hslot : s₂.machine.memory.readBytes (s₂.machine.core.read .rsp + 40#64).toNat 8 =
      some (encodeWords [exit]) := by
    rw [haddr, guar, h1, show (s.machine.core.read .rsp).toNat - 48 + 48 =
      (s.machine.core.read .rsp).toNat by omega]
    rw [← ra]
    apply Memory.WritesWithin.readBytes
      ((Memory.writesOnly_iff_writesWithin _ _ _ _).1 facts.frame)
    intro offset _ h
    omega
  obtain ⟨m₃, hrun, lf⟩ := leave_run s₂.machine exit hslot
  refine ⟨exit, ra, m₃, hrun, lf, ?_⟩
  rw [lf.rsp, hstack]
  apply BitVec.eq_of_toNat_eq
  simp only [reg]
  bv_omega

theorem implements (options : Options) :
    Implements (callMs (sysv options) win64 p rel) SysvToMs.Enter SysvToMs.Leave
      CallMs.Room CallMs.Guar where
  enter _ _ entry room _ entered := (callMs_enter options entry room entered).1
  leave a s entry room s₁ entered s₂ proper guar s₃ left := by
    obtain ⟨exit, ra, m₃, hrun, lf, hrsp⟩ :=
      callMs_leave_run options entry room entered proper guar
    obtain ⟨m₃', hrun', rfl⟩ := left
    rw [hrun] at hrun'
    cases hrun'
    refine ⟨⟨exit, ra, lf.pc⟩, hrsp, lf.other _ (by decide), ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    intro r mem
    exact lf.other r (by revert r; decide)

theorem progress (options : Options) :
    Progress (callMs (sysv options) win64 p rel) CallMs.Room CallMs.Guar where
  enter _ s _ room := by
    obtain ⟨m₁, hrun, -⟩ := enter_run s.machine rel room.low room.write room.read
    exact ⟨_, m₁, hrun, rfl⟩
  leave _ _ entry room _ entered s₂ proper guar := by
    obtain ⟨-, -, m₃, hrun, -⟩ := callMs_leave_run options entry room entered proper guar
    exact ⟨_, m₃, hrun, rfl⟩

end Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc

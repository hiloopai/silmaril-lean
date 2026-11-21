module

public import Silmaril.X86.Decompile.RightRot.Defs
public import Silmaril.X86.Open.Thms

/-!
# Proofs: the `right_rot` run on the open machine, with the footprint of every state

`Silmaril.X86.Decompile.RightRot.right_rot_returns` (Raw, via the header
`Silmaril.X86.Decompile.RightRot.Defs`) concludes an `Ext.Returns` run and the final
state's `Post`; it says nothing about the states in between. A stable triple needs them.

`run_stable` replays the certificate's per-instruction proof, **copied verbatim** from the
`certify_right_rot_returns` macro of `Silmaril/Raw/X86/Decompile/RightRot.lean`
(the per-instruction part of that macro and its `rax` and callee-saved `Post` bullets;
the only edit is
`storeN_isSome` qualified as `Decompile.storeN_isSome`), and replaces its `Ext.Returns`
conclusion by:

* the fifteen steps as a run of `Open.step` (`Ext.stepOpt → Ext8.stepOpt → Open.step` for
  the fourteen retirements, `Ext.step = .returned → Open.step` for the `ret`);
* `Within m mk` for **every** state `mk` of the run: registers other than `rsp`, `rbp`,
  `rax`, `rcx`, `rdx` are unchanged, and memory is written only in the sixteen frame bytes
  below the entry `rsp` (`Memory.WritesOnly`, which also keeps the mappings).

`rbp` is *not* unchanged in the middle of the run (it holds the post-push `rsp`), although
`Post` restores it: this is exactly why the System V triple of `right_rot` (whose frame
holds the callee-saved registers) is not stable, and why the stable triple of
`Safe/Stable/RightRot` owns `rbp`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SafeStable.RightRot

open Silmaril
open Silmaril.X86
open Silmaril.X86.Ext
open Silmaril.X86.Decompile
open Silmaril.X86.Decompile.RightRot
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Machine.Execution (run run_zero run_succ)

/-- The footprint of a state of the `right_rot` run, relative to its entry state. -/
def Within (m mk : MState) : Prop :=
  (∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
      mk.core.read r = m.core.read r) ∧
    Memory.WritesOnly m.memory mk.memory ((m.core.read .rsp).toNat - 16) 16

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- **`right_rot` on the open machine, with every intermediate state's footprint.** -/
theorem run_stable :
    ∀ {entry exit : Word} {m : MState}, Entry entry exit m →
      ∃ final, run Silmaril.X86.Open.step 15 m = some final ∧ final.core.rip = exit ∧
        Post (rightRotSpec (args m).1 (args m).2) m final ∧
        ∀ k ≤ 15, ∀ mk, run Silmaril.X86.Open.step k m = some mk → Within m mk := by
    intro entry exit m h
    obtain ⟨hrip, himage, hretaddr, hfw, hfr, hsplow, hapart, hcpos, hclt⟩ := h
    simp only [args, Post]
    -- ### Bounds and addresses
    have hcl : code.length = 37 := by decide
    have hb : entry.toNat + 37 ≤ 2 ^ 64 := by
      have hbb := himage.bound; rw [hcl] at hbb; exact hbb
    have hsplt : (m.core.read .rsp).toNat < 2 ^ 64 := (m.core.read .rsp).isLt
    have hsp8 : (m.core.read .rsp - 8#64).toNat = (m.core.read .rsp).toNat - 8 :=
      toNat_sub_lit (k := 8) (by omega) (by omega)
    have hsp12 : (m.core.read .rsp - 12#64).toNat = (m.core.read .rsp).toNat - 12 :=
      toNat_sub_lit (k := 12) (by omega) (by omega)
    have hsp16 : (m.core.read .rsp - 16#64).toNat = (m.core.read .rsp).toNat - 16 :=
      toNat_sub_lit (k := 16) (by omega) (by omega)
    -- Anything inside the frame is disjoint from the code.
    have hdis : ∀ a l : Nat, (m.core.read .rsp).toNat - 16 ≤ a →
        a + l ≤ (m.core.read .rsp).toNat →
        entry.toNat + code.length ≤ a ∨ a + l ≤ entry.toNat := by
      intro a l h1 h2
      rw [hcl]
      rcases hapart with hap | hap
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    -- Permissions, transported along the chain of writes (which keep the regions).
    have permOf : ∀ {a b : Memory}, b.regions = a.regions → ∀ {acc : Process.Access} {ad l : Nat},
        a.Permitted acc ad l → b.Permitted acc ad l := by
      intro a b hr acc ad l hp
      rw [Memory.Permitted, X86.Memory.checkSpan_congr hr]
      exact hp
    have hpushW : m.memory.Permitted .write (m.core.read .rsp - 8#64).toNat 8 := by
      rw [hsp8]
      have hs := permitted_sub hfw (off := 8) (count := 8) (by omega) (by omega)
      rwa [show (m.core.read .rsp).toNat - 16 + 8 = (m.core.read .rsp).toNat - 8 by omega] at hs
    have hpushR : m.memory.Permitted .read (m.core.read .rsp - 8#64).toNat 8 := by
      rw [hsp8]
      have hs := permitted_sub hfr (off := 8) (count := 8) (by omega) (by omega)
      rwa [show (m.core.read .rsp).toNat - 16 + 8 = (m.core.read .rsp).toNat - 8 by omega] at hs
    have hs12W : m.memory.Permitted .write (m.core.read .rsp - 12#64).toNat 4 := by
      rw [hsp12]
      have hs := permitted_sub hfw (off := 4) (count := 4) (by omega) (by omega)
      rwa [show (m.core.read .rsp).toNat - 16 + 4 = (m.core.read .rsp).toNat - 12 by omega] at hs
    have hs12R : m.memory.Permitted .read (m.core.read .rsp - 12#64).toNat 4 := by
      rw [hsp12]
      have hs := permitted_sub hfr (off := 4) (count := 4) (by omega) (by omega)
      rwa [show (m.core.read .rsp).toNat - 16 + 4 = (m.core.read .rsp).toNat - 12 by omega] at hs
    have hs16W : m.memory.Permitted .write (m.core.read .rsp - 16#64).toNat 4 := by
      rw [hsp16]
      have hs := permitted_sub hfw (off := 0) (count := 4) (by omega) (by omega)
      rwa [Nat.add_zero] at hs
    have hs16R : m.memory.Permitted .read (m.core.read .rsp - 16#64).toNat 4 := by
      rw [hsp16]
      have hs := permitted_sub hfr (off := 0) (count := 4) (by omega) (by omega)
      rwa [Nat.add_zero] at hs
    -- `[rbp - 4]` and `[rbp - 8]` once `rbp` holds the post-push `rsp`.
    have hframe4 : ∀ (t : State) (nxt : Word), t.read .rbp = m.core.read .rsp - 8#64 →
        (frame 0xFFFFFFFC).addr t nxt = m.core.read .rsp - 12#64 := by
      intro t nxt ht
      rw [frame_addr, ht, addr4]
    have hframe8 : ∀ (t : State) (nxt : Word), t.read .rbp = m.core.read .rsp - 8#64 →
        (frame 0xFFFFFFF8).addr t nxt = m.core.read .rsp - 16#64 := by
      intro t nxt ht
      rw [frame_addr, ht, addr8]
    have hdb : Sz.d.bytes = 4 := rfl
    have hrip₀ : m.core.rip.toNat = entry.toNat + 0 := by rw [hrip]; omega
    -- The register-read tactic used throughout: unfold the state updates `exec`
    -- produced and discharge the register disequalities.
    -- ### c90  55                 push %rbp
    obtain ⟨mem₁, hmem₁⟩ : ∃ mm : Memory, X86.pushWord m.core m.memory (m.core.read .rbp) =
        some (m.core.write .rsp (m.core.read .rsp - 8#64), mm) :=
      ⟨_, X86.pushWord_eq_some hpushW⟩
    obtain ⟨c₁, hc₁⟩ : ∃ c : State, c =
        { m.core.write .rsp (m.core.read .rsp - 8#64) with
          rip := m.core.rip + BitVec.ofNat 64 (X86.Insn.push Reg.rbp).length } := ⟨_, rfl⟩
    have e₀ : Ext.exec (.push .rbp) m.core m.memory = .ok c₁ mem₁ := by
      rw [Ext.exec_push, hc₁]
      simp only [X86.Insn.exec, hmem₁, Option.map_some]
    have hstep₀ : Ext.stepOpt exit m = some ⟨c₁, mem₁⟩ :=
      retires_instr himage 0 (.push .rbp) hrip₀ (by decide) (by decide) (by decide) e₀
    have hwo₁ : Memory.WritesOnly m.memory mem₁ (m.core.read .rsp - 8#64).toNat 8 :=
      X86.pushWord_writesOnly hmem₁
    have hreg₁ : mem₁.regions = m.memory.regions := hwo₁.1
    have himg₁ : Image code entry mem₁ :=
      Image.of_writesOnly himage hwo₁ (by rw [hsp8]; exact hdis _ 8 (by omega) (by omega))
    have hrip₁ : c₁.rip.toNat = entry.toNat + 1 := by
      rw [hc₁]; rw [L0]; exact rip_step (len := 1) hrip₀ (by omega)
    have hc₁rsp : c₁.read .rsp = m.core.read .rsp - 8#64 := by simp [hc₁]
    have hc₁oth : ∀ r : Reg, r ≠ .rsp → c₁.read r = m.core.read r := by
      intro r hr; simp [hc₁, hr]
    -- ### c91  48 89 e5           mov %rsp,%rbp
    obtain ⟨c₂, hc₂⟩ : ∃ c : State, c =
        { Sz.q.write c₁ .rbp (Sz.q.read c₁ .rsp) with
          rip := c₁.rip + BitVec.ofNat 64 (Ext.Instr.mov .q (.reg Reg.rbp) Reg.rsp).length } :=
      ⟨_, rfl⟩
    have e₁ : Ext.exec (.mov .q (.reg .rbp) .rsp) c₁ mem₁ = .ok c₂ mem₁ := by
      rw [hc₂]; exact Ext.exec_mov_reg c₁ mem₁ .q .rbp .rsp
    have hstep₁ : Ext.stepOpt exit ⟨c₁, mem₁⟩ = some ⟨c₂, mem₁⟩ :=
      retires_instr himg₁ 1 (.mov .q (.reg .rbp) .rsp) hrip₁ (by decide) (by decide) (by decide) e₁
    have hrip₂ : c₂.rip.toNat = entry.toNat + 4 := by
      rw [hc₂]; rw [L1]; exact rip_step (len := 3) hrip₁ (by omega)
    have hc₂rbp : c₂.read .rbp = m.core.read .rsp - 8#64 := by simp [hc₂, hc₁rsp]
    have hc₂oth : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₂.read r = m.core.read r := by
      intro r h1 h2; simp [hc₂, h2, hc₁oth r h1]
    have hc₂rdi : Sz.d.read c₂ .rdi = Sz.d.read m.core .rdi := by
      simp only [Sz.read, hc₂oth .rdi (by decide) (by decide)]
    have hc₂rsi : Sz.d.read c₂ .rsi = Sz.d.read m.core .rsi := by
      simp only [Sz.read, hc₂oth .rsi (by decide) (by decide)]
    have hc₂rsp : c₂.read .rsp = m.core.read .rsp - 8#64 := by simp [hc₂, hc₁rsp]
    -- ### c94  89 7d fc           mov %edi,-0x4(%rbp)
    obtain ⟨mem₂, hst₂⟩ := Decompile.storeN_isSome (memory := mem₁)
      (address := m.core.read .rsp - 12#64) (k := 4)
      (v := (Sz.d.read m.core .rdi).setWidth 64) (permOf hreg₁ hs12W)
    obtain ⟨c₃, hc₃⟩ : ∃ c : State, c =
        { c₂ with rip := c₂.rip +
          BitVec.ofNat 64 (Ext.Instr.mov .d (.mem (frame 0xFFFFFFFC)) Reg.rdi).length } := ⟨_, rfl⟩
    have e₂ : Ext.exec (.mov .d (.mem (frame 0xFFFFFFFC)) .rdi) c₂ mem₁ = .ok c₃ mem₂ := by
      rw [Ext.exec_store, hframe4 _ _ hc₂rbp, hdb, hc₂rdi, hst₂, hc₃]
    have hstep₂ : Ext.stepOpt exit ⟨c₂, mem₁⟩ = some ⟨c₃, mem₂⟩ :=
      retires_instr himg₁ 4 (.mov .d (.mem (frame 0xFFFFFFFC)) .rdi) hrip₂
        (by decide) (by decide) (by decide) e₂
    have hwo₂ : Memory.WritesOnly mem₁ mem₂ (m.core.read .rsp - 12#64).toNat 4 :=
      Ext.storeN_writesOnly hst₂
    have hreg₂ : mem₂.regions = m.memory.regions := hwo₂.1.trans hreg₁
    have himg₂ : Image code entry mem₂ :=
      Image.of_writesOnly himg₁ hwo₂ (by rw [hsp12]; exact hdis _ 4 (by omega) (by omega))
    have hrip₃ : c₃.rip.toNat = entry.toNat + 7 := by
      rw [hc₃]; rw [L2]; exact rip_step (len := 3) hrip₂ (by omega)
    have hc₃rbp : c₃.read .rbp = m.core.read .rsp - 8#64 := by simp [hc₃, hc₂rbp]
    have hc₃oth : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₃.read r = m.core.read r := by
      intro r h1 h2; simp [hc₃, hc₂oth r h1 h2]
    have hc₃rsi : Sz.d.read c₃ .rsi = Sz.d.read m.core .rsi := by
      simp only [Sz.read, hc₃oth .rsi (by decide) (by decide)]
    -- ### c97  89 75 f8           mov %esi,-0x8(%rbp)
    obtain ⟨mem₃, hst₃⟩ := Decompile.storeN_isSome (memory := mem₂)
      (address := m.core.read .rsp - 16#64) (k := 4)
      (v := (Sz.d.read m.core .rsi).setWidth 64) (permOf hreg₂ hs16W)
    obtain ⟨c₄, hc₄⟩ : ∃ c : State, c =
        { c₃ with rip := c₃.rip +
          BitVec.ofNat 64 (Ext.Instr.mov .d (.mem (frame 0xFFFFFFF8)) Reg.rsi).length } := ⟨_, rfl⟩
    have e₃ : Ext.exec (.mov .d (.mem (frame 0xFFFFFFF8)) .rsi) c₃ mem₂ = .ok c₄ mem₃ := by
      rw [Ext.exec_store, hframe8 _ _ hc₃rbp, hdb, hc₃rsi, hst₃, hc₄]
    have hstep₃ : Ext.stepOpt exit ⟨c₃, mem₂⟩ = some ⟨c₄, mem₃⟩ :=
      retires_instr himg₂ 7 (.mov .d (.mem (frame 0xFFFFFFF8)) .rsi) hrip₃
        (by decide) (by decide) (by decide) e₃
    have hwo₃ : Memory.WritesOnly mem₂ mem₃ (m.core.read .rsp - 16#64).toNat 4 :=
      Ext.storeN_writesOnly hst₃
    have himg₃ : Image code entry mem₃ :=
      Image.of_writesOnly himg₂ hwo₃ (by rw [hsp16]; exact hdis _ 4 (by omega) (by omega))
    have hrip₄ : c₄.rip.toNat = entry.toNat + 10 := by
      rw [hc₄]; rw [L3]; exact rip_step (len := 3) hrip₃ (by omega)
    have hc₄rbp : c₄.read .rbp = m.core.read .rsp - 8#64 := by simp [hc₄, hc₃rbp]
    have hc₄oth : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₄.read r = m.core.read r := by
      intro r h1 h2; simp [hc₄, hc₃oth r h1 h2]
    -- ### The two reload facts, once both arguments are spilled.
    have hload12 : Ext.loadN mem₃ (m.core.read .rsp - 12#64) 4 =
        some (BitVec.ofNat 64 (((Sz.d.read m.core .rdi).setWidth 64).toNat % 2 ^ (8 * 4))) := by
      rw [Ext.loadN_storeN_disjoint hst₃ (by rw [hsp12, hsp16]; omega)]
      exact Ext.loadN_storeN hst₂ (permOf hreg₁ hs12R)
    have hload16 : Ext.loadN mem₃ (m.core.read .rsp - 16#64) 4 =
        some (BitVec.ofNat 64 (((Sz.d.read m.core .rsi).setWidth 64).toNat % 2 ^ (8 * 4))) :=
      Ext.loadN_storeN hst₃ (permOf hreg₂ hs16R)
    -- ### The state-to-state read lemmas: each body instruction writes one register.
    have szr : ∀ {a b : State} {r : Reg}, a.read r = b.read r → Sz.d.read a r = Sz.d.read b r := by
      intro a b r hh; simp only [Sz.read, hh]
    have hc₃rsp : c₃.read .rsp = m.core.read .rsp - 8#64 := by simp [hc₃, hc₂rsp]
    have hc₄rsp : c₄.read .rsp = m.core.read .rsp - 8#64 := by simp [hc₄, hc₃rsp]
    -- ### c9a  8b 45 fc           mov -0x4(%rbp),%eax
    obtain ⟨c₅, hc₅⟩ : ∃ c : State, c =
        { Sz.d.write c₄ .rax (Sz.d.read m.core .rdi) with
          rip := c₄.rip +
            BitVec.ofNat 64 (Ext.Instr.load .d Reg.rax (frame 0xFFFFFFFC)).length } := ⟨_, rfl⟩
    have e₄ : Ext.exec (.load .d .rax (frame 0xFFFFFFFC)) c₄ mem₃ = .ok c₅ mem₃ := by
      rw [Ext.exec_load, hframe4 _ _ hc₄rbp, hdb, hload12]
      simp only [reload_setWidth, hc₅]
    have hstep₄ : Ext.stepOpt exit ⟨c₄, mem₃⟩ = some ⟨c₅, mem₃⟩ :=
      retires_instr himg₃ 10 (.load .d .rax (frame 0xFFFFFFFC)) hrip₄
        (by decide) (by decide) (by decide) e₄
    have hrip₅ : c₅.rip.toNat = entry.toNat + 13 := by
      rw [hc₅]; rw [L4]; exact rip_step (len := 3) hrip₄ (by omega)
    have hr₅ : ∀ r : Reg, r ≠ .rax → c₅.read r = c₄.read r := by
      intro r hh; rw [hc₅]; exact Sz.read_write_other _ _ _ _ _ hh
    have hv₅ : Sz.d.read c₅ .rax = Sz.d.read m.core .rdi := by
      simp only [hc₅, szRead_setRip, Sz.read_write]
    -- ### c9d  8b 4d f8           mov -0x8(%rbp),%ecx
    obtain ⟨c₆, hc₆⟩ : ∃ c : State, c =
        { Sz.d.write c₅ .rcx (Sz.d.read m.core .rsi) with
          rip := c₅.rip +
            BitVec.ofNat 64 (Ext.Instr.load .d Reg.rcx (frame 0xFFFFFFF8)).length } := ⟨_, rfl⟩
    have e₅ : Ext.exec (.load .d .rcx (frame 0xFFFFFFF8)) c₅ mem₃ = .ok c₆ mem₃ := by
      rw [Ext.exec_load, hframe8 _ _ ((hr₅ .rbp (by decide)).trans hc₄rbp), hdb, hload16]
      simp only [reload_setWidth, hc₆]
    have hstep₅ : Ext.stepOpt exit ⟨c₅, mem₃⟩ = some ⟨c₆, mem₃⟩ :=
      retires_instr himg₃ 13 (.load .d .rcx (frame 0xFFFFFFF8)) hrip₅
        (by decide) (by decide) (by decide) e₅
    have hrip₆ : c₆.rip.toNat = entry.toNat + 16 := by
      rw [hc₆]; rw [L5]; exact rip_step (len := 3) hrip₅ (by omega)
    have hr₆ : ∀ r : Reg, r ≠ .rcx → c₆.read r = c₅.read r := by
      intro r hh; rw [hc₆]; exact Sz.read_write_other _ _ _ _ _ hh
    have hv₆ : Sz.d.read c₆ .rax = Sz.d.read m.core .rdi :=
      (szr (hr₆ .rax (by decide))).trans hv₅
    have hcnt₆ : (Count.cl.raw c₆).toNat % Sz.d.bits = (Sz.d.read m.core .rsi).toNat := by
      have hrcx : c₆.read .rcx = (Sz.d.read m.core .rsi).setWidth 64 := by
        simp only [hc₆, read_setRip, read_szWrite_same]
      simp only [Count.raw, hrcx]
      exact masked_count _ hclt
    -- ### ca0  d3 e8              shr %cl,%eax
    obtain ⟨c₇, hc₇⟩ : ∃ c : State, c =
        { Sz.d.write c₆ .rax
            (ShiftOp.shr.result (Sz.d.read c₆ .rax) ((Count.cl.raw c₆).toNat % Sz.d.bits)) with
          flags := ShiftOp.shr.flags (Sz.d.read c₆ .rax)
            ((Count.cl.raw c₆).toNat % Sz.d.bits) c₆.flags
          rip := c₆.rip +
            BitVec.ofNat 64 (Ext.Instr.shift .d .shr (.reg Reg.rax) .cl).length } := ⟨_, rfl⟩
    have e₆ : Ext.exec (.shift .d .shr (.reg .rax) .cl) c₆ mem₃ = .ok c₇ mem₃ := by
      rw [hc₇]; exact Ext.exec_shift_reg c₆ mem₃ .d .shr .rax .cl
    have hstep₆ : Ext.stepOpt exit ⟨c₆, mem₃⟩ = some ⟨c₇, mem₃⟩ :=
      retires_instr himg₃ 16 (.shift .d .shr (.reg .rax) .cl) hrip₆
        (by decide) (by decide) (by decide) e₆
    have hrip₇ : c₇.rip.toNat = entry.toNat + 18 := by
      rw [hc₇]; rw [L6]; exact rip_step (len := 2) hrip₆ (by omega)
    have hr₇ : ∀ r : Reg, r ≠ .rax → c₇.read r = c₆.read r := by
      intro r hh; rw [hc₇]; exact Sz.read_write_other _ _ _ _ _ hh
    have hshr : Sz.d.read c₇ .rax =
        ShiftOp.shr.result (Sz.d.read m.core .rdi) (Sz.d.read m.core .rsi).toNat := by
      simp only [hc₇, szRead_setFlagsRip, Sz.read_write, hv₆, hcnt₆]
    -- ### ca2  8b 55 fc           mov -0x4(%rbp),%edx
    obtain ⟨c₈, hc₈⟩ : ∃ c : State, c =
        { Sz.d.write c₇ .rdx (Sz.d.read m.core .rdi) with
          rip := c₇.rip +
            BitVec.ofNat 64 (Ext.Instr.load .d Reg.rdx (frame 0xFFFFFFFC)).length } := ⟨_, rfl⟩
    have e₇ : Ext.exec (.load .d .rdx (frame 0xFFFFFFFC)) c₇ mem₃ = .ok c₈ mem₃ := by
      rw [Ext.exec_load, hframe4 _ _ ((hr₇ .rbp (by decide)).trans
        ((hr₆ .rbp (by decide)).trans ((hr₅ .rbp (by decide)).trans hc₄rbp))), hdb, hload12]
      simp only [reload_setWidth, hc₈]
    have hstep₇ : Ext.stepOpt exit ⟨c₇, mem₃⟩ = some ⟨c₈, mem₃⟩ :=
      retires_instr himg₃ 18 (.load .d .rdx (frame 0xFFFFFFFC)) hrip₇
        (by decide) (by decide) (by decide) e₇
    have hrip₈ : c₈.rip.toNat = entry.toNat + 21 := by
      rw [hc₈]; rw [L7]; exact rip_step (len := 3) hrip₇ (by omega)
    have hr₈ : ∀ r : Reg, r ≠ .rdx → c₈.read r = c₇.read r := by
      intro r hh; rw [hc₈]; exact Sz.read_write_other _ _ _ _ _ hh
    have hv₈ : Sz.d.read c₈ .rdx = Sz.d.read m.core .rdi := by
      simp only [hc₈, szRead_setRip, Sz.read_write]
    -- ### ca5  b9 20 00 00 00     mov $0x20,%ecx
    obtain ⟨c₉, hc₉⟩ : ∃ c : State, c =
        { c₈.write .rcx ((0x20 : BitVec 32).setWidth 64) with
          rip := c₈.rip + BitVec.ofNat 64 (Ext.Instr.movI32 Reg.rcx 0x20).length } := ⟨_, rfl⟩
    have e₈ : Ext.exec (.movI32 .rcx 0x20) c₈ mem₃ = .ok c₉ mem₃ := by
      rw [hc₉]; exact Ext.exec_movI32 c₈ mem₃ .rcx 0x20
    have hstep₈ : Ext.stepOpt exit ⟨c₈, mem₃⟩ = some ⟨c₉, mem₃⟩ :=
      retires_instr himg₃ 21 (.movI32 .rcx 0x20) hrip₈ (by decide) (by decide) (by decide) e₈
    have hrip₉ : c₉.rip.toNat = entry.toNat + 26 := by
      rw [hc₉]; rw [L8]; exact rip_step (len := 5) hrip₈ (by omega)
    have hr₉ : ∀ r : Reg, r ≠ .rcx → c₉.read r = c₈.read r := by
      intro r hh; rw [hc₉]; exact State.read_write_other _ _ _ _ hh
    have hv₉rcx : Sz.d.read c₉ .rcx = (0x20 : BitVec Sz.d.bits) := by
      simp only [hc₉, Sz.read, read_setRip, State.read_write_same]
      decide
    -- ### caa  2b 4d f8           sub -0x8(%rbp),%ecx
    have hc₉rbp : c₉.read .rbp = m.core.read .rsp - 8#64 :=
      (hr₉ .rbp (by decide)).trans ((hr₈ .rbp (by decide)).trans ((hr₇ .rbp (by decide)).trans
        ((hr₆ .rbp (by decide)).trans ((hr₅ .rbp (by decide)).trans hc₄rbp))))
    have hrm : ∀ nxt : Word, Ext.readRM .d (.mem (frame 0xFFFFFFF8)) c₉ mem₃ nxt =
        some (Sz.d.read m.core .rsi) := by
      intro nxt
      simp only [Ext.readRM, hframe8 _ _ hc₉rbp, hdb, hload16, Option.map_some, reload_setWidth]
    obtain ⟨c₁₀, hc₁₀⟩ : ∃ c : State, c =
        { Sz.d.write c₉ .rcx
            (Ext.AluOp.resultN .sub (Sz.d.read c₉ .rcx) (Sz.d.read m.core .rsi)) with
          flags := Ext.AluOp.flagsN .sub (Sz.d.read c₉ .rcx) (Sz.d.read m.core .rsi)
          rip := c₉.rip +
            BitVec.ofNat 64 (Ext.Instr.aluR .d .sub Reg.rcx
              (.mem (frame 0xFFFFFFF8))).length } := ⟨_, rfl⟩
    have e₉ : Ext.exec (.aluR .d .sub .rcx (.mem (frame 0xFFFFFFF8))) c₉ mem₃ = .ok c₁₀ mem₃ := by
      rw [hc₁₀]; exact exec_aluR_mem .d .sub .rcx (frame 0xFFFFFFF8) c₉ mem₃ (by decide) (hrm _)
    have hstep₉ : Ext.stepOpt exit ⟨c₉, mem₃⟩ = some ⟨c₁₀, mem₃⟩ :=
      retires_instr himg₃ 26 (.aluR .d .sub .rcx (.mem (frame 0xFFFFFFF8))) hrip₉
        (by decide) (by decide) (by decide) e₉
    have hrip₁₀ : c₁₀.rip.toNat = entry.toNat + 29 := by
      rw [hc₁₀]; rw [L9]; exact rip_step (len := 3) hrip₉ (by omega)
    have hr₁₀ : ∀ r : Reg, r ≠ .rcx → c₁₀.read r = c₉.read r := by
      intro r hh; rw [hc₁₀]; exact Sz.read_write_other _ _ _ _ _ hh
    have hcnt₁₀ : (Count.cl.raw c₁₀).toNat % Sz.d.bits = 32 - (Sz.d.read m.core .rsi).toNat := by
      have hrcx : c₁₀.read .rcx =
          ((0x20 : BitVec Sz.d.bits) - Sz.d.read m.core .rsi).setWidth 64 := by
        simp only [hc₁₀, read_setFlagsRip, read_szWrite_same, hv₉rcx, Ext.AluOp.resultN]
      simp only [Count.raw, hrcx]
      rw [masked_count _ (by rw [sub_from_32 _ hcpos hclt]; omega)]
      exact sub_from_32 _ hcpos hclt
    have hv₁₀rdx : Sz.d.read c₁₀ .rdx = Sz.d.read m.core .rdi :=
      (szr (hr₁₀ .rdx (by decide))).trans ((szr (hr₉ .rdx (by decide))).trans hv₈)
    -- ### cad  d3 e2              shl %cl,%edx
    obtain ⟨c₁₁, hc₁₁⟩ : ∃ c : State, c =
        { Sz.d.write c₁₀ .rdx
            (ShiftOp.shl.result (Sz.d.read c₁₀ .rdx) ((Count.cl.raw c₁₀).toNat % Sz.d.bits)) with
          flags := ShiftOp.shl.flags (Sz.d.read c₁₀ .rdx)
            ((Count.cl.raw c₁₀).toNat % Sz.d.bits) c₁₀.flags
          rip := c₁₀.rip +
            BitVec.ofNat 64 (Ext.Instr.shift .d .shl (.reg Reg.rdx) .cl).length } := ⟨_, rfl⟩
    have e₁₀ : Ext.exec (.shift .d .shl (.reg .rdx) .cl) c₁₀ mem₃ = .ok c₁₁ mem₃ := by
      rw [hc₁₁]; exact Ext.exec_shift_reg c₁₀ mem₃ .d .shl .rdx .cl
    have hstep₁₀ : Ext.stepOpt exit ⟨c₁₀, mem₃⟩ = some ⟨c₁₁, mem₃⟩ :=
      retires_instr himg₃ 29 (.shift .d .shl (.reg .rdx) .cl) hrip₁₀
        (by decide) (by decide) (by decide) e₁₀
    have hrip₁₁ : c₁₁.rip.toNat = entry.toNat + 31 := by
      rw [hc₁₁]; rw [L10]; exact rip_step (len := 2) hrip₁₀ (by omega)
    have hr₁₁ : ∀ r : Reg, r ≠ .rdx → c₁₁.read r = c₁₀.read r := by
      intro r hh; rw [hc₁₁]; exact Sz.read_write_other _ _ _ _ _ hh
    have hshl : Sz.d.read c₁₁ .rdx =
        ShiftOp.shl.result (Sz.d.read m.core .rdi) (32 - (Sz.d.read m.core .rsi).toNat) := by
      simp only [hc₁₁, szRead_setFlagsRip, Sz.read_write, hv₁₀rdx, hcnt₁₀]
    -- ### caf  89 d1              mov %edx,%ecx
    obtain ⟨c₁₂, hc₁₂⟩ : ∃ c : State, c =
        { Sz.d.write c₁₁ .rcx (Sz.d.read c₁₁ .rdx) with
          rip := c₁₁.rip +
            BitVec.ofNat 64 (Ext.Instr.mov .d (.reg Reg.rcx) Reg.rdx).length } := ⟨_, rfl⟩
    have e₁₁ : Ext.exec (.mov .d (.reg .rcx) .rdx) c₁₁ mem₃ = .ok c₁₂ mem₃ := by
      rw [hc₁₂]; exact Ext.exec_mov_reg c₁₁ mem₃ .d .rcx .rdx
    have hstep₁₁ : Ext.stepOpt exit ⟨c₁₁, mem₃⟩ = some ⟨c₁₂, mem₃⟩ :=
      retires_instr himg₃ 31 (.mov .d (.reg .rcx) .rdx) hrip₁₁
        (by decide) (by decide) (by decide) e₁₁
    have hrip₁₂ : c₁₂.rip.toNat = entry.toNat + 33 := by
      rw [hc₁₂]; rw [L11]; exact rip_step (len := 2) hrip₁₁ (by omega)
    have hr₁₂ : ∀ r : Reg, r ≠ .rcx → c₁₂.read r = c₁₁.read r := by
      intro r hh; rw [hc₁₂]; exact Sz.read_write_other _ _ _ _ _ hh
    have hv₁₂rcx : Sz.d.read c₁₂ .rcx =
        ShiftOp.shl.result (Sz.d.read m.core .rdi) (32 - (Sz.d.read m.core .rsi).toNat) := by
      simp only [hc₁₂, szRead_setRip, Sz.read_write, hshl]
    have hv₁₂rax : Sz.d.read c₁₂ .rax =
        ShiftOp.shr.result (Sz.d.read m.core .rdi) (Sz.d.read m.core .rsi).toNat :=
      (szr (hr₁₂ .rax (by decide))).trans ((szr (hr₁₁ .rax (by decide))).trans
        ((szr (hr₁₀ .rax (by decide))).trans ((szr (hr₉ .rax (by decide))).trans
          ((szr (hr₈ .rax (by decide))).trans hshr))))
    -- ### cb1  09 c8              or %ecx,%eax
    obtain ⟨c₁₃, hc₁₃⟩ : ∃ c : State, c =
        { Sz.d.write c₁₂ .rax
            (Ext.AluOp.resultN .or (Sz.d.read c₁₂ .rax) (Sz.d.read c₁₂ .rcx)) with
          flags := Ext.AluOp.flagsN .or (Sz.d.read c₁₂ .rax) (Sz.d.read c₁₂ .rcx)
          rip := c₁₂.rip +
            BitVec.ofNat 64 (Ext.Instr.alu .d .or (.reg Reg.rax) Reg.rcx).length } := ⟨_, rfl⟩
    have e₁₂ : Ext.exec (.alu .d .or (.reg .rax) .rcx) c₁₂ mem₃ = .ok c₁₃ mem₃ := by
      rw [hc₁₃]; exact Ext.exec_alu_reg c₁₂ mem₃ .d .or .rax .rcx (by decide)
    have hstep₁₂ : Ext.stepOpt exit ⟨c₁₂, mem₃⟩ = some ⟨c₁₃, mem₃⟩ :=
      retires_instr himg₃ 33 (.alu .d .or (.reg .rax) .rcx) hrip₁₂
        (by decide) (by decide) (by decide) e₁₂
    have hrip₁₃ : c₁₃.rip.toNat = entry.toNat + 35 := by
      rw [hc₁₃]; rw [L12]; exact rip_step (len := 2) hrip₁₂ (by omega)
    have hr₁₃ : ∀ r : Reg, r ≠ .rax → c₁₃.read r = c₁₂.read r := by
      intro r hh; rw [hc₁₃]; exact Sz.read_write_other _ _ _ _ _ hh
    -- **The functional conclusion**: `eax` holds the decompiled function's value.
    have hrax : Sz.d.read c₁₃ .rax =
        rightRotSpec (Sz.d.read m.core .rdi) (Sz.d.read m.core .rsi).toNat := by
      simp only [hc₁₃, szRead_setFlagsRip, Sz.read_write, hv₁₂rax, hv₁₂rcx, Ext.AluOp.resultN]
      exact or_shifts_eq _ _
    -- ### cb3  5d                 pop %rbp
    have hrsp₁₃ : c₁₃.read .rsp = m.core.read .rsp - 8#64 := by
      rw [hr₁₃ _ (by decide), hr₁₂ _ (by decide), hr₁₁ _ (by decide), hr₁₀ _ (by decide),
        hr₉ _ (by decide), hr₈ _ (by decide), hr₇ _ (by decide), hr₆ _ (by decide),
        hr₅ _ (by decide)]
      exact hc₄rsp
    have hpb₁ : mem₁.readBytes (m.core.read .rsp - 8#64).toNat 8 =
        some (encodeWords [m.core.read .rbp]) := X86.pushWord_readBytes hmem₁ hpushR
    have hpb₃ : mem₃.readBytes (m.core.read .rsp - 8#64).toNat 8 =
        some (encodeWords [m.core.read .rbp]) := by
      show mem₃.readWith .read _ 8 = _
      rw [X86.Memory.readWith_writesOnly hwo₃ .read _ 8 (by rw [hsp8, hsp16]; omega),
        X86.Memory.readWith_writesOnly hwo₂ .read _ 8 (by rw [hsp8, hsp12]; omega)]
      exact hpb₁
    have hpop : X86.popWord c₁₃ mem₃ =
        some (m.core.read .rbp, c₁₃.write .rsp (c₁₃.read .rsp + 8#64)) :=
      X86.popWord_of_readBytes (by rw [hrsp₁₃]; exact hpb₃)
    obtain ⟨c₁₄, hc₁₄⟩ : ∃ c : State, c =
        { (c₁₃.write .rsp (c₁₃.read .rsp + 8#64)).write .rbp (m.core.read .rbp) with
          rip := c₁₃.rip + BitVec.ofNat 64 (X86.Insn.pop Reg.rbp).length } := ⟨_, rfl⟩
    have e₁₃ : Ext.exec (.pop .rbp) c₁₃ mem₃ = .ok c₁₄ mem₃ := by
      rw [Ext.exec_pop, hc₁₄]
      simp only [X86.Insn.exec, hpop, Option.map_some]
    have hstep₁₃ : Ext.stepOpt exit ⟨c₁₃, mem₃⟩ = some ⟨c₁₄, mem₃⟩ :=
      retires_instr himg₃ 35 (.pop .rbp) hrip₁₃ (by decide) (by decide) (by decide) e₁₃
    have hrip₁₄ : c₁₄.rip.toNat = entry.toNat + 36 := by
      rw [hc₁₄]; rw [L13]; exact rip_step (len := 1) hrip₁₃ (by omega)
    have hr₁₄ : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → c₁₄.read r = c₁₃.read r := by
      intro r h1 h2; simp [hc₁₄, h1, h2]
    have hrbp₁₄ : c₁₄.read .rbp = m.core.read .rbp := by simp [hc₁₄]
    have hrsp₁₄ : c₁₄.read .rsp = m.core.read .rsp := by
      simp only [hc₁₄, read_setRip, State.read_write_other _ _ _ _ (by decide : Reg.rsp ≠ Reg.rbp),
        State.read_write_same, hrsp₁₃]
      exact sp_restore _
    -- ### cb4  c3                 ret
    have hra₃ : mem₃.readBytes (m.core.read .rsp).toNat 8 = some (encodeWords [exit]) := by
      show mem₃.readWith .read _ 8 = _
      rw [X86.Memory.readWith_writesOnly hwo₃ .read _ 8 (by rw [hsp16]; omega),
        X86.Memory.readWith_writesOnly hwo₂ .read _ 8 (by rw [hsp12]; omega),
        X86.Memory.readWith_writesOnly hwo₁ .read _ 8 (by rw [hsp8]; omega)]
      exact hretaddr
    have hpop₂ : X86.popWord c₁₄ mem₃ =
        some (exit, c₁₄.write .rsp (c₁₄.read .rsp + 8#64)) :=
      X86.popWord_of_readBytes (by rw [hrsp₁₄]; exact hra₃)
    obtain ⟨c₁₅, hc₁₅⟩ : ∃ c : State, c =
        { c₁₄.write .rsp (c₁₄.read .rsp + 8#64) with rip := exit } := ⟨_, rfl⟩
    have e₁₄ : Ext.exec .ret c₁₄ mem₃ = .ok c₁₅ mem₃ := by
      rw [Ext.exec_ret, hc₁₅]
      simp only [X86.Insn.exec, hpop₂, Option.map_some]
    have hreturn : Ext.step exit ⟨c₁₄, mem₃⟩ = .returned ⟨c₁₅, mem₃⟩ :=
      returns_ret himg₃ 36 hrip₁₄ (by decide) (by decide) e₁₄ (by simp [hc₁₅])
    -- ### The memory footprint
    have hframe : Memory.WritesOnly m.memory mem₃ ((m.core.read .rsp).toNat - 16) 16 :=
      writesOnly_trans (writesOnly_trans
        (writesOnly_widen hwo₁ (by rw [hsp8]; omega) (by rw [hsp8]; omega))
        (writesOnly_widen hwo₂ (by rw [hsp12]; omega) (by rw [hsp12]; omega)))
        (writesOnly_widen hwo₃ (by rw [hsp16]) (by rw [hsp16]; omega))
    have hr₁₅ : ∀ r : Reg, r ≠ .rsp → c₁₅.read r = c₁₄.read r := by
      intro r hh; rw [hc₁₅]; exact State.read_write_other _ _ _ _ hh
    have hrsp₁₅ : c₁₅.read .rsp = m.core.read .rsp + 8#64 := by
      rw [hc₁₅]
      show (c₁₄.write .rsp (c₁₄.read .rsp + 8#64)).read .rsp = _
      rw [State.read_write_same, hrsp₁₄]
    have hsaved : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₁₅.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5
      rw [hr₁₅ _ h1, hr₁₄ _ h1 h2, hr₁₃ _ h3, hr₁₂ _ h4, hr₁₁ _ h5, hr₁₀ _ h4, hr₉ _ h4,
        hr₈ _ h5, hr₇ _ h3, hr₆ _ h4, hr₅ _ h3]
      exact hc₄oth _ h1 h2
    -- ### The same run on the open machine, and the footprint of every state
    have R1 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₁.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact hc₁oth r h1
    have R2 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₂.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact hc₂oth r h1 h2
    have R3 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₃.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact hc₃oth r h1 h2
    have R4 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₄.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact hc₄oth r h1 h2
    have R5 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₅.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact (hr₅ r h3).trans (R4 r h1 h2 h3 h4 h5)
    have R6 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₆.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact (hr₆ r h4).trans (R5 r h1 h2 h3 h4 h5)
    have R7 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₇.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact (hr₇ r h3).trans (R6 r h1 h2 h3 h4 h5)
    have R8 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₈.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact (hr₈ r h5).trans (R7 r h1 h2 h3 h4 h5)
    have R9 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₉.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact (hr₉ r h4).trans (R8 r h1 h2 h3 h4 h5)
    have R10 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₁₀.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact (hr₁₀ r h4).trans (R9 r h1 h2 h3 h4 h5)
    have R11 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₁₁.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact (hr₁₁ r h5).trans (R10 r h1 h2 h3 h4 h5)
    have R12 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₁₂.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact (hr₁₂ r h4).trans (R11 r h1 h2 h3 h4 h5)
    have R13 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₁₃.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact (hr₁₃ r h3).trans (R12 r h1 h2 h3 h4 h5)
    have R14 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₁₄.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact (hr₁₄ r h1 h2).trans (R13 r h1 h2 h3 h4 h5)
    have R15 : ∀ r : Reg, r ≠ .rsp → r ≠ .rbp → r ≠ .rax → r ≠ .rcx → r ≠ .rdx →
        c₁₅.read r = m.core.read r := by
      intro r h1 h2 h3 h4 h5; exact hsaved r h1 h2 h3 h4 h5
    have w0 : Memory.WritesOnly m.memory m.memory ((m.core.read .rsp).toNat - 16) 16 :=
      ⟨rfl, fun _ _ => rfl⟩
    have w1 : Memory.WritesOnly m.memory mem₁ ((m.core.read .rsp).toNat - 16) 16 :=
      writesOnly_widen hwo₁ (by rw [hsp8]; omega) (by rw [hsp8]; omega)
    have w2 : Memory.WritesOnly m.memory mem₂ ((m.core.read .rsp).toNat - 16) 16 :=
      writesOnly_trans w1 (writesOnly_widen hwo₂ (by rw [hsp12]; omega) (by rw [hsp12]; omega))
    have o0 : Silmaril.X86.Open.step m = some ⟨c₁, mem₁⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₀)
    have o1 : Silmaril.X86.Open.step ⟨c₁, mem₁⟩ = some ⟨c₂, mem₁⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₁)
    have o2 : Silmaril.X86.Open.step ⟨c₂, mem₁⟩ = some ⟨c₃, mem₂⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₂)
    have o3 : Silmaril.X86.Open.step ⟨c₃, mem₂⟩ = some ⟨c₄, mem₃⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₃)
    have o4 : Silmaril.X86.Open.step ⟨c₄, mem₃⟩ = some ⟨c₅, mem₃⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₄)
    have o5 : Silmaril.X86.Open.step ⟨c₅, mem₃⟩ = some ⟨c₆, mem₃⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₅)
    have o6 : Silmaril.X86.Open.step ⟨c₆, mem₃⟩ = some ⟨c₇, mem₃⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₆)
    have o7 : Silmaril.X86.Open.step ⟨c₇, mem₃⟩ = some ⟨c₈, mem₃⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₇)
    have o8 : Silmaril.X86.Open.step ⟨c₈, mem₃⟩ = some ⟨c₉, mem₃⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₈)
    have o9 : Silmaril.X86.Open.step ⟨c₉, mem₃⟩ = some ⟨c₁₀, mem₃⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₉)
    have o10 : Silmaril.X86.Open.step ⟨c₁₀, mem₃⟩ = some ⟨c₁₁, mem₃⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₁₀)
    have o11 : Silmaril.X86.Open.step ⟨c₁₁, mem₃⟩ = some ⟨c₁₂, mem₃⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₁₁)
    have o12 : Silmaril.X86.Open.step ⟨c₁₂, mem₃⟩ = some ⟨c₁₃, mem₃⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₁₂)
    have o13 : Silmaril.X86.Open.step ⟨c₁₃, mem₃⟩ = some ⟨c₁₄, mem₃⟩ :=
      Silmaril.X86.Open.step_of_ext8_stepOpt (Ext8.stepOpt_of_ext hstep₁₃)
    have o14 : Silmaril.X86.Open.step ⟨c₁₄, mem₃⟩ = some ⟨c₁₅, mem₃⟩ := by
      apply Silmaril.X86.Open.step_of_ext8_returned (exit := exit)
      rw [Ext8.step_eq_of_ne_undecodable (by rw [hreturn]; simp), hreturn]
    refine ⟨⟨c₁₅, mem₃⟩, ?_, by simp [hc₁₅], ⟨?_, hrsp₁₅, ?_, hframe⟩, ?_⟩
    · simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
        o14, Option.bind_some]
    · -- the System V result: `eax` holds the decompiled function's value
      show Sz.d.read c₁₅ .rax = _
      rw [szr (hr₁₅ .rax (by decide)), szr (hr₁₄ .rax (by decide) (by decide))]
      exact hrax
    · -- every System V callee-saved register comes back
      intro r hr
      have hcs : r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 :=
        (X86.sysv64_mem_calleeSaved r).mp hr
      rcases hcs with hcs | hcs | hcs | hcs | hcs | hcs
      all_goals subst r
      · exact hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact (hr₁₅ _ (by decide)).trans hrbp₁₄
      · exact hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · intro k hk mk hrk
      match k, hk with
      | 0, _ =>
        simp only [run_zero, Option.some.injEq] at hrk
        subst hrk; exact ⟨fun _ _ _ _ _ _ => rfl, w0⟩
      | 1, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R1, w1⟩
      | 2, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R2, w1⟩
      | 3, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R3, w2⟩
      | 4, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R4, hframe⟩
      | 5, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R5, hframe⟩
      | 6, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R6, hframe⟩
      | 7, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R7, hframe⟩
      | 8, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R8, hframe⟩
      | 9, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R9, hframe⟩
      | 10, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R10, hframe⟩
      | 11, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R11, hframe⟩
      | 12, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R12, hframe⟩
      | 13, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R13, hframe⟩
      | 14, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R14, hframe⟩
      | 15, _ =>
        simp only [run_succ, run_zero, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13,
          o14, Option.bind_some, Option.some.injEq] at hrk
        subst hrk; exact ⟨R15, hframe⟩
      | _ + 16, h => exact absurd h (by omega)

end Silmaril.Proofs.X86.SafeStable.RightRot

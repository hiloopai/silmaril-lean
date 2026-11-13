module

public import Silmaril.Libc.SysWrap.Defs

/-!
# System call wrappers: single steps and the instructions before the call

* `step_of`: a listed instruction that executes is one `Str9G` step (`Str9G.isa.step_of`).
* `PInv`: the machine state agrees with the symbolic state `PSt` of `runPre`; `pstep_sound`,
  `runPre_sound`: every symbolic step is a machine step that keeps it.
-/

@[expose] public section

namespace Silmaril.Proofs.Libc.SysWrap

open Silmaril.X86 (State Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory)
open Silmaril.X86.Str9G (GState)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Libc.SysWrap

/-! ## Steps -/

/-- **A listed instruction that executes is one step.** -/
theorem step_of {g : GState} {A : Word} {code : List Byte} {o l : Nat}
    {i : Silmaril.X86.Str9FsX.Instr} {c : State} {m : Memory}
    (hl : Loaded g.x.m.memory A code) (hrip : g.x.m.core.rip = A + BitVec.ofNat 64 o)
    (hok : listed code o i l = true)
    (hx : Silmaril.X86.Str9FsX.exec i g.x.m.core g.x.m.memory l = .ok c m) :
    Silmaril.X86.Str9G.step g = some { g with x := ⟨⟨c, m⟩, g.x.xmm⟩ } := by
  simp only [listed, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact Silmaril.X86.Str9G.isa.step_of (s := g) trivial hl hrip hok.2 hok.1 hx trivial

theorem exec_ext (i : Silmaril.X86.Ext.Instr) (c : State) (m : Memory) (l : Nat) :
    Silmaril.X86.Str9FsX.exec (ext i) c m l = Silmaril.X86.Ext.exec i c m l := rfl

theorem add_ofNat (A : Word) (a b : Nat) :
    A + BitVec.ofNat 64 a + BitVec.ofNat 64 b = A + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem reaches_step {s t : GState} (h : Silmaril.X86.Str9G.step s = some t) :
    Reaches Silmaril.X86.Str9G.step s t :=
  ⟨1, by simp [Silmaril.Machine.Execution.run, h]⟩

theorem reaches_cons {s t u : GState} (h : Silmaril.X86.Str9G.step s = some t)
    (r : Reaches Silmaril.X86.Str9G.step t u) : Reaches Silmaril.X86.Str9G.step s u :=
  (reaches_step h).trans r

/-! ## Values -/

@[simp] theorem eval_low32 (c : State) (v : Val) :
    v.low32.eval c = ((v.eval c).setWidth 32).setWidth 64 := by
  cases v <;> simp [Val.low32, Val.eval, BitVec.setWidth_setWidth_of_le]

theorem upd_apply (σ : Reg → Val) (r q : Reg) (v : Val) :
    upd σ r v q = if q = r then v else σ q := rfl

theorem scratch_not_kept {r : Reg} (h : scratch r = true) : ∀ q ∈ kept, q ≠ r := by
  intro q hq hqr; subst hqr
  simp only [scratch, Bool.not_eq_true'] at h
  have := List.contains_iff_mem.mpr hq
  rw [h] at this; cases this

/-! ## The invariant before the call -/

/-- The machine state `h` agrees with the symbolic state `p` of the run from the entry `g`. -/
structure PInv (A : Word) (single : Option Word) (g h : GState) (p : PSt) : Prop where
  rip : h.x.m.core.rip = A + BitVec.ofNat 64 p.off
  regs : ∀ r, h.x.m.core.read r = (p.σ r).eval g.x.m.core
  mem : h.x.m.memory = g.x.m.memory
  fs : h.x.m.core.fsBase = g.x.m.core.fsBase
  xmm : h.x.xmm = g.x.xmm
  tsc : h.tsc = g.tsc
  cet : h.cetOff = g.cetOff
  keep : ∀ r ∈ Silmaril.Libc.SysWrap.kept, p.σ r = .reg r
  flag : p.fl = true → ∃ f v, single = some f ∧ loadN g.x.m.memory (A + f) 1 = some v ∧
    v.setWidth 8 ≠ 0 ∧ h.x.m.core.flags = Silmaril.X86.Ext.subFlagsN (v.setWidth 8) 0#8

theorem PInv.entry {A : Word} {single : Option Word} {g : GState}
    (hrip : g.x.m.core.rip = A) : PInv A single g g PSt.entry where
  rip := by simp [PSt.entry, hrip]
  regs _ := rfl
  mem := rfl
  fs := rfl
  xmm := rfl
  tsc := rfl
  cet := rfl
  keep _ _ := rfl
  flag h := by simp [PSt.entry] at h

/-- A step that changes only the core keeps the invariant at the next symbolic state. -/
theorem PInv.next {A : Word} {single : Option Word} {g h : GState} {p : PSt} {l : Nat}
    (inv : PInv A single g h p) {c : State} {σ' : Reg → Val} {fl' : Bool}
    (hrip : c.rip = h.x.m.core.rip + BitVec.ofNat 64 l)
    (hregs : ∀ r, c.read r = (σ' r).eval g.x.m.core) (hfs : c.fsBase = h.x.m.core.fsBase)
    (hkept : ∀ r ∈ kept, σ' r = .reg r)
    (hfl : fl' = true → ∃ f v, single = some f ∧ loadN g.x.m.memory (A + f) 1 = some v ∧
      v.setWidth 8 ≠ 0 ∧ c.flags = Silmaril.X86.Ext.subFlagsN (v.setWidth 8) 0#8) :
    PInv A single g { h with x := ⟨⟨c, h.x.m.memory⟩, h.x.xmm⟩ } ⟨p.off + l, σ', fl'⟩ where
  rip := by simp only; rw [hrip, inv.rip, add_ofNat]
  regs := hregs
  mem := inv.mem
  fs := by simp only; rw [hfs, inv.fs]
  xmm := inv.xmm
  tsc := inv.tsc
  cet := inv.cet
  keep := hkept
  flag := hfl

theorem kept_upd {σ : Reg → Val} {r : Reg} {v : Val} (hk : ∀ q ∈ kept, σ q = .reg q)
    (hs : scratch r = true) : ∀ q ∈ kept, upd σ r v q = .reg q := by
  intro q hq
  simp [upd_apply, scratch_not_kept hs q hq, hk q hq]

theorem regs_upd {g : GState} {c : State} {σ : Reg → Val} {r : Reg} {v : Val}
    (hregs : ∀ q, c.read q = (σ q).eval g.x.m.core) (w : Word)
    (hw : w = v.eval g.x.m.core) : ∀ q, (c.write r w).read q = (upd σ r v q).eval g.x.m.core := by
  intro q
  rw [upd_apply, State.read_write]
  split
  · exact hw
  · exact hregs q

/-- **One instruction before the call.** -/
theorem pstep_sound {code : List Byte} {single : Option Word} {A : Word} {g h : GState}
    {p q : PSt} {op : Op} {l : Nat}
    (hl : Loaded g.x.m.memory A code)
    (hs : ∀ f, single = some f → ∃ v, loadN g.x.m.memory (A + f) 1 = some v ∧ v.setWidth 8 ≠ 0)
    (inv : PInv A single g h p) (hstep : p.step code single (op, l) = some q) :
    ∃ h', Silmaril.X86.Str9G.step h = some h' ∧ PInv A single g h' q := by
  have hl' : Loaded h.x.m.memory A code := by rw [inv.mem]; exact hl
  by_cases hok : listed code p.off (ext op.instr) l = true
  swap
  · simp [PSt.step, hok] at hstep
  simp only [PSt.step, hok, ↓reduceIte] at hstep
  cases op with
  | endbr =>
    simp only [Option.some.injEq] at hstep; subst hstep
    refine ⟨_, step_of hl' inv.rip hok (by rw [exec_ext]; rfl), ?_⟩
    exact inv.next (l := l) (σ' := p.σ) (fl' := p.fl) rfl (fun r => by simpa using inv.regs r) rfl
      inv.keep (fun hf => by simpa using inv.flag hf)
  | movRR sz d s =>
    cases sz with
    | q =>
      simp only at hstep
      split at hstep
      case isFalse => cases hstep
      rename_i hsd
      simp only [Option.some.injEq] at hstep; subst hstep
      refine ⟨_, step_of hl' inv.rip hok (by rw [exec_ext]; rfl), ?_⟩
      refine inv.next (l := l) rfl ?_ rfl (kept_upd inv.keep hsd) (fun hf => by
        simpa [Silmaril.X86.Ext.Sz.write] using inv.flag hf)
      intro r
      simp only [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read, State.read_mk_regs]
      exact regs_upd inv.regs _ (by rw [BitVec.setWidth_setWidth_of_le _ (by decide)]; simpa using inv.regs s) r
    | d =>
      simp only at hstep
      split at hstep
      case isFalse => cases hstep
      rename_i hsd
      simp only [Option.some.injEq] at hstep; subst hstep
      refine ⟨_, step_of hl' inv.rip hok (by rw [exec_ext]; rfl), ?_⟩
      refine inv.next (l := l) rfl ?_ rfl (kept_upd inv.keep hsd) (fun hf => by
        simpa [Silmaril.X86.Ext.Sz.write] using inv.flag hf)
      intro r
      simp only [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read, State.read_mk_regs]
      exact regs_upd inv.regs _ (by rw [eval_low32, ← inv.regs s]; rfl) r
  | movImm d imm =>
    simp only at hstep
    split at hstep
    case isFalse => cases hstep
    rename_i hsd
    simp only [Option.some.injEq] at hstep; subst hstep
    refine ⟨_, step_of hl' inv.rip hok (by rw [exec_ext]; rfl), ?_⟩
    refine inv.next (l := l) rfl ?_ rfl (kept_upd inv.keep hsd) (fun hf => by
      simpa [Silmaril.X86.Ext.Sz.write] using inv.flag hf)
    intro r
    simp only [Silmaril.X86.Ext.Sz.write, State.read_mk_regs]
    exact regs_upd (v := .const (imm.setWidth 64)) inv.regs _ rfl r
  | xorSelf r =>
    simp only at hstep
    split at hstep
    case isFalse => cases hstep
    rename_i hsd
    simp only [Option.some.injEq] at hstep; subst hstep
    refine ⟨_, step_of hl' inv.rip hok (by rw [exec_ext]; rfl), ?_⟩
    refine inv.next (l := l) (fl' := false) rfl ?_ rfl (kept_upd inv.keep hsd) (fun hf => by cases hf)
    intro q
    simp only [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.AluOp.resultN, BitVec.xor_self,
      State.read_mk_regs]
    exact regs_upd inv.regs _ (by simp [Val.eval]) q
  | cmpFlag disp =>
    simp only at hstep
    split at hstep
    case isFalse => cases hstep
    rename_i hsd
    simp only [Option.some.injEq] at hstep; subst hstep
    obtain ⟨v, hv, hv0⟩ := hs _ hsd
    have haddr : (Silmaril.X86.Ext.Mem.ofRip disp).addr h.x.m.core
        (h.x.m.core.rip + BitVec.ofNat 64 l) = A + (BitVec.ofNat 64 (p.off + l) + disp.signExtend 64) := by
      simp only [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip, Silmaril.X86.Ext.Base.value,
        Option.map_none, Option.getD_none, BitVec.add_zero, inv.rip, BitVec.add_assoc]
      rw [← BitVec.add_assoc (BitVec.ofNat 64 p.off), ← BitVec.ofNat_add]
    have hx : Silmaril.X86.Str9FsX.exec (ext (Op.cmpFlag disp).instr) h.x.m.core h.x.m.memory l =
        .ok { h.x.m.core with flags := Silmaril.X86.Ext.subFlagsN (v.setWidth 8) (0#8)
                              rip := h.x.m.core.rip + BitVec.ofNat 64 l } h.x.m.memory := by
      rw [exec_ext]
      simp only [Op.instr, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readNarrow, haddr, inv.mem, hv,
        Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits, Option.map_some,
        Silmaril.X86.Ext.retire]
    refine ⟨_, step_of hl' inv.rip hok hx, ?_⟩
    refine inv.next (l := l) (fl' := true) rfl (fun r => by simpa using inv.regs r) rfl inv.keep ?_
    intro _
    exact ⟨_, v, hsd, hv, hv0, rfl⟩
  | jeSlow rel =>
    simp only at hstep
    split at hstep
    case isFalse => cases hstep
    rename_i hfl
    simp only [Option.some.injEq] at hstep; subst hstep
    obtain ⟨f, v, -, -, hv0, hflags⟩ := inv.flag hfl
    have hx : Silmaril.X86.Str9FsX.exec (ext (Op.jeSlow rel).instr) h.x.m.core h.x.m.memory l =
        .ok { h.x.m.core with rip := h.x.m.core.rip + BitVec.ofNat 64 l } h.x.m.memory := by
      rw [exec_ext]
      simp only [Op.instr, Silmaril.X86.Ext.exec, hflags, Silmaril.X86.Ext.eval_subFlagsN (w := 7),
        Silmaril.X86.Ext.Cond.afterCmp]
      have h0 : (v.setWidth 8 == 0#8) = false := by simpa using hv0
      rw [h0]
    refine ⟨_, step_of hl' inv.rip hok hx, ?_⟩
    exact inv.next (l := l) (σ' := p.σ) (fl' := p.fl) rfl (fun r => by simpa using inv.regs r) rfl
      inv.keep (fun hf => by simpa using inv.flag hf)

/-- **The instructions before the call.** -/
theorem runPre_sound {code : List Byte} {single : Option Word} {A : Word} {g : GState}
    (hl : Loaded g.x.m.memory A code)
    (hs : ∀ f, single = some f → ∃ v, loadN g.x.m.memory (A + f) 1 = some v ∧ v.setWidth 8 ≠ 0) :
    ∀ (ops : List (Op × Nat)) {h : GState} {p q : PSt}, PInv A single g h p →
      runPre code single ops p = some q →
      ∃ h', Reaches Silmaril.X86.Str9G.step h h' ∧ PInv A single g h' q
  | [], h, p, q, inv, hr => by
    simp only [runPre, Option.some.injEq] at hr; subst hr; exact ⟨h, .refl _ _, inv⟩
  | (op, l) :: ops, h, p, q, inv, hr => by
    simp only [runPre, Option.bind_eq_some_iff] at hr
    obtain ⟨p', h1, h2⟩ := hr
    obtain ⟨h', hst, inv'⟩ := pstep_sound hl hs inv h1
    obtain ⟨h'', hr, inv''⟩ := runPre_sound hl hs ops inv' h2
    exact ⟨h'', reaches_cons hst hr, inv''⟩

end Silmaril.Proofs.Libc.SysWrap

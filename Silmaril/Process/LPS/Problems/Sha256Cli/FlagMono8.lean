module

public import Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono
public import Silmaril.X86.Ext8.Basic

/-! # `X86.Ext8` is monotone in the definedness of the flags (VERIFIED)

`FlagMono.exec_mono` for the new 8-bit forms of the `Ext8` variant (`execNew_mono`) and for
the whole variant (`exec8_mono`): if a core with less defined flags retires, a `CoreLe`-larger
core retires to the same memory and a `CoreLe`-related core. ALU, TEST and the moves do not
read the flags (ALU and TEST overwrite them, the moves carry them); a nonzero shift by fewer
than 8 uses `ShiftOp.flags` (monotone, `ShiftOp.flags_mono`), by 8 or more overwrites them;
`setcc` reads them through `Cond.eval` (monotone).

This is what the LPS bridge needs to cover the 8-bit forms: LPS completes undefined flags at
every `syscall`, the middle model leaves them as they are.

No `sorry`, no new axiom.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

open Silmaril.X86 (Flags State Reg Word)
open Silmaril.X86.Ext (Result retire storeN loadN)
open Silmaril.X86.Ext8 (BReg RM8 New execNew alu8 shift8Flags)
open Silmaril.Process (Memory)

section Helpers

variable (s : State) (g : Flags) (memory : Memory) (next : Word)

@[simp] theorem breg_read_withFlags (b : BReg) : b.read ({ s with flags := g } : State) = b.read s := by
  cases b <;> rfl

@[simp] theorem breg_write_withFlags (b : BReg) (v : BitVec 8) :
    b.write ({ s with flags := g } : State) v = { b.write s v with flags := g } := by
  cases b <;> rfl

@[simp] theorem rm8_read_withFlags (op : RM8) :
    op.read ({ s with flags := g } : State) memory next = op.read s memory next := by
  cases op with
  | reg b => simp [RM8.read]
  | mem m => simp [RM8.read]

@[simp] theorem rm8_write_withFlags (op : RM8) (v : BitVec 8) :
    op.write v ({ s with flags := g } : State) memory next =
      (op.write v s memory next).map fun r => ({ r.1 with flags := g }, r.2) := by
  cases op with
  | reg b => simp [RM8.write]
  | mem m =>
    simp only [RM8.write, addr_withFlags, Option.map_map]
    cases storeN memory (m.addr s next) 1 (v.setWidth 64) <;> rfl

@[simp] theorem alu8_withFlags (op : Silmaril.X86.AluOp) (dst : RM8) (y : BitVec 8) :
    alu8 op dst y ({ s with flags := g } : State) memory next = alu8 op dst y s memory next := by
  unfold alu8
  rw [rm8_read_withFlags]
  cases dst.read s memory next with
  | none => rfl
  | some x =>
    simp only [rm8_write_withFlags, Option.map_map]
    split
    · rfl
    · rfl

end Helpers

/-- How a new form uses the flags. -/
theorem execNew_cases (i : New) :
    (∀ (s : State) g memory next,
      execNew i ({ s with flags := g } : State) memory next = execNew i s memory next) ∨
    (∀ (s : State) g memory next,
      execNew i ({ s with flags := g } : State) memory next = withFlagsR g (execNew i s memory next)) ∨
    (∃ op dst count, i = .shift op dst count) ∨ (∃ c dst, i = .setcc c dst) := by
  cases i with
  | alu op dst src => left; intro s g memory next; simp [execNew]
  | aluR op dst src =>
    left; intro s g memory next
    simp only [execNew, rm8_read_withFlags, alu8_withFlags]
  | aluA op imm => left; intro s g memory next; simp [execNew]
  | aluI op dst imm => left; intro s g memory next; simp [execNew]
  | test dst src =>
    left; intro s g memory next
    simp only [execNew, rm8_read_withFlags, breg_read_withFlags]
  | shift op dst count => right; right; left; exact ⟨op, dst, count, rfl⟩
  | mov dst src =>
    right; left; intro s g memory next
    simp only [execNew, breg_read_withFlags, rm8_write_withFlags, retire_map_withFlags]
  | movR dst src =>
    right; left; intro s g memory next
    simp only [execNew, rm8_read_withFlags, breg_write_withFlags]
    cases src.read s memory next <;> rfl
  | movx sx sz dst src =>
    right; left; intro s g memory next
    simp only [execNew, rm8_read_withFlags, szWrite_withFlags]
    cases src.read s memory next <;> rfl
  | setcc c dst => right; right; right; exact ⟨c, dst, rfl⟩

theorem shift8Flags_mono (op : Silmaril.X86.Ext.ShiftOp) (x : BitVec 8) (c : Nat) {f g : Flags}
    (h : FlagsLe f g) : FlagsLe (shift8Flags op x c f) (shift8Flags op x c g) := by
  unfold shift8Flags
  split
  · exact ShiftOp.flags_mono op x c h
  · exact .refl _

/-- **Flag monotonicity of the new forms.** -/
theorem execNew_mono (i : New) {s t : State} (memory : Memory) (next : Word) (h : CoreLe s t)
    {s' : State} {memory' : Memory} (e : execNew i s memory next = .ok s' memory') :
    ∃ t', execNew i t memory next = .ok t' memory' ∧ CoreLe s' t' := by
  obtain ⟨teq, hf⟩ := h
  rw [teq]
  generalize t.flags = g at hf
  rcases execNew_cases i with same | keep | ⟨op, dst, count, rfl⟩ | ⟨c, dst, rfl⟩
  · rw [same]; exact ⟨s', e, .refl _⟩
  · rw [keep, e]
    refine ⟨_, rfl, rfl, ?_⟩
    have preserved := keep s s.flags memory next
    rw [show ({ s with flags := s.flags } : State) = s from rfl, e] at preserved
    simp only [withFlagsR, Result.ok.injEq] at preserved
    have flags : s'.flags = s.flags := by rw [preserved.1]
    rw [flags]; exact hf
  · simp only [execNew, rm8_read_withFlags, countRaw_withFlags, rm8_write_withFlags,
      Option.map_map] at e ⊢
    split at e
    · cases e
    · rename_i x hx
      try rw [hx]
      split at e
      · rename_i zero
        rw [ite_eq_left zero]
        obtain ⟨rfl, rfl⟩ := retire_some_ok e
        exact ⟨_, rfl, coreLe_rip next hf⟩
      · rename_i nonzero
        rw [ite_eq_right nonzero]
        obtain ⟨⟨a, m⟩, hw, e⟩ := retire_map_ok e
        rw [hw]
        obtain ⟨rfl, rfl⟩ := retire_some_ok e
        simp only [Option.map_some, Function.comp_apply]
        exact ⟨_, rfl, rfl, shift8Flags_mono op x _ hf⟩
  · simp only [execNew, rm8_write_withFlags] at e ⊢
    split at e
    · cases e
    · rename_i v hv
      rw [Cond.eval_mono_some hf c hv]
      dsimp only
      obtain ⟨⟨a, m⟩, hw, e⟩ := retire_map_ok (o := dst.write _ s memory next) (f := id)
        (by simpa using e)
      rw [hw]
      obtain ⟨rfl, rfl⟩ := retire_some_ok e
      refine ⟨_, rfl, rfl, ?_⟩
      have := rm8_write_withFlags s s.flags memory next dst (if v then 1#8 else 0#8)
      rw [show ({ s with flags := s.flags } : State) = s from rfl, hw] at this
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      rw [this.1]; exact hf

/-- **Flag monotonicity of the whole `Ext8` variant.** -/
theorem exec8_mono (i : Silmaril.X86.Ext8.Instr) {s t : State} (memory : Memory) (length : Nat)
    (h : CoreLe s t) {s' : State} {memory' : Memory}
    (e : Silmaril.X86.Ext8.exec i s memory length = .ok s' memory') :
    ∃ t', Silmaril.X86.Ext8.exec i t memory length = .ok t' memory' ∧ CoreLe s' t' := by
  cases i with
  | base i => exact exec_mono i memory length h e
  | new i =>
    have rip : t.rip = s.rip := by rw [h.1]
    simp only [Silmaril.X86.Ext8.exec] at e ⊢
    rw [rip]
    exact execNew_mono i memory _ h e

end Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

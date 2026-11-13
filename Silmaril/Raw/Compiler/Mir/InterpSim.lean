module

public import Silmaril.Compiler.Mir.InterpMemImage.Defs
public import Silmaril.Compiler.Mir.InterpMemStore.Defs
public import Silmaril.Compiler.Mir.InterpStart.Defs
@[expose] public section

/-! # State correspondence for the Mir interpreter -/

namespace Silmaril.Compile.Mir.Interp

open Silmaril.Machine

def Activation.toLir (a : Activation) : Lir.Activation Nat := ⟨a.point.toLir, a.frame.toLir⟩

/-- The interpreter stores the most recent caller at the back of its array. -/
def Machine.toLir (m : Machine) : Lir.State Nat :=
  ⟨m.point.toLir, m.frame.toLir, m.stack.toList.reverse.map Activation.toLir, m.mem.toLir⟩

/-- Suspended result locations must be those of the call saved at that point. -/
def Activation.WellFormed (p : Lir.Prog Nat) (a : Activation) : Prop :=
  a.frame.WellFormed ∧ ∃ f args, p.fetch a.point.toLir = some (.instr (.call f args a.results))

def Machine.WellFormed (p : Lir.Prog Nat) (m : Machine) : Prop :=
  m.frame.WellFormed ∧ m.mem.WellFormed ∧
    m.mem.pages.size = (m.mem.size + pageSize - 1) / pageSize ∧
    ∀ a ∈ m.stack, a.WellFormed p

def Next.Rel (p : Lir.Prog Nat) : Next → Lir.Result Nat → Prop
  | .running m, r => r = .running m.toLir ∧ m.WellFormed p
  | .done (.returned vs mem), r => r = .returned (vs.map UInt64.toBitVec) mem.toLir
  | .done (.trapped mem), r => r = .trapped mem.toLir
  | .done (.stuck ..), r => r = .stuck
  | .done (.exhausted ..), _ => True
  | .done _, _ => False

@[simp] theorem Frame.toLir_get (fr : Frame) (r : Nat) :
    fr.toLir.get r = (fr.get r).map UInt64.toBitVec := rfl

@[simp] theorem Frame.toLir_slots (fr : Frame) (n : Nat) :
    fr.toLir.slots n = (fr.getSlot n).map UInt64.toBitVec := rfl

/-- Straight-line instructions have the same step in both representations. -/
theorem step_op_rel (p : Lir.Prog Nat) (lim : Limits) (m : Machine)
    (hm : m.WellFormed p) (hg : lim.guard = 0)
    (fn : Func) (b : Block) (o : Lir.Op Nat)
    (hf : (load p)[m.point.func]? = some fn)
    (hb : fn.blocks[m.point.label]? = some b)
    (hi : b.instrs[m.point.index]? = some (.op o)) :
    Next.Rel p (step (load p) lim m) (Lir.step p m.toLir) := by
  rcases m with ⟨pt, fr, stack, mem⟩
  obtain ⟨hfr, hmem, hp, hstack⟩ := hm
  have hfetch : p.fetch pt.toLir = some (.instr (.op o)) := by
    simpa [hi] using fetch_load p pt fn b hf hb
  dsimp only at hf hb hi hfr hmem hp hstack
  simp only [Point.toLir] at hfetch
  cases o with
  | const d v =>
    simp [step, hf, hb, hi, Lir.step, Machine.toLir, hfetch, Lir.Op.exec,
      Next.Rel, Machine.WellFormed, Point.toLir, Lir.Point.next,
      hfr, hmem, hp]
    exact hstack
  | move d s =>
    cases hs : fr.get s <;>
      simp [step, hf, hb, hi, Lir.step, Machine.toLir, hfetch, Lir.Op.exec,
        Next.Rel, Machine.WellFormed, Point.toLir, Lir.Point.next,
        hs, hfr, hmem, hp]
    exact hstack
  | unary op d s =>
    cases hs : fr.get s <;>
      simp [step, hf, hb, hi, Lir.step, Machine.toLir, hfetch, Lir.Op.exec,
        Next.Rel, Machine.WellFormed, Point.toLir, Lir.Point.next,
        hs, hfr, hmem, hp, unop_eq]
    exact hstack
  | binary op d a c =>
    cases ha : fr.get a <;> cases hc : fr.get c <;>
      simp [step, hf, hb, hi, Lir.step, Machine.toLir, hfetch, Lir.Op.exec,
        Next.Rel, Machine.WellFormed, Point.toLir, Lir.Point.next,
        ha, hc, binop_eq]
    rename_i x y
    cases he : op.eval x.toBitVec y.toBitVec <;>
      simp [hfr, hmem, hp]
    exact hstack
  | load w e d base off =>
    cases ha : fr.get base <;>
      simp [step, hf, hb, hi, Lir.step, Machine.toLir, hfetch, Lir.Op.exec,
        Next.Rel, Machine.WellFormed, Point.toLir, Lir.Point.next,
        ha, checkAccess, hg, Mem.load_toLir]
    rename_i x
    by_cases hbound : x.toNat + off + w.bytes ≤ mem.size <;>
      simp [hbound, hfr, hmem, hp]
    exact hstack
  | store w base off src =>
    cases ha : fr.get base <;> cases hx : fr.get src <;>
      simp [step, hf, hb, hi, Lir.step, Machine.toLir, hfetch, Lir.Op.exec,
        Next.Rel, Machine.WellFormed, Point.toLir, Lir.Point.next,
        ha, hx, checkAccess, hg, Mem.store_toLir mem hmem hp]
    rename_i x y
    by_cases hbound : x.toNat + off + w.bytes ≤ mem.size
    ·
      obtain ⟨hw', hs, hp', _⟩ := Mem.writeLE_spec mem hmem hp (x.toNat + off) w.bytes y
        (by cases w <;> decide) hbound
      simp [hbound, hfr, hw', hs, hp', hp]
      exact hstack
    · simp [hbound]
  | slotGet d n =>
    cases hs : fr.getSlot n <;>
      simp [step, hf, hb, hi, Lir.step, Machine.toLir, hfetch, Lir.Op.exec,
        Next.Rel, Machine.WellFormed, Point.toLir, Lir.Point.next,
        hs, hfr, hmem, hp]
    exact hstack
  | slotSet n s =>
    cases hs : fr.get s <;>
      simp [step, hf, hb, hi, Lir.step, Machine.toLir, hfetch, Lir.Op.exec,
        Next.Rel, Machine.WellFormed, Point.toLir, Lir.Point.next,
        hs, hfr, hmem, hp]
    exact hstack


end Silmaril.Compile.Mir.Interp

module

public import Silmaril.Compiler.Mir.InterpStart.Defs
@[expose] public section

/-! # Missing code and callee entry correspondences -/

namespace Silmaril.Compile.Mir.Interp

open Silmaril.Machine

theorem fetch_no_func (p : Lir.Prog Nat) (pt : Point)
    (hf : (load p)[pt.func]? = none) : p.fetch pt.toLir = none := by
  rw [load_get] at hf
  have hf' : p.func? pt.func = none := by simpa using hf
  simp [Lir.Prog.fetch, Lir.Prog.block?, Point.toLir, hf']

theorem fetch_no_block (p : Lir.Prog Nat) (pt : Point) (fn : Func)
    (hf : (load p)[pt.func]? = some fn) (hb : fn.blocks[pt.label]? = none) :
    p.fetch pt.toLir = none := by
  rw [load_get] at hf
  cases hf' : p.func? pt.func with
  | none => simp [hf'] at hf
  | some f =>
    simp only [hf', Option.map_some, Option.some.injEq] at hf
    subst fn
    have hb' : f.blocks[pt.label]? = none := by simpa [Func.ofLir] using hb
    simp [Lir.Prog.fetch, Lir.Prog.block?, Point.toLir, hf', hb']

theorem enter_loaded (p : Lir.Prog Nat) (f : Nat) (fn : Func) (vals : List UInt64)
    (hf : (load p)[f]? = some fn) :
    p.enter f (vals.map UInt64.toBitVec) =
      ((Frame.empty fn.regs).writeAll fn.params vals).map
        (fun fr => (⟨f, fn.entry, 0⟩, fr.toLir)) := by
  rw [load_get] at hf
  cases hf' : p.func? f with
  | none => simp [hf'] at hf
  | some g =>
    simp only [hf', Option.map_some, Option.some.injEq] at hf
    subst fn
    simp only [Lir.Prog.enter, hf', Option.bind_some]
    rw [← Frame.empty_toLir (Func.ofLir g).regs,
      Frame.writeAll_toLir _ (Frame.empty_wellFormed _) g.params vals]
    simp only [show (Func.ofLir g).params = g.params from rfl,
      show (Func.ofLir g).entry = g.entry from rfl]
    cases hw : (Frame.empty (Func.ofLir g).regs).writeAll g.params vals <;> rfl

end Silmaril.Compile.Mir.Interp

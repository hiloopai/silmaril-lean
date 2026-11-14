module

public import Silmaril.Compiler.Mir.InterpFrame.Defs
@[expose] public section

/-! # Code lookup and entry-state correspondence for the Mir interpreter -/

namespace Silmaril.Compile.Mir.Interp

open Silmaril.Machine

/-- The interpreter's program points use the same indices as Lir. -/
def Point.toLir (pt : Point) : Lir.Point := ⟨pt.func, pt.label, pt.index⟩

@[simp] theorem load_get (p : Lir.Prog Nat) (f : Nat) :
    (load p)[f]? = (p.func? f).map Func.ofLir := by
  simp [load, Lir.Prog.func?, List.getElem?_map]

/-- Loading code preserves block and instruction lookup. -/
theorem fetch_load (p : Lir.Prog Nat) (pt : Point) (fn : Func) (b : Block)
    (hf : (load p)[pt.func]? = some fn) (hb : fn.blocks[pt.label]? = some b) :
    p.fetch pt.toLir =
      match b.instrs[pt.index]? with
      | some i => some (.instr i)
      | none => if pt.index = b.instrs.size then some (.term b.term) else none := by
  rw [load_get] at hf
  cases hfn : p.func? pt.func with
  | none => simp [hfn] at hf
  | some f =>
    simp only [hfn, Option.map_some, Option.some.injEq] at hf
    subst fn
    simp only [Func.ofLir, List.getElem?_toArray, List.getElem?_map] at hb
    cases hbl : f.blocks[pt.label]? with
    | none => simp [hbl] at hb
    | some bl =>
      simp only [hbl, Option.map_some, Option.some.injEq] at hb
      subst b
      simp [Lir.Prog.fetch, Lir.Prog.block?, Point.toLir, hfn, hbl]
      cases hi : bl.instrs[pt.index]?
      · by_cases he : pt.index = bl.instrs.length <;> simp [he]
      · rfl

/-- A successful executable start is the semantic start over the same memory.
The returned frame also satisfies the invariant required by register-write correspondence. -/
theorem start_toLir (p : Lir.Prog Nat) (f : Nat) (args : List UInt64) (mem : Mem)
    (m : Machine) (hs : start (load p) f args mem = .ok m) :
    p.start f (args.map UInt64.toBitVec) mem.toLir =
      some ⟨m.point.toLir, m.frame.toLir, [], m.mem.toLir⟩ ∧
      m.stack = #[] ∧ m.frame.WellFormed := by
  unfold start at hs
  rw [load_get] at hs
  cases hf : p.func? f with
  | none => simp [hf] at hs
  | some fn =>
    simp only [hf, Option.map_some] at hs
    simp only [Func.ofLir] at hs
    cases hw : (Frame.empty (Func.ofLir fn).regs).writeAll fn.params args with
    | none =>
      simp only [Func.ofLir] at hw
      rw [hw] at hs
      cases hs
    | some fr =>
      have hw' := hw
      simp only [Func.ofLir] at hw'
      rw [hw'] at hs
      cases hs
      refine ⟨?_, rfl, Frame.writeAll_wellFormed _ (Frame.empty_wellFormed _) _ _ _ hw⟩
      have hwrite := Frame.writeAll_toLir (Frame.empty (Func.ofLir fn).regs)
        (Frame.empty_wellFormed _) fn.params args
      rw [Frame.empty_toLir, hw] at hwrite
      simp [Lir.Prog.start, Lir.Prog.enter, hf, hwrite, Point.toLir]

end Silmaril.Compile.Mir.Interp

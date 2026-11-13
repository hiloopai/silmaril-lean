module

public import Silmaril.Compiler.Mir.InterpSim.Defs
public import Silmaril.Compiler.Mir.InterpCode.Defs
@[expose] public section

/-! # Control-flow steps of the interpreter -/

namespace Silmaril.Compile.Mir.Interp

open Silmaril.Machine

private theorem uint64_zero (x : UInt64) : x.toBitVec = 0#64 ↔ x = 0 :=
  by
    constructor
    · intro h
      apply UInt64.toBitVec_inj.mp
      exact h.trans (by decide)
    · intro h
      subst x
      decide

theorem step_rel (p : Lir.Prog Nat) (lim : Limits) (m : Machine)
    (hm : m.WellFormed p) (hg : lim.guard = 0) :
    Next.Rel p (step (load p) lim m) (Lir.step p m.toLir) := by
  rcases m with ⟨pt, fr, stack, mem⟩
  obtain ⟨hfr, hmem, hp, hstack⟩ := hm
  dsimp only at hfr hmem hp hstack
  cases hf : (load p)[pt.func]? with
  | none =>
    have hfetch := fetch_no_func p pt hf
    simp only [Point.toLir] at hfetch
    simp [step, hf, Lir.step, Machine.toLir, Point.toLir, hfetch, Next.Rel]
  | some fn =>
    cases hb : fn.blocks[pt.label]? with
    | none =>
      have hfetch := fetch_no_block p pt fn hf hb
      simp only [Point.toLir] at hfetch
      simp [step, hf, hb, Lir.step, Machine.toLir, Point.toLir, hfetch, Next.Rel]
    | some b =>
      have hfetch := fetch_load p pt fn b hf hb
      simp only [Point.toLir] at hfetch
      cases hi : b.instrs[pt.index]? with
      | some ins =>
        cases ins with
        | op o => exact step_op_rel p lim ⟨pt,fr,stack,mem⟩ ⟨hfr,hmem,hp,hstack⟩ hg fn b o hf hb hi
        | fop op d a c =>
          simp only [hi] at hfetch
          cases ha : fr.get a <;> cases hc : fr.get c <;>
            simp [step, hf, hb, hi, Lir.step, Machine.toLir, hfetch, Lir.FOp.exec,
              Next.Rel, Machine.WellFormed, Point.toLir, Lir.Point.next, ha, hc, hfr, hmem, hp]
          exact hstack
        | call f args results =>
          simp only [hi] at hfetch
          cases hv : fr.readAll args with
          | none =>
            simp [step, hf, hb, hi, hv, Lir.step, Machine.toLir, Point.toLir, hfetch, Next.Rel]
          | some vs =>
            cases hc : (load p)[f]? with
            | none =>
              have hc' : p.func? f = none := by simpa only [load_get, Option.map_eq_none_iff] using hc
              simp [step, hf, hb, hi, hv, hc, Lir.step, Machine.toLir, Point.toLir,
                hfetch, Lir.Prog.enter, hc', Next.Rel]
            | some callee =>
              have he := enter_loaded p f callee vs hc
              cases hw : (Frame.empty callee.regs).writeAll callee.params vs with
              | none =>
                simp [step, hf, hb, hi, hv, hc, hw, Lir.step, Machine.toLir,
                  Point.toLir, hfetch, he, Next.Rel]
              | some cfr =>
                by_cases hd : stack.size < lim.maxDepth
                ·
                  have hcf := Frame.writeAll_wellFormed _ (Frame.empty_wellFormed _)
                    callee.params vs cfr hw
                  have hpush : ∀ a ∈ stack.push ⟨pt,fr,results⟩, a.WellFormed p := by
                    intro a ha
                    rcases Array.mem_push.mp ha with ha | ha
                    · exact hstack a ha
                    · subst a
                      exact ⟨hfr, f, args, hfetch⟩
                  simp [step, hf, hb, hi, hv, hc, hw, Lir.step, Machine.toLir,
                    Point.toLir, hfetch, he, Next.Rel, not_le_of_gt hd,
                    Activation.toLir, Machine.WellFormed, hcf, hmem, hp]
                  simpa only [Array.mem_push] using hpush
                · have hd' : stack.size ≥ lim.maxDepth := by omega
                  simp [step, hf, hb, hi, hv, hc, hw, hd', Next.Rel]

      | none =>
        simp only [hi] at hfetch
        by_cases hend : pt.index = b.instrs.size
        · simp only [hend, ite_true] at hfetch
          cases ht : b.term with
          | jump l =>
            simp [step, hf, hb, hend, ht, Lir.step, Machine.toLir, Point.toLir,
              hfetch, Next.Rel, Machine.WellFormed, hfr, hmem, hp]
            exact hstack
          | branch c l₁ l₂ =>
            cases hc : fr.get c <;>
              simp [step, hf, hb, hend, ht, hc, Lir.step, Machine.toLir, Point.toLir,
                hfetch, Next.Rel, Machine.WellFormed, hfr, hmem, hp]
            rename_i x
            refine ⟨?_, hstack⟩
            by_cases hz : x = 0
            · subst x; rfl
            · have hn : x.toBitVec ≠ 0#64 := fun h => hz ((uint64_zero x).mp h)
              rw [ite_eq_right hn, ite_eq_right hz]
          | trap =>
            simp [step, hf, hb, hend, ht, Lir.step, Machine.toLir, Point.toLir,
              hfetch, Next.Rel]
          | ret locs =>
            cases hv : fr.readAll locs with
            | none =>
              simp [step, hf, hb, hend, ht, hv, Lir.step, Machine.toLir, Point.toLir,
                hfetch, Next.Rel]
            | some vs =>
              cases hs : stack.back? with
              | none =>
                have hz : stack = #[] := Array.back?_eq_none_iff.mp hs
                subst stack
                simp [step, hf, hb, hend, ht, hv, Lir.step, Machine.toLir, Point.toLir,
                  hfetch, Next.Rel]
              | some a =>
                obtain ⟨rest, hrest⟩ := Array.back?_eq_some_iff.mp hs
                subst stack
                obtain ⟨hfa, f, args, hcall⟩ := hstack a (by simp)
                simp only [Point.toLir] at hcall
                have he := Frame.writeAll_toLir a.frame hfa a.results vs
                cases hw : a.frame.writeAll a.results vs with
                | none =>
                  simp [step, hf, hb, hend, ht, hv, hw, Lir.step, Machine.toLir,
                    Point.toLir, hfetch, Next.Rel, Activation.toLir, hcall, he]
                | some rfr =>
                  have hr := Frame.writeAll_wellFormed a.frame hfa a.results vs rfr hw
                  have hrest : ∀ a ∈ rest, a.WellFormed p := fun a ha =>
                    hstack a (by simp only [Array.mem_push]; exact Or.inl ha)
                  simp [step, hf, hb, hend, ht, hv, hw, Lir.step, Machine.toLir,
                    Point.toLir, hfetch, Next.Rel, Activation.toLir, hcall, he,
                    Machine.WellFormed, hr, hmem, hp, Lir.Point.next]
                  exact hrest
        · simp only [hend, ite_false] at hfetch
          simp [step, hf, hb, hi, hend, Lir.step, Machine.toLir, Point.toLir, hfetch, Next.Rel]

end Silmaril.Compile.Mir.Interp

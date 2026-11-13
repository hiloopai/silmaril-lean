module

public import Silmaril.Compiler.Mir.InterpControl.Defs
public import Silmaril.Compiler.Mir.InterpEntryMem.Defs
@[expose] public section

/-! # Fuel induction for the Mir interpreter -/

namespace Silmaril.Compile.Mir.Interp

open Silmaril.Machine

/-- Terminal interpreter outcomes agree with the fuel-bounded semantic runner. -/
def RunRel : Outcome → Lir.Result Nat → Prop
  | .returned vs mem, r => r = .returned (vs.map UInt64.toBitVec) mem.toLir
  | .trapped mem, r => r = .trapped mem.toLir
  | .stuck .., r => r = .stuck
  | .outOfFuel .., _ => True
  | .exhausted .., _ => True
  | _, _ => False

theorem run_rel (p : Lir.Prog Nat) (lim : Limits) (hg : lim.guard = 0) (n : Nat) :
    ∀ m : Machine, m.WellFormed p →
      RunRel (run (load p) lim n m) (Lir.run p n m.toLir) := by
  induction n with
  | zero => intro m _; trivial
  | succ n ih =>
    intro m hm
    have hstep := step_rel p lim m hm hg
    cases hs : step (load p) lim m with
    | running m' =>
      rw [hs] at hstep
      obtain ⟨he, hm'⟩ := hstep
      have hi := ih m' hm'
      simpa only [run, hs, Lir.run, he] using hi
    | done o =>
      rw [hs] at hstep
      cases o <;> simp_all only [Next.Rel, run, Lir.run, RunRel]

end Silmaril.Compile.Mir.Interp

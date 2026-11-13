module

public import Silmaril.Machine.CBackend.Lir.Examples.Defs

/-!
# Recursive factorial for every input

The existing `recFactorial` program performs a real recursive Lir call. The
proof works with any suspended caller stack and any memory, then closes the
outer return. Results are factorial modulo 2^64. No execution fuel or finite
input enumeration is used.
-/

@[expose] public section

namespace Silmaril.Machine.Lir.Examples

open Relation

/-- A recursive invocation reaches its own RET with the expected value. Its
caller stack and memory are unchanged, so another invocation can compose it. -/
theorem recFactorial_before_ret : ∀ (n : Nat), n < 2 ^ 64 →
    ∀ (fr : Frame Nat) (stack : List (Activation Nat)) (mem : Memory),
    fr.get 0 = some (BitVec.ofNat 64 n) →
    ∃ (last : State Nat) (results : List (Loc Nat)),
      ReflTransGen (Step recFactorial) ⟨⟨0, 0, 0⟩, fr, stack, mem⟩ last ∧
      last.stack = stack ∧ last.mem = mem ∧
      recFactorial.fetch last.point = some (.term (.ret results)) ∧
      last.frame.readAll results = some [wordFact n]
  | 0, _, fr, stack, mem, input => by
    let fr₁ := fr.set 5 1
    have branch : Step recFactorial ⟨⟨0, 0, 0⟩, fr, stack, mem⟩
        ⟨⟨0, 2, 0⟩, fr, stack, mem⟩ := by
      simpa [Step] using
        (Transition.branch (p := recFactorial) (s := ⟨⟨0, 0, 0⟩, fr, stack, mem⟩)
          rfl input).step_eq
    have value : Step recFactorial ⟨⟨0, 2, 0⟩, fr, stack, mem⟩
        ⟨⟨0, 2, 1⟩, fr₁, stack, mem⟩ :=
      (Transition.op (p := recFactorial) (s := ⟨⟨0, 2, 0⟩, fr, stack, mem⟩)
        rfl rfl).step_eq
    exact ⟨⟨⟨0, 2, 1⟩, fr₁, stack, mem⟩, [.reg 5],
      (ReflTransGen.single branch).trans (ReflTransGen.single value), rfl, rfl, rfl,
      by simp [Frame.readAll, Frame.read, fr₁, wordFact]⟩
  | n + 1, bound, fr, stack, mem, input => by
    have nonzero : BitVec.ofNat 64 (n + 1) ≠ 0#64 := by
      intro eq
      have := congrArg BitVec.toNat eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at this
      simp at this
    let fr₁ := fr.set 1 1
    let fr₂ := fr₁.set 2 (BitVec.ofNat 64 n)
    let suspended : Activation Nat := ⟨⟨0, 1, 2⟩, fr₂⟩
    let child := Frame.empty.set 0 (BitVec.ofNat 64 n)
    have branch : Step recFactorial ⟨⟨0, 0, 0⟩, fr, stack, mem⟩
        ⟨⟨0, 1, 0⟩, fr, stack, mem⟩ := by
      simpa [Step, nonzero] using
        (Transition.branch (p := recFactorial) (s := ⟨⟨0, 0, 0⟩, fr, stack, mem⟩)
          rfl input).step_eq
    have one : Step recFactorial ⟨⟨0, 1, 0⟩, fr, stack, mem⟩
        ⟨⟨0, 1, 1⟩, fr₁, stack, mem⟩ :=
      (Transition.op (p := recFactorial) (s := ⟨⟨0, 1, 0⟩, fr, stack, mem⟩)
        rfl rfl).step_eq
    have subtract : BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
      rw [BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ _
    have decrement : Step recFactorial ⟨⟨0, 1, 1⟩, fr₁, stack, mem⟩
        ⟨⟨0, 1, 2⟩, fr₂, stack, mem⟩ :=
      (Transition.op (p := recFactorial) (s := ⟨⟨0, 1, 1⟩, fr₁, stack, mem⟩)
        rfl (by simp [Op.exec, Binop.eval, fr₁, fr₂, input, subtract])).step_eq
    have call : Step recFactorial ⟨⟨0, 1, 2⟩, fr₂, stack, mem⟩
        ⟨⟨0, 0, 0⟩, child, suspended :: stack, mem⟩ :=
      (Transition.call (p := recFactorial) (s := ⟨⟨0, 1, 2⟩, fr₂, stack, mem⟩)
        (vals := [BitVec.ofNat 64 n]) (pt := ⟨0, 0, 0⟩) (fr := child) rfl (by simp [Frame.readAll, Frame.read, fr₂]) rfl).step_eq
    obtain ⟨last, results, childRuns, childStack, childMem, childRet, childValues⟩ :=
      recFactorial_before_ret n (by omega) child (suspended :: stack) mem (by simp [child])
    let fr₃ := fr₂.set 3 (wordFact n)
    have resume : Step recFactorial last ⟨⟨0, 1, 3⟩, fr₃, stack, mem⟩ := by
      have := (Transition.ret (p := recFactorial) (s := last)
        childRet childValues childStack (by rfl : recFactorial.fetch suspended.point =
          some (.instr (.call 0 [.reg 2] [.reg 3]))) rfl).step_eq
      simpa [Step, childMem, suspended, fr₃, Point.next, Frame.write] using this
    let fr₄ := fr₃.set 4 (wordFact (n + 1))
    have multiply : Step recFactorial ⟨⟨0, 1, 3⟩, fr₃, stack, mem⟩
        ⟨⟨0, 1, 4⟩, fr₄, stack, mem⟩ :=
      (Transition.op (p := recFactorial) (s := ⟨⟨0, 1, 3⟩, fr₃, stack, mem⟩)
        rfl (by simp [Op.exec, Binop.eval, fr₄, fr₃, fr₂, fr₁, input, wordFact])).step_eq
    have enterCall := (ReflTransGen.single branch).trans ((ReflTransGen.single one).trans
      ((ReflTransGen.single decrement).trans (ReflTransGen.single call)))
    have resumeCall := (ReflTransGen.single resume).trans (ReflTransGen.single multiply)
    exact ⟨⟨⟨0, 1, 4⟩, fr₄, stack, mem⟩, [.reg 4],
      enterCall.trans (childRuns.trans resumeCall), rfl, rfl, rfl,
      by simp [Frame.readAll, Frame.read, fr₄]⟩

/-- Every word input and every memory has a finite recursive return. -/
theorem recFactorial_returns (n : Word) (mem : Memory) :
    ∃ s, recFactorial.start 0 [n] mem = some s ∧
      Behaves recFactorial s (.returned [BitVec.ofNat 64 n.toNat.factorial] mem) := by
  let fr := Frame.empty.set 0 n
  obtain ⟨last, results, runs, stack, memory, ret, values⟩ :=
    recFactorial_before_ret n.toNat n.isLt fr [] mem (by simp [fr])
  refine ⟨⟨⟨0, 0, 0⟩, fr, [], mem⟩, rfl, last, runs, ?_⟩
  have := (Transition.halt (p := recFactorial) (s := last) ret values stack).step_eq
  simpa [memory, wordFact_eq] using this

/-- Spilling preserves the recursive result for every allocation size. -/
theorem recFactorial_spilled_returns (k : Nat) (n : Word) (mem : Memory) :
    ∃ s, (Alloc.spill (Alloc.firstK k) recFactorial).start 0 [n] mem = some s ∧
      Behaves (Alloc.spill (Alloc.firstK k) recFactorial) s
        (.returned [BitVec.ofNat 64 n.toNat.factorial] mem) := by
  obtain ⟨s, start, returns⟩ := recFactorial_returns n mem
  exact Alloc.spill_firstK_behaves k start returns (by intro h; cases h)

end Silmaril.Machine.Lir.Examples

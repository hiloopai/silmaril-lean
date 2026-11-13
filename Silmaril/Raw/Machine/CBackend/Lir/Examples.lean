module

public import Silmaril.Machine.CBackend.Lir.Alloc.Defs
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Lir examples

* `factorial`: a loop. Executable checks, and `factorial_returns`: for every
  64-bit input `n` and every memory, the program returns `n! mod 2^64`. The
  same holds for the program spilled with `firstK k`, for every `k`
  (`factorial_spilled_returns`).
* `memSum`: sums `count` little-endian 64-bit words starting at `base`.
* `recFactorial`: factorial by recursive calls.
* `guardedDiv`: a division with an explicit zero guard that traps.

The executable checks use `decide` on the fuel-bounded runner and the
spilled programs with few physical registers, so spill code is exercised.
-/

@[expose] public section

namespace Silmaril.Machine.Lir.Examples

open Alloc

def emptyMem : Memory := Memory.ofList 0 []

/-! ## Factorial loop -/

/-- `r0 = n`; `r1` accumulates the product; `r2 = 1`. -/
def factorial : Prog Nat := ⟨[{
  params := [.reg 0], entry := 0,
  blocks := [
    ⟨[.op (.const 1 1), .op (.const 2 1)], .jump 1⟩,
    ⟨[], .branch 0 2 3⟩,
    ⟨[.op (.binary .mul 1 1 0), .op (.binary .sub 0 0 2)], .jump 1⟩,
    ⟨[], .ret [.reg 1]⟩] }]⟩

example : (factorial.runMain 100 0 [5] emptyMem).returnedValues? = some [120] := by decide
example : (factorial.runMain 100 0 [0] emptyMem).returnedValues? = some [1] := by decide
example : ((spill (firstK 1) factorial).runMain 200 0 [6] emptyMem).returnedValues? =
    some [720] := by decide
example : ((spill (firstK 0) factorial).runMain 300 0 [6] emptyMem).returnedValues? =
    some [720] := by decide

/-- Factorial in 64-bit arithmetic. -/
def wordFact : Nat → Word
  | 0 => 1
  | k + 1 => BitVec.ofNat 64 (k + 1) * wordFact k

theorem wordFact_eq (k : Nat) : wordFact k = BitVec.ofNat 64 k.factorial := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wordFact, ih, Nat.factorial_succ, BitVec.ofNat_mul]

theorem Behaves.head {R : Type} [DecidableEq R] {p : Prog R} {s s' : State R} {b : Behavior}
    (h : Step p s s') (hb : Behaves p s' b) : Behaves p s b := by
  cases b with
  | returned vs m => obtain ⟨t, ht, hf⟩ := hb; exact ⟨t, .head h ht, hf⟩
  | trapped m => obtain ⟨t, ht, hf⟩ := hb; exact ⟨t, .head h ht, hf⟩
  | stuck => obtain ⟨t, ht, hf⟩ := hb; exact ⟨t, .head h ht, hf⟩
  | diverges => exact InfiniteTrace.fold h hb

theorem factorial_loop : ∀ (k : Nat), k < 2 ^ 64 → ∀ (fr : Frame Nat) (acc : Word) (mem : Memory),
    fr.get 0 = some (BitVec.ofNat 64 k) → fr.get 1 = some acc → fr.get 2 = some 1 →
    Behaves factorial ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (.returned [acc * wordFact k] mem)
  | 0, _, fr, acc, mem, h0, h1, _ => by
    have s₁ : Step factorial ⟨⟨0, 1, 0⟩, fr, [], mem⟩ ⟨⟨0, 3, 0⟩, fr, [], mem⟩ := by
      have := (Transition.branch (p := factorial) (s := ⟨⟨0, 1, 0⟩, fr, [], mem⟩) rfl h0).step_eq
      unfold Step; simpa using this
    have h1' : fr.regs 1 = some acc := h1
    have s₂ : step factorial ⟨⟨0, 3, 0⟩, fr, [], mem⟩ = .returned [acc] mem :=
      (Transition.halt (p := factorial) (s := ⟨⟨0, 3, 0⟩, fr, [], mem⟩) rfl
        (by simp [Frame.readAll, Frame.read, h1']) rfl).step_eq
    have hb : Behaves factorial ⟨⟨0, 3, 0⟩, fr, [], mem⟩ (.returned [acc] mem) := ⟨_, .refl, s₂⟩
    simpa [wordFact] using Behaves.head s₁ hb
  | k + 1, hk, fr, acc, mem, h0, h1, h2 => by
    have hne : BitVec.ofNat 64 (k + 1) ≠ 0 := by
      intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
      simp at this
    have s₁ : Step factorial ⟨⟨0, 1, 0⟩, fr, [], mem⟩ ⟨⟨0, 2, 0⟩, fr, [], mem⟩ := by
      have := (Transition.branch (p := factorial) (s := ⟨⟨0, 1, 0⟩, fr, [], mem⟩) rfl h0).step_eq
      have hne' : ¬ (BitVec.ofNat 64 (k + 1) = 0#64) := hne
      unfold Step; simpa [hne'] using this
    let fr₁ := fr.set 1 (acc * BitVec.ofNat 64 (k + 1))
    have s₂ : Step factorial ⟨⟨0, 2, 0⟩, fr, [], mem⟩ ⟨⟨0, 2, 1⟩, fr₁, [], mem⟩ :=
      (Transition.op (p := factorial) (s := ⟨⟨0, 2, 0⟩, fr, [], mem⟩) rfl
        (by simp [Op.exec, h0, h1, Binop.eval, fr₁])).step_eq
    let fr₂ := fr₁.set 0 (BitVec.ofNat 64 (k + 1) - 1)
    have s₃ : Step factorial ⟨⟨0, 2, 1⟩, fr₁, [], mem⟩ ⟨⟨0, 2, 2⟩, fr₂, [], mem⟩ :=
      (Transition.op (p := factorial) (s := ⟨⟨0, 2, 1⟩, fr₁, [], mem⟩) rfl
        (by simp [Op.exec, h0, h2, Binop.eval, fr₁, fr₂])).step_eq
    have s₄ : Step factorial ⟨⟨0, 2, 2⟩, fr₂, [], mem⟩ ⟨⟨0, 1, 0⟩, fr₂, [], mem⟩ :=
      (Transition.jump (p := factorial) (s := ⟨⟨0, 2, 2⟩, fr₂, [], mem⟩) (l := 1) rfl).step_eq
    have hk' : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by
      rw [BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ _
    have ih := factorial_loop k (by omega) fr₂ (acc * BitVec.ofNat 64 (k + 1)) mem
      (by rw [show fr₂.get 0 = some (BitVec.ofNat 64 (k + 1) - 1) from rfl, hk']) (by simp [fr₂, fr₁]) (by simp [fr₂, fr₁, h2])
    have e : acc * BitVec.ofNat 64 (k + 1) * wordFact k = acc * wordFact (k + 1) := by
      rw [wordFact, BitVec.mul_assoc]
    rw [e] at ih
    exact Behaves.head s₁ (Behaves.head s₂ (Behaves.head s₃ (Behaves.head s₄ ih)))

/-- The factorial loop returns `n! mod 2^64` for every 64-bit input and memory. -/
theorem factorial_returns (n : Word) (mem : Memory) :
    ∃ s, factorial.start 0 [n] mem = some s ∧
      Behaves factorial s (.returned [BitVec.ofNat 64 n.toNat.factorial] mem) := by
  let fr₀ : Frame Nat := Frame.empty.set 0 n
  refine ⟨⟨⟨0, 0, 0⟩, fr₀, [], mem⟩, rfl, ?_⟩
  let fr₁ := fr₀.set 1 1
  let fr₂ := fr₁.set 2 1
  have s₁ : Step factorial ⟨⟨0, 0, 0⟩, fr₀, [], mem⟩ ⟨⟨0, 0, 1⟩, fr₁, [], mem⟩ :=
    (Transition.op (p := factorial) (s := ⟨⟨0, 0, 0⟩, fr₀, [], mem⟩) rfl rfl).step_eq
  have s₂ : Step factorial ⟨⟨0, 0, 1⟩, fr₁, [], mem⟩ ⟨⟨0, 0, 2⟩, fr₂, [], mem⟩ :=
    (Transition.op (p := factorial) (s := ⟨⟨0, 0, 1⟩, fr₁, [], mem⟩) rfl rfl).step_eq
  have s₃ : Step factorial ⟨⟨0, 0, 2⟩, fr₂, [], mem⟩ ⟨⟨0, 1, 0⟩, fr₂, [], mem⟩ :=
    (Transition.jump (p := factorial) (s := ⟨⟨0, 0, 2⟩, fr₂, [], mem⟩) (l := 1) rfl).step_eq
  have loop := factorial_loop n.toNat n.isLt fr₂ 1 mem (by simp [fr₂, fr₁, fr₀])
    (by simp [fr₂, fr₁]) (by simp [fr₂])
  rw [one_mul, wordFact_eq] at loop
  exact Behaves.head s₁ (Behaves.head s₂ (Behaves.head s₃ loop))

/-- The same result after spilling with `firstK k`, for every `k`. -/
theorem factorial_spilled_returns (k : Nat) (n : Word) (mem : Memory) :
    ∃ t, (spill (firstK k) factorial).start 0 [n] mem = some t ∧
      Behaves (spill (firstK k) factorial) t (.returned [BitVec.ofNat 64 n.toNat.factorial] mem) := by
  obtain ⟨s, hs, hb⟩ := factorial_returns n mem
  exact spill_firstK_behaves k hs hb (by intro h; cases h)

/-! ## Memory sum -/

/-- `r0 = base`, `r1 = count`; returns the sum of `count` 64-bit words. -/
def memSum : Prog Nat := ⟨[{
  params := [.reg 0, .reg 1], entry := 0,
  blocks := [
    ⟨[.op (.const 2 0), .op (.const 3 1), .op (.const 4 8)], .jump 1⟩,
    ⟨[], .branch 1 2 3⟩,
    ⟨[.op (.load .b8 .zero 5 0 0), .op (.binary .add 2 2 5), .op (.binary .add 0 0 4),
      .op (.binary .sub 1 1 3)], .jump 1⟩,
    ⟨[], .ret [.reg 2]⟩] }]⟩

def words : List Word := [3, 5, 7, 11, 13]

def wordsMem : Memory := Memory.ofList 40 (LittleEndian.encodeWords words)

example : (memSum.runMain 200 0 [0, 5] wordsMem).returnedValues? = some [39] := by decide
example : (memSum.runMain 200 0 [8, 3] wordsMem).returnedValues? = some [23] := by decide
/-- Reading past the end of memory is stuck, not a trap. -/
example : (memSum.runMain 200 0 [8, 5] wordsMem).returnedValues? = none := by decide
example : ((spill (firstK 2) memSum).runMain 400 0 [0, 5] wordsMem).returnedValues? =
    some [39] := by decide

/-- Byte loads with sign and zero extension. -/
def loadByte (ext : Ext) : Prog Nat := ⟨[{
  params := [.reg 0], entry := 0,
  blocks := [⟨[.op (.load .b1 ext 1 0 0)], .ret [.reg 1]⟩] }]⟩

example : ((loadByte .sign).runMain 10 0 [0] (Memory.ofList 1 [0xff])).returnedValues? =
    some [-1] := by decide
example : ((loadByte .zero).runMain 10 0 [0] (Memory.ofList 1 [0xff])).returnedValues? =
    some [255] := by decide

/-! ## Recursive calls -/

/-- `f(n) = if n = 0 then 1 else n * f(n - 1)`, with a call in the middle of a
block. -/
def recFactorial : Prog Nat := ⟨[{
  params := [.reg 0], entry := 0,
  blocks := [
    ⟨[], .branch 0 1 2⟩,
    ⟨[.op (.const 1 1), .op (.binary .sub 2 0 1), .call 0 [.reg 2] [.reg 3],
      .op (.binary .mul 4 0 3)], .ret [.reg 4]⟩,
    ⟨[.op (.const 5 1)], .ret [.reg 5]⟩] }]⟩

example : (recFactorial.runMain 200 0 [5] emptyMem).returnedValues? = some [120] := by decide
example : ((spill (firstK 1) recFactorial).runMain 400 0 [5] emptyMem).returnedValues? =
    some [120] := by decide

/-- Arguments and results passed through stack slots. -/
def slotCall : Prog Nat := ⟨[
  { params := [], entry := 0,
    blocks := [⟨[.op (.const 0 20), .op (.slotSet 3 0), .op (.const 1 22),
      .call 1 [.slot 3, .reg 1] [.slot 0], .op (.slotGet 2 0)], .ret [.reg 2]⟩] },
  { params := [.slot 0, .reg 7], entry := 0,
    blocks := [⟨[.op (.slotGet 1 0), .op (.binary .add 2 1 7)], .ret [.reg 2]⟩] }]⟩

example : (slotCall.runMain 50 0 [] emptyMem).returnedValues? = some [42] := by decide
example : ((spill (firstK 0) slotCall).runMain 100 0 [] emptyMem).returnedValues? =
    some [42] := by decide

/-! ## Guarded division and traps -/

/-- Divides `r0` by `r1`, trapping on a zero divisor. -/
def guardedDiv : Prog Nat := ⟨[{
  params := [.reg 0, .reg 1], entry := 0,
  blocks := [
    ⟨[], .branch 1 1 2⟩,
    ⟨[.op (.binary .divu 2 0 1)], .ret [.reg 2]⟩,
    ⟨[], .trap⟩] }]⟩

example : (guardedDiv.runMain 10 0 [42, 5] emptyMem).returnedValues? = some [8] := by decide
example : (guardedDiv.runMain 10 0 [42, 0] emptyMem).isTrapped = true := by decide

/-- Without the guard, division by zero is stuck (undefined), not a trap. -/
def unguardedDiv : Prog Nat := ⟨[{
  params := [.reg 0, .reg 1], entry := 0,
  blocks := [⟨[.op (.binary .divu 2 0 1)], .ret [.reg 2]⟩] }]⟩

example : (unguardedDiv.runMain 10 0 [42, 0] emptyMem).isTrapped = false := by decide
example : (unguardedDiv.runMain 10 0 [42, 0] emptyMem).returnedValues? = none := by decide

/-! ## Operator spot checks -/

example : Unop.eval .clz32 1 = 31 := by decide
example : Unop.eval .popcnt32 0xff00000fff = 12 := by decide
example : Unop.eval .sext32 0x80000000 = 0xffffffff80000000 := by decide
example : Unop.eval .zext32 0xffffffff80000000 = 0x80000000 := by decide
example : Binop.eval .shl32 1 33 = some 2 := by decide
example : Binop.eval .rotl32 0x80000001 1 = some 3 := by decide
example : Binop.eval (.cmp32 .lts) 0xffffffff 0 = some 1 := by decide
example : Binop.eval (.cmp .lts) 0xffffffff 0 = some 0 := by decide
example : Binop.eval .mulhu (-1) (-1) = some (-2) := by decide
example : Binop.eval .mulhs (-1) (-1) = some 0 := by decide
example : Binop.eval .divs (BitVec.intMin 64) (-1) = none := by decide
example : Binop.eval .rems (BitVec.intMin 64) (-1) = none := by decide
example : Binop.eval .rems32 0x80000000 0xffffffff = none := by decide
example : Binop.eval .divu32 0x100000007 2 = some 3 := by decide
example : Binop.eval .remu 7 0 = none := by decide

end Silmaril.Machine.Lir.Examples

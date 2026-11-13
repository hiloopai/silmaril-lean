module

public import Silmaril.Machine.CBackend.RTL.SSA.Defs
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# RTL examples

The same factorial loop twice: once as an RTL control-flow graph of nodes over
pseudo-registers, once in `RTL.SSA` with block arguments. Both come with a
theorem covering every 64-bit input and every memory, in the style of
`Silmaril/Machine/Lir/Examples.lean`.

The SSA version shows what block arguments replace: the loop header block takes
the current counter and accumulator as parameters, each back edge supplies its
own pair, and no register is assigned twice. `ssaFactorial_wellFormed` checks the
whole well-formedness predicate by `decide`, which means the kernel evaluates the
dominance fixpoint of `Machine/Graph/Dominance.lean` — four rounds of successor
closure per candidate dominator — and not merely a syntactic check. The
`Decidable` instance it runs is sound only because
`Graph.Digraph.dominates_iff_not_walk` is proved; a `decide` that returned
`isTrue` through an unproved instance would prove nothing.
-/

@[expose] public section

namespace Silmaril.Machine.RTL.Examples

open Silmaril.Machine.Lir (Word Memory)

/-- The empty linear memory. -/
def emptyMem : Memory := Lir.Memory.ofList 0 []

/-- Factorial in 64-bit arithmetic. -/
def wordFact : Nat → Word
  | 0 => 1
  | k + 1 => BitVec.ofNat 64 (k + 1) * wordFact k

theorem wordFact_eq (k : Nat) : wordFact k = BitVec.ofNat 64 k.factorial := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wordFact, ih, Nat.factorial_succ, BitVec.ofNat_mul]

/-! ## The loop in RTL

`r0` is the counter, `r1` the accumulator and `r2` the constant one. Every
instruction names its successor; node 2 is the loop test. -/

/-- A factorial loop as an RTL control-flow graph. -/
def factorial : Prog Nat := ⟨[{
  sig := ⟨1, 1⟩, params := [0], entry := 0,
  code := [
    .const 1 1 1,
    .const 2 1 2,
    .cond 0 3 5,
    .binary .mul 1 1 0 4,
    .binary .sub 0 0 2 2,
    .ret [1]] }]⟩

example : factorial.WellFormedSig := by decide
example : (factorial.runMain 100 0 [5] emptyMem).returnedValues? = some [120] := by decide
example : (factorial.runMain 100 0 [0] emptyMem).returnedValues? = some [1] := by decide
example : (factorial.runMain 100 0 [10] emptyMem).returnedValues? = some [3628800] := by decide

theorem factorial_loop : ∀ (k : Nat), k < 2 ^ 64 → ∀ (fr : Frame Nat) (acc : Word) (mem : Memory),
    fr.get 0 = some (BitVec.ofNat 64 k) → fr.get 1 = some acc → fr.get 2 = some 1 →
    Behaves factorial ⟨⟨0, 2⟩, fr, [], mem⟩ (.returned [acc * wordFact k] mem)
  | 0, _, fr, acc, mem, h0, h1, _ => by
    have s₁ : Step factorial ⟨⟨0, 2⟩, fr, [], mem⟩ ⟨⟨0, 5⟩, fr, [], mem⟩ := by
      have := (Transition.cond (p := factorial) (s := ⟨⟨0, 2⟩, fr, [], mem⟩) rfl h0).step_eq
      unfold Step; simpa [Point.at] using this
    have s₂ : step factorial ⟨⟨0, 5⟩, fr, [], mem⟩ = .returned [acc] mem :=
      (Transition.halt (p := factorial) (s := ⟨⟨0, 5⟩, fr, [], mem⟩) rfl
        (by simp [Frame.readAll, h1]) rfl).step_eq
    have hb : Behaves factorial ⟨⟨0, 5⟩, fr, [], mem⟩ (.returned [acc] mem) := ⟨_, .refl, s₂⟩
    simpa [wordFact] using Behaves.head s₁ hb
  | k + 1, hk, fr, acc, mem, h0, h1, h2 => by
    have hne : BitVec.ofNat 64 (k + 1) ≠ 0 := by
      intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
      simp at this
    have s₁ : Step factorial ⟨⟨0, 2⟩, fr, [], mem⟩ ⟨⟨0, 3⟩, fr, [], mem⟩ := by
      have := (Transition.cond (p := factorial) (s := ⟨⟨0, 2⟩, fr, [], mem⟩) rfl h0).step_eq
      have hne' : ¬ (BitVec.ofNat 64 (k + 1) = 0#64) := hne
      unfold Step; simpa [hne', Point.at] using this
    let fr₁ := fr.set 1 (acc * BitVec.ofNat 64 (k + 1))
    have s₂ : Step factorial ⟨⟨0, 3⟩, fr, [], mem⟩ ⟨⟨0, 4⟩, fr₁, [], mem⟩ :=
      (Transition.binary (p := factorial) (s := ⟨⟨0, 3⟩, fr, [], mem⟩) rfl h1 h0 rfl).step_eq
    have g0 : fr₁.get 0 = some (BitVec.ofNat 64 (k + 1)) := by simp [fr₁, h0]
    have g2 : fr₁.get 2 = some (1 : Word) := by simp [fr₁, h2]
    let fr₂ := fr₁.set 0 (BitVec.ofNat 64 (k + 1) - 1)
    have s₃ : Step factorial ⟨⟨0, 4⟩, fr₁, [], mem⟩ ⟨⟨0, 2⟩, fr₂, [], mem⟩ :=
      (Transition.binary (p := factorial) (s := ⟨⟨0, 4⟩, fr₁, [], mem⟩) rfl g0 g2 rfl).step_eq
    have hk' : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by
      rw [BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ _
    have ih := factorial_loop k (by omega) fr₂ (acc * BitVec.ofNat 64 (k + 1)) mem
      (by rw [show fr₂.get 0 = some (BitVec.ofNat 64 (k + 1) - 1) from rfl, hk'])
      (by simp [fr₂, fr₁]) (by simp [fr₂, fr₁, h2])
    have e : acc * BitVec.ofNat 64 (k + 1) * wordFact k = acc * wordFact (k + 1) := by
      rw [wordFact, BitVec.mul_assoc]
    rw [e] at ih
    exact Behaves.head s₁ (Behaves.head s₂ (Behaves.head s₃ ih))

/-- **The RTL factorial loop returns `n! mod 2^64`** for every 64-bit input and
every memory. -/
theorem factorial_returns (n : Word) (mem : Memory) :
    ∃ s, factorial.start 0 [n] mem = some s ∧
      Behaves factorial s (.returned [BitVec.ofNat 64 n.toNat.factorial] mem) := by
  let fr₀ : Frame Nat := Frame.empty.set 0 n
  refine ⟨⟨⟨0, 0⟩, fr₀, [], mem⟩, rfl, ?_⟩
  let fr₁ := fr₀.set 1 1
  let fr₂ := fr₁.set 2 1
  have s₁ : Step factorial ⟨⟨0, 0⟩, fr₀, [], mem⟩ ⟨⟨0, 1⟩, fr₁, [], mem⟩ :=
    (Transition.const (p := factorial) (s := ⟨⟨0, 0⟩, fr₀, [], mem⟩) rfl).step_eq
  have s₂ : Step factorial ⟨⟨0, 1⟩, fr₁, [], mem⟩ ⟨⟨0, 2⟩, fr₂, [], mem⟩ :=
    (Transition.const (p := factorial) (s := ⟨⟨0, 1⟩, fr₁, [], mem⟩) rfl).step_eq
  have loop := factorial_loop n.toNat n.isLt fr₂ 1 mem (by simp [fr₂, fr₁, fr₀])
    (by simp [fr₂, fr₁]) (by simp [fr₂])
  rw [one_mul, wordFact_eq] at loop
  exact Behaves.head s₁ (Behaves.head s₂ loop)

/-! ## The same loop in RTL.SSA

Block `1` is the loop header; its parameters are the counter and the
accumulator. The entry block and the loop body each supply their own pair of
arguments along their edge to it, so there is no φ-node and no register is
written twice. -/

/-- The same factorial loop in SSA form with block arguments. -/
def ssaFactorial : SSA.Prog Nat := ⟨[{
  sig := ⟨1, 1⟩, entry := 0,
  blocks := [
    ⟨[0], [.const 1 1], .jump 1 [0, 1]⟩,
    ⟨[2, 3], [], .cond 2 2 [2, 3] 3 [3]⟩,
    ⟨[4, 5], [.binary .mul 6 5 4, .const 7 1, .binary .sub 8 4 7], .jump 1 [8, 6]⟩,
    ⟨[9], [], .ret [9]⟩] }]⟩

/-- **The SSA factorial loop is well-formed**: single assignment, every use
dominated by its definition, every block argument list matching its target. -/
theorem ssaFactorial_wellFormed : ssaFactorial.WellFormed := by decide

example : (ssaFactorial.runMain 100 0 [5] emptyMem).returnedValues? = some [120] := by decide
example : (ssaFactorial.runMain 100 0 [0] emptyMem).returnedValues? = some [1] := by decide
example : (ssaFactorial.runMain 200 0 [10] emptyMem).returnedValues? = some [3628800] := by decide

/-- A step through an SSA `cond`, with the branch taken already resolved: `t`,
`as` and `vals` are the target, argument list and argument values of the edge
actually followed. -/
theorem ssaCondStep {p : SSA.Prog Nat} {s : SSA.State Nat} {c : Nat} {t₁ t₂ : SSA.Label}
    {a₁ a₂ : List Nat} {x : Word} {b : SSA.Block Nat} {fr : Frame Nat}
    (t : SSA.Label) (as : List Nat) (vals : List Word)
    (hf : p.fetch s.point = some (.term (.cond c t₁ a₁ t₂ a₂)))
    (hc : s.frame.get c = some x)
    (ht : (if x = 0 then t₂ else t₁) = t) (ha : (if x = 0 then a₂ else a₁) = as)
    (hv : s.frame.readAll as = some vals) (hb : p.block? s.point.func t = some b)
    (hw : s.frame.writeAll b.params vals = some fr) :
    SSA.Step p s ⟨⟨s.point.func, t, 0⟩, fr, s.stack, s.mem⟩ := by
  subst ht
  subst ha
  exact (SSA.Transition.cond hf hc hv hb hw).step_eq

theorem ssaFactorial_loop : ∀ (k : Nat), k < 2 ^ 64 →
    ∀ (fr : Frame Nat) (acc : Word) (mem : Memory),
    fr.get 2 = some (BitVec.ofNat 64 k) → fr.get 3 = some acc →
    SSA.Behaves ssaFactorial ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (.returned [acc * wordFact k] mem)
  | 0, _, fr, acc, mem, h2, h3 => by
    have h2' : fr.get 2 = some (0 : Word) := h2
    have s₁ : SSA.Step ssaFactorial ⟨⟨0, 1, 0⟩, fr, [], mem⟩
        ⟨⟨0, 3, 0⟩, fr.set 9 acc, [], mem⟩ :=
      ssaCondStep (p := ssaFactorial) (s := ⟨⟨0, 1, 0⟩, fr, [], mem⟩) 3 [3] [acc]
        rfl h2' (by simp) (by simp) (by simp [Frame.readAll, h3]) rfl rfl
    have s₂ : SSA.step ssaFactorial ⟨⟨0, 3, 0⟩, fr.set 9 acc, [], mem⟩ = .returned [acc] mem :=
      (SSA.Transition.halt (p := ssaFactorial)
        (s := ⟨⟨0, 3, 0⟩, fr.set 9 acc, [], mem⟩) rfl (by simp [Frame.readAll]) rfl).step_eq
    have hb : SSA.Behaves ssaFactorial ⟨⟨0, 3, 0⟩, fr.set 9 acc, [], mem⟩
        (.returned [acc] mem) := ⟨_, .refl, s₂⟩
    simpa [wordFact] using SSA.Behaves.head s₁ hb
  | k + 1, hk, fr, acc, mem, h2, h3 => by
    have hne : BitVec.ofNat 64 (k + 1) ≠ 0 := by
      intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
      simp at this
    have hne' : ¬ (BitVec.ofNat 64 (k + 1) = 0#64) := hne
    let g₀ : Frame Nat := (fr.set 4 (BitVec.ofNat 64 (k + 1))).set 5 acc
    have s₁ : SSA.Step ssaFactorial ⟨⟨0, 1, 0⟩, fr, [], mem⟩ ⟨⟨0, 2, 0⟩, g₀, [], mem⟩ :=
      ssaCondStep (p := ssaFactorial) (s := ⟨⟨0, 1, 0⟩, fr, [], mem⟩) 2 [2, 3]
        [BitVec.ofNat 64 (k + 1), acc] rfl h2 (by simp [hne']) (by simp [hne'])
        (by simp [Frame.readAll, h2, h3]) rfl rfl
    let g₁ : Frame Nat := g₀.set 6 (acc * BitVec.ofNat 64 (k + 1))
    have s₂ : SSA.Step ssaFactorial ⟨⟨0, 2, 0⟩, g₀, [], mem⟩ ⟨⟨0, 2, 1⟩, g₁, [], mem⟩ :=
      (SSA.Transition.op (p := ssaFactorial) (s := ⟨⟨0, 2, 0⟩, g₀, [], mem⟩) rfl
        (by simp [SSA.Op.exec, Lir.Binop.eval, g₀, g₁])).step_eq
    let g₂ : Frame Nat := g₁.set 7 1
    have s₃ : SSA.Step ssaFactorial ⟨⟨0, 2, 1⟩, g₁, [], mem⟩ ⟨⟨0, 2, 2⟩, g₂, [], mem⟩ :=
      (SSA.Transition.op (p := ssaFactorial) (s := ⟨⟨0, 2, 1⟩, g₁, [], mem⟩) rfl rfl).step_eq
    let g₃ : Frame Nat := g₂.set 8 (BitVec.ofNat 64 (k + 1) - 1)
    have s₄ : SSA.Step ssaFactorial ⟨⟨0, 2, 2⟩, g₂, [], mem⟩ ⟨⟨0, 2, 3⟩, g₃, [], mem⟩ :=
      (SSA.Transition.op (p := ssaFactorial) (s := ⟨⟨0, 2, 2⟩, g₂, [], mem⟩) rfl
        (by simp [SSA.Op.exec, Lir.Binop.eval, g₀, g₁, g₂, g₃])).step_eq
    let g₄ : Frame Nat :=
      (g₃.set 2 (BitVec.ofNat 64 (k + 1) - 1)).set 3 (acc * BitVec.ofNat 64 (k + 1))
    have s₅ : SSA.Step ssaFactorial ⟨⟨0, 2, 3⟩, g₃, [], mem⟩ ⟨⟨0, 1, 0⟩, g₄, [], mem⟩ :=
      (SSA.Transition.jump (p := ssaFactorial) (s := ⟨⟨0, 2, 3⟩, g₃, [], mem⟩)
        (vals := [BitVec.ofNat 64 (k + 1) - 1, acc * BitVec.ofNat 64 (k + 1)])
        rfl (by simp [Frame.readAll, g₁, g₂, g₃]) rfl rfl).step_eq
    have hk' : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by
      rw [BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ _
    have ih := ssaFactorial_loop k (by omega) g₄ (acc * BitVec.ofNat 64 (k + 1)) mem
      (by rw [show g₄.get 2 = some (BitVec.ofNat 64 (k + 1) - 1) from rfl, hk'])
      (by simp [g₄])
    have e : acc * BitVec.ofNat 64 (k + 1) * wordFact k = acc * wordFact (k + 1) := by
      rw [wordFact, BitVec.mul_assoc]
    rw [e] at ih
    exact SSA.Behaves.head s₁ (SSA.Behaves.head s₂ (SSA.Behaves.head s₃
      (SSA.Behaves.head s₄ (SSA.Behaves.head s₅ ih))))

/-- **The SSA factorial loop returns `n! mod 2^64`** for every 64-bit input and
every memory. -/
theorem ssaFactorial_returns (n : Word) (mem : Memory) :
    ∃ s, ssaFactorial.start 0 [n] mem = some s ∧
      SSA.Behaves ssaFactorial s (.returned [BitVec.ofNat 64 n.toNat.factorial] mem) := by
  let fr₀ : Frame Nat := Frame.empty.set 0 n
  refine ⟨⟨⟨0, 0, 0⟩, fr₀, [], mem⟩, rfl, ?_⟩
  let fr₁ : Frame Nat := fr₀.set 1 1
  have s₁ : SSA.Step ssaFactorial ⟨⟨0, 0, 0⟩, fr₀, [], mem⟩ ⟨⟨0, 0, 1⟩, fr₁, [], mem⟩ :=
    (SSA.Transition.op (p := ssaFactorial) (s := ⟨⟨0, 0, 0⟩, fr₀, [], mem⟩) rfl rfl).step_eq
  let fr₂ : Frame Nat := (fr₁.set 2 n).set 3 1
  have s₂ : SSA.Step ssaFactorial ⟨⟨0, 0, 1⟩, fr₁, [], mem⟩ ⟨⟨0, 1, 0⟩, fr₂, [], mem⟩ :=
    (SSA.Transition.jump (p := ssaFactorial) (s := ⟨⟨0, 0, 1⟩, fr₁, [], mem⟩) (vals := [n, 1])
      rfl (by simp [Frame.readAll, fr₁, fr₀]) rfl rfl).step_eq
  have loop := ssaFactorial_loop n.toNat n.isLt fr₂ 1 mem (by simp [fr₂, fr₁]) (by simp [fr₂])
  rw [one_mul, wordFact_eq] at loop
  exact SSA.Behaves.head s₁ (SSA.Behaves.head s₂ loop)

/-! ## Traps and undefined behaviour

The conventions are `Lir`'s: a `trap` instruction traps, an unguarded division
by zero is stuck, and so is a read of a register that was never written. -/

/-- Divides `r0` by `r1`, trapping on a zero divisor. -/
def guardedDiv : Prog Nat := ⟨[{
  sig := ⟨2, 1⟩, params := [0, 1], entry := 0,
  code := [.cond 1 1 3, .binary .divu 2 0 1 2, .ret [2], .trap] }]⟩

example : guardedDiv.WellFormedSig := by decide
example : (guardedDiv.runMain 10 0 [42, 5] emptyMem).returnedValues? = some [8] := by decide
example : (guardedDiv.runMain 10 0 [42, 0] emptyMem).isTrapped = true := by decide

/-- Without the guard, division by zero is stuck, not a trap. -/
def unguardedDiv : Prog Nat := ⟨[{
  sig := ⟨2, 1⟩, params := [0, 1], entry := 0,
  code := [.binary .divu 2 0 1 1, .ret [2]] }]⟩

example : (unguardedDiv.runMain 10 0 [42, 0] emptyMem).isTrapped = false := by decide
example : (unguardedDiv.runMain 10 0 [42, 0] emptyMem).returnedValues? = none := by decide

/-- Reading a register that was never written is stuck. An SSA function in
which this happens is not well-formed. -/
def readsUnwritten : SSA.Prog Nat := ⟨[{
  sig := ⟨0, 1⟩, entry := 0, blocks := [⟨[], [], .ret [7]⟩] }]⟩

example : (readsUnwritten.runMain 10 0 [] emptyMem).returnedValues? = none := by decide
example : ¬ readsUnwritten.WellFormed := by decide

end Silmaril.Machine.RTL.Examples

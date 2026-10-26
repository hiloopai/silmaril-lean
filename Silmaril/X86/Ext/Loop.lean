module

public import Silmaril.X86.Ext.Store

/-!
# Loop rules, and the comparisons that drive them

A compiled counted loop is a cycle in the machine's transition relation, and
the step-count bookkeeping of `Runs` is the wrong currency for it: the number
of instructions a loop retires depends on the trip count. `Returns` only ever
asks for *some* finite run, so this module works with `Reaches`, which forgets
the count, and states the loop rule there.

## The rule

`reaches_loop` is the whole thing:

    body     : ∀ i < N, ∀ m, I i m → ∃ m', Reaches exit m m' ∧ I (i + 1) m'
    exitPath : ∀ m, I N m → ∃ m', Reaches exit m m' ∧ Q m'
    start    : I 0 m
    ─────────────────────────────────────────────────────────────────────
               ∃ m', Reaches exit m m' ∧ Q m'

`I i` is read as "at the loop head, having completed `i` iterations". For the
clang `-O0` shape

    head:  cmpl $N, slot(%rbp)
           jge  after
           <body>
           jmp  head

`I i` says the counter *slot* holds `i`, not a register, which is why the
invariant has to be about memory (see `Ext.HoldsLE`). `reaches_loop_of_trace`
below is the form to use in practice: it splits the body obligation into an
invariant-free trace and a preservation step, so that the same loop can be
run at two invariant strengths — weak for liveness, strong for correctness —
without executing it twice. The `cmp`/`jge` pair
itself is not part of the rule: falling through is the first thing `body`
proves and branching is the first thing `exitPath` proves, each from
`eval_ge_cmp` below. That keeps the rule independent of which condition code
the compiler chose, so `-O1`..`-O3` can reuse it unchanged.

## The comparison

`jge` after `cmp` is a *signed* test, and relating `SF = OF` to an order on
`Nat` is exactly the kind of goal one is tempted to throw at a bit-blaster.
It does not need one. Every counter in this pilot is a C `int` known to lie in
`[0, 2^31)`, and for operands in that range the overflow flag is identically
`false` (`subOverflowN_eq_false`), so `SF = OF` collapses to `¬ SF`, and `SF`
is a statement about `(x - y).toNat` that `omega` settles
(`msb_sub_of_small`). `eval_ge_cmp` is the packaged result. No `bv_decide`.

The same hypothesis — the counter is a small non-negative `int` — is what the
`movslq`/`cltq` sign-extensions of a `-O0` body need, so an invariant that
carries `i < N ≤ 2^31` pays for both.
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (State MState Word Byte AluOp)
open Silmaril.Process (Memory)

/-! ## Reaching, without counting steps -/

/-- Some finite run of retirements leads from `a` to `b`. This is `Runs` with
the step count forgotten, which is the right currency for a loop: `Returns`
only asks for *some* finite run. -/
def Reaches (exit : Word) (a b : MState) : Prop :=
  Machine.Execution.Reaches (stepOpt exit) a b

@[refl] theorem Reaches.refl {exit : Word} (m : MState) : Reaches exit m m :=
  Machine.Execution.Reaches.refl _ _

theorem Reaches.trans {exit : Word} {a b c : MState} (first : Reaches exit a b)
    (second : Reaches exit b c) : Reaches exit a c :=
  Machine.Execution.Reaches.trans first second

/-- One retirement. -/
theorem Reaches.one {exit : Word} {m next : MState} (h : stepOpt exit m = some next) :
    Reaches exit m next := ⟨1, by simp [Machine.Execution.run, h]⟩

theorem Reaches.of_runs {exit : Word} {n : Nat} {a b : MState} (h : Runs exit n a b) :
    Reaches exit a b := ⟨n, h⟩

theorem Reaches.cons {exit : Word} {a b c : MState} (head : stepOpt exit a = some b)
    (tail : Reaches exit b c) : Reaches exit a c := (Reaches.one head).trans tail

/-- A run that reaches a returning step returns. This is also the liveness
witness: the symbolic execution *is* the proof that the function terminates. -/
theorem Returns.of_reaches {exit : Word} {initial mid final : MState}
    (reached : Reaches exit initial mid) (returned : step exit mid = .returned final) :
    Returns exit initial final := by
  obtain ⟨n, run⟩ := reached
  exact ⟨n, mid, run, returned⟩

/-- Determinism, in the `Reaches` currency: see `Returns.eq_of_run`. -/
theorem Returns.eq_of_reaches {exit : Word} {initial mid final other : MState}
    (reached : Reaches exit initial mid) (returned : step exit mid = .returned final)
    (h : Returns exit initial other) : other = final := by
  obtain ⟨n, run⟩ := reached
  exact Returns.eq_of_run run returned h

/-! ## The loop rule -/

/-- **Counted loop.** `I i` is the invariant at the loop head after `i`
iterations. One instantiation per loop; see the module doc for the shape it is
meant for. -/
theorem reaches_loop {exit : Word} {I : Nat → MState → Prop} {Q : MState → Prop} {N : Nat}
    (body : ∀ i, i < N → ∀ m, I i m → ∃ m', Reaches exit m m' ∧ I (i + 1) m')
    (exitPath : ∀ m, I N m → ∃ m', Reaches exit m m' ∧ Q m')
    {m : MState} (start : I 0 m) : ∃ m', Reaches exit m m' ∧ Q m' := by
  suffices h : ∀ k, k ≤ N → ∀ s, I (N - k) s → ∃ m', Reaches exit s m' ∧ Q m' by
    simpa using h N (Nat.le_refl N) m (by simpa using start)
  intro k
  induction k with
  | zero => intro _ s hs; simpa using exitPath s (by simpa using hs)
  | succ k ih =>
    intro hk s hs
    have hlt : N - (k + 1) < N := by omega
    obtain ⟨t, reached, ht⟩ := body (N - (k + 1)) hlt s hs
    have hstep : N - (k + 1) + 1 = N - k := by omega
    rw [hstep] at ht
    obtain ⟨final, reached', hq⟩ := ih (by omega) t ht
    exact ⟨final, reached.trans reached', hq⟩

/-- **Counted loop, with the body obligation factored.** This is
`reaches_loop` with the per-iteration work split in two, which is what makes
one loop provable at two invariant strengths without reproving the execution.

* `Pre i m` is what one iteration needs in order to *execute*: the image
  loaded, the accesses permitted, the registers holding what the addressing
  modes read. It mentions no data.
* `trace` is the invariant-free statement of what one iteration *does*. It
  consumes `Pre` only, so it is shared verbatim between a weak run and a
  strong one.
* `Post i m m'` records the effect, and `preserve` is the only place the
  invariant appears.

Strengthening `I` — from "the counter is in range and nothing faults", which
is all a liveness claim needs, to "and `w[0..i)` holds the schedule", which a
correctness claim needs — then re-uses `trace` unchanged and extends
`preserve` additively. Proving a loop twice costs one `preserve`, not two
symbolic executions.

A note on the `rip` component of `I`. A top-tested loop (`cmp; jge exit` at
the head, which is what clang `-O0` emits) is at the head for every `i`,
including `i = N`; a bottom-tested loop with a `jne` backedge (`-O2`, `-O3`,
`-Os`) is at the head for `i < N` and at the *fallthrough* for `i = N`. `I` is
indexed, so both fit; but an invariant written with a constant `rip` only
looks like the general shape. Write it as a function of the index even where
it is constant, or the second track to use it rewrites the loop. -/
theorem reaches_loop_of_trace {exit : Word} {I : Nat → MState → Prop} {Q : MState → Prop}
    {Pre : Nat → MState → Prop} {Effect : Nat → MState → MState → Prop} {N : Nat}
    (entry : ∀ i, i < N → ∀ m, I i m → Pre i m)
    (trace : ∀ i, i < N → ∀ m, Pre i m → ∃ m', Reaches exit m m' ∧ Effect i m m')
    (preserve : ∀ i, i < N → ∀ m m', I i m → Effect i m m' → I (i + 1) m')
    (exitPath : ∀ m, I N m → ∃ m', Reaches exit m m' ∧ Q m')
    {m : MState} (start : I 0 m) : ∃ m', Reaches exit m m' ∧ Q m' := by
  refine reaches_loop (I := I) (fun i hi s hs => ?_) exitPath start
  obtain ⟨t, reached, effect⟩ := trace i hi s (entry i hi s hs)
  exact ⟨t, reached, preserve i hi s t hs effect⟩

/-- The loop rule run straight into a `ret`: the packaged form a whole
function proof uses. -/
theorem returns_of_loop {exit : Word} {I : Nat → MState → Prop} {N : Nat}
    {initial final : MState}
    (body : ∀ i, i < N → ∀ m, I i m → ∃ m', Reaches exit m m' ∧ I (i + 1) m')
    (exitPath : ∀ m, I N m → ∃ m', Reaches exit m m' ∧ step exit m' = .returned final)
    (start : I 0 initial) : Returns exit initial final := by
  obtain ⟨m', reached, returned⟩ := reaches_loop body exitPath start
  exact Returns.of_reaches reached returned

/-! ## Signed comparison of small non-negative operands

Every index variable of the pilot is a C `int` in `[0, 2^31)`. For operands in
that range the subtraction cannot overflow, so `OF` is `false` and the signed
conditions reduce to statements about `Nat`. -/

/-- A value below half the modulus has a clear sign bit. -/
theorem msb_eq_false_of_small {n : Nat} {x : BitVec (n + 1)} (hx : x.toNat < 2 ^ n) :
    x.msb = false := by
  rw [BitVec.msb_eq_decide, Nat.add_one_sub_one]
  simp only [decide_eq_false_iff_not]
  omega

/-- Wrapped subtraction, as a `Nat` case split. No hypothesis is needed: a
borrow adds the modulus back. -/
theorem toNat_sub_wrap {n : Nat} (x y : BitVec n) :
    (x - y).toNat =
      if x.toNat < y.toNat then 2 ^ n - y.toNat + x.toNat else x.toNat - y.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_sub]
  split
  · exact Nat.mod_eq_of_lt (by omega)
  · rename_i h
    rw [show 2 ^ n - y.toNat + x.toNat = 2 ^ n + (x.toNat - y.toNat) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- `SF` after `cmp x, y` on small non-negative operands is `x < y`. -/
theorem msb_sub_of_small {n : Nat} {x y : BitVec (n + 1)}
    (hx : x.toNat < 2 ^ n) (hy : y.toNat < 2 ^ n) :
    (x - y).msb = decide (x.toNat < y.toNat) := by
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
  rw [BitVec.msb_eq_decide, Nat.add_one_sub_one, toNat_sub_wrap]
  split <;> rename_i h
  · simp only [h, decide_true, decide_eq_true_eq]; omega
  · simp only [h, decide_false, decide_eq_false_iff_not]; omega

/-- `OF` after `cmp x, y` on small non-negative operands is `false`: the
difference of two values in `[0, 2^n)` is representable. This is what makes
the signed conditions elementary. -/
theorem subOverflowN_eq_false_of_small {n : Nat} {x y : BitVec (n + 1)}
    (hx : x.toNat < 2 ^ n) (hy : y.toNat < 2 ^ n) : subOverflowN x y = false := by
  rw [subOverflowN, BitVec.msb_and, BitVec.msb_xor, msb_eq_false_of_small hx,
    msb_eq_false_of_small hy]
  simp

/-- **`jge` after `cmp`.** On small non-negative operands the signed
greater-or-equal condition is the `Nat` order, with no case split on bits. -/
theorem eval_ge_cmp {n : Nat} {x y : BitVec (n + 1)}
    (hx : x.toNat < 2 ^ n) (hy : y.toNat < 2 ^ n) :
    Cond.ge.eval (AluOp.flagsN .cmp x y) = some (decide (y.toNat ≤ x.toNat)) := by
  simp only [AluOp.flagsN, subFlagsN, Cond.eval, kNot, kXor,
    subOverflowN_eq_false_of_small hx hy, msb_sub_of_small hx hy, Option.map_some,
    Bool.bne_false, Option.some.injEq]
  rw [show (decide (y.toNat ≤ x.toNat)) = !(decide (x.toNat < y.toNat)) by
    rw [← decide_not]; simp]

/-! ### Every condition at once

`Ext.Flags.eval_subFlagsN` gives the meaning of *every* condition after `cmp`,
as `Cond.afterCmp`. `eval_cmp` is that fact in the form the ALU step produces,
and it closes all three axes a loop can vary along — signed versus unsigned
(`l`/`ge` versus `b`/`ae`), `SF`/`OF` versus `ZF` (`jge` versus `jne`), and
which way the branch runs — in one statement. The specialisations below are
the shapes a loop proof actually wants: a `Bool` over `Nat` comparisons rather
than over `BitVec` predicates. -/

/-- Every condition after `cmp x, y`. -/
theorem eval_cmp {w : Nat} (x y : BitVec (w + 1)) (c : Cond) :
    c.eval (AluOp.flagsN .cmp x y) = some (c.afterCmp x y) := eval_subFlagsN x y c

/-- `jb` after `cmp`: the **unsigned** order, with no range hypothesis at all.
An `unsigned` C loop counter branches on this, where a signed one branches on
`jl`. -/
theorem eval_b_cmp {w : Nat} (x y : BitVec (w + 1)) :
    Cond.b.eval (AluOp.flagsN .cmp x y) = some (decide (x.toNat < y.toNat)) := by
  rw [eval_cmp]
  simp [Cond.afterCmp, BitVec.ult_eq_decide]

/-- `jae` after `cmp`: the unsigned counterpart of `eval_ge_cmp`, and the exit
test of an `unsigned`-counter loop. -/
theorem eval_ae_cmp {w : Nat} (x y : BitVec (w + 1)) :
    Cond.ae.eval (AluOp.flagsN .cmp x y) = some (decide (y.toNat ≤ x.toNat)) := by
  rw [eval_cmp]
  simp only [Cond.afterCmp, BitVec.ult_eq_decide, Option.some.injEq]
  rw [← decide_not]
  simp

/-! ### The zero flag

`jne`/`je` read `ZF` alone, which needs no range hypothesis at all: `x - y` is
zero exactly when `x = y`, at every width. The `-O0` loops branch on `jge`,
the `-O2` loops on `jne`; `reaches_loop` is indifferent, because the
comparison lives in the body and exit-path obligations rather than in the
rule. -/

/-- A wrapped difference is zero exactly on equal operands. -/
theorem sub_eq_zero_iff {n : Nat} (x y : BitVec n) : x - y = 0#n ↔ x = y := by
  have hx := x.isLt
  have hy := y.isLt
  constructor
  · intro hs
    have hz := congrArg BitVec.toNat hs
    rw [toNat_sub_wrap] at hz
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hz
    refine BitVec.eq_of_toNat_eq ?_
    split at hz <;> omega
  · rintro rfl
    refine BitVec.eq_of_toNat_eq ?_
    rw [toNat_sub_wrap]
    simp

/-- `je` after `cmp`, at any width and with no range hypothesis. -/
theorem eval_e_cmp {n : Nat} (x y : BitVec n) :
    Cond.e.eval (AluOp.flagsN .cmp x y) = some (decide (x = y)) := by
  simp only [AluOp.flagsN, subFlagsN, Cond.eval, isZeroN, Option.some.injEq]
  rw [show ((x - y) == 0#n) = decide (x - y = 0#n) from rfl]
  congr 1
  simp [sub_eq_zero_iff]

/-- `jne` after `cmp`: the loop condition of the `-O2` images. -/
theorem eval_ne_cmp {n : Nat} (x y : BitVec n) :
    Cond.ne.eval (AluOp.flagsN .cmp x y) = some (decide (x ≠ y)) := by
  simp only [Cond.eval, kNot]
  rw [show (AluOp.flagsN (n := n) .cmp x y).zero = Cond.e.eval (AluOp.flagsN .cmp x y) from rfl,
    eval_e_cmp]
  simp

/-- `jl` after `cmp`, the complementary branch. -/
theorem eval_l_cmp {n : Nat} {x y : BitVec (n + 1)}
    (hx : x.toNat < 2 ^ n) (hy : y.toNat < 2 ^ n) :
    Cond.l.eval (AluOp.flagsN .cmp x y) = some (decide (x.toNat < y.toNat)) := by
  simp only [AluOp.flagsN, subFlagsN, Cond.eval, kXor,
    subOverflowN_eq_false_of_small hx hy, msb_sub_of_small hx hy, Bool.bne_false]

end Silmaril.X86.Ext

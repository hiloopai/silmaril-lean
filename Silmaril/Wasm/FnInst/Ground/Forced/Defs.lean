module

public import Silmaril.Wasm.FnInst.Ground.Defs

@[expose] public section

/-! # Grounding left sides that write locals: the deferred bridge

The bridge of `Silmaril.Wasm.FnInst.Ground.Defs` (`Good`, `gBaseSim`) only accepts left sides
that never write a local and read at most one; `not_baseSim_twoSets` shows that silmaril's
`BaseSim` cannot do more, because it matches every left step in the same frame. Silmaril's
deferred simulation (`Silmaril.Wasm.Binaryen.Deferred`) relaxes exactly this: after a matched
step the left side may run a chain of **forced** local steps (an in-bounds `local.set`, a
`local.get` of a set local, a `local.tee` expansion) before the frames must agree.

This module states the pairs of that second bridge over the grounded fragment:

* `GInstr.loc`: constants and local access, the instructions whose steps are forced;
* `WPair q a r b`: a runtime pair after the values `q` (left) and `r` (right). The left side
  is `ks; i; l; p`: constants `ks`, a non-constant local instruction `i`, local code `l`
  (which may read and write several locals) and stack-only code `p`; once `i` has run on the
  pair's stack, the rest cannot get stuck (`Commits`); and the pair has equal runs from every
  frame and every stack below (`PairRef`). The right side is any code of the fragment;
* `GoodW a b := WPair [] a [] b`: the source pairs (equal runs `RunRef a b` and the side
  conditions); `GWI` and `GW`: the source and runtime relations for the deferred closure.
  The second kind of runtime pair is the stack-only rest `p` of a left side against the
  values the right side has already reached.

The simulation (`Silmaril.Proofs.Wasm.FnInst.Ground.Forced`) lets the right side **commit** at
the left's first non-constant step: it runs its whole code (`run_steps`), and the left side
completes its local code `l` as a forced chain; then its stack-only rest `p` runs while the
right side stutters (it touches no frame, so the pair is frame-free). The one exception is
`local.tee`, whose first step is an expansion that does not touch the frame: the right side
stutters and the pair moves on to `local.set`.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- Local code: constants and local access. Their steps are the forced steps of
`Silmaril.Wasm.Binaryen.Deferred` (constants are values). -/
def GInstr.loc : GInstr → Bool
  | .const _ | .localGet _ | .localSet _ | .localTee _ => true
  | _ => false

/-- The constants of a list, as `i32` values (bottom first). -/
def kvalsW (ks : List (BitVec 32)) : List Val := ks.map Val.i32

/-- After the first non-constant instruction `i` has run on the pair's stack `q ++ ks` over
any stack `S`, the rest `a₁` runs to a result. -/
def Commits (q : List Val) (ks : List (BitVec 32)) (i : GInstr) (a₁ : List GInstr) : Prop :=
  ∀ f S r, step1 i f ((q ++ kvalsW ks).reverse ++ S) = some r → (run a₁ r.1 r.2).isSome

/-- Local code followed by stack-only code. -/
def LocStk (a₁ : List GInstr) : Prop :=
  ∃ l p, a₁ = l ++ p ∧ (∀ j ∈ l, j.loc = true) ∧ ∀ j ∈ p, j.stk = true

/-- Runtime pairs of the deferred bridge (see the module docstring). -/
def WPair (q : List Val) (a : List GInstr) (r : List Val) (b : List GInstr) : Prop :=
  ∃ ks i a₁, a = ks.map GInstr.const ++ i :: a₁ ∧ i.isConst = false ∧ i.loc = true ∧
    LocStk a₁ ∧ Commits q ks i a₁ ∧ PairRef q a r b

/-- **The pairs the deferred bridge accepts**: local code with equal runs, not all
constants, that cannot get stuck after its first non-constant instruction. -/
def GoodW (a b : List GInstr) : Prop := WPair [] a [] b

/-- Source base pairs of the deferred bridge. -/
def GWI (x y : List Instr) : Prop :=
  ∃ a b, GoodW a b ∧ x = lower a ∧ y = lower b

/-- Runtime base pairs of the deferred bridge. -/
def GW (x y : List Admin) : Prop :=
  (∃ q a r b, x = vals q ++ expression (lower a) ∧ y = vals r ++ expression (lower b) ∧
    WPair q a r b) ∨
  (∃ q a r, x = vals q ++ expression (lower a) ∧ y = vals r ∧ StkOp a ∧ PairRef q a r [])

end Silmaril.Wasm.FnInst.Ground

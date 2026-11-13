module

public import Silmaril.Wasm.Instructions
public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Backward dataflow analysis over structured Wasm control flow: definitions

The monotone-framework equations of the *Optimising Compilers* notes (§2, p. 8; §3, p. 9;
`Silmaril.Calculi.Dataflow`) are written over a flowgraph. Wasm code has no flowgraph:
control is structured (`block`, `loop`, `if`) and jumps (`br`, `br_if`, `br_table`) name an
enclosing *label* by de Bruijn index. Following the structured analyses of Nipkow and
Klein, *Concrete Semantics*, §10.3–10.4, the equations are solved by recursion on the
syntax, with the value of every enclosing label carried in a *label environment*
`env : List L` (index `0` is the innermost label):

* the value of a `block`'s label is the value *after* the block (its continuation);
* the value of a `loop`'s label is the value at the loop *head*, a post-fixed point
  `X ⊒ seq (X :: env) out body`. It is computed by bounded Kleene iteration from `⊥`,
  *checked*, and replaced by `⊤` if the check fails (`loopFix`);
* `br l` takes the value of label `l`; `br_if l` joins it with the fall-through value;
  `br_table` joins all its targets; `return` and `unreachable` take `⊥` (no code of the
  function runs afterwards);
* every other instruction goes through the analysis' `transfer` function.

Only *safety* is used downstream (notes p. 8: "any solution of these dataflow equations is
safe"): `instr_loop_safe` in `Silmaril.Wasm.Dataflow.Structured.Thms` is the one place where
a fixed point is needed, and it holds by the check in `loopFix`. Precision (that the check
never fails for gen/kill problems) is not proved and not needed.

Out-of-fragment control (`try_table`, `throw`, `throw_ref`) is answered with `⊤`; the
`br_on_*` family is treated like `br_if`, tail calls like `return`.

Ported from an earlier development `Silmaril/Wasm/Dataflow/Structured.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm

/-- A backward analysis over structured Wasm code, with values in `L`. -/
structure Backward (L : Type) where
  /-- The transfer function of a straight-line instruction: the value after it
  to the value before it. -/
  transfer : Instr → L → L
  /-- The iteration budget for the fixed point at a `loop` (label environment,
  value after the loop, loop body). Any value is sound. -/
  loopFuel : List L → L → List Instr → Nat

variable {L : Type} [Lattice L] [OrderBot L] [OrderTop L] [DecidableLE L]

/-- The value of label `l` in a label environment; `⊤` for an unbound label. -/
def labelVal (env : List L) (l : LabelIdx) : L := env.getD l.toNat ⊤

/-- A checked post-fixed point of `F`: `n` Kleene iterates from `⊥`, kept if
they are already safe (`F X ≤ X`), otherwise `⊤`. -/
def loopFix (F : L → L) (n : Nat) : L :=
  if F (F^[n] ⊥) ≤ F^[n] ⊥ then F^[n] ⊥ else ⊤

namespace Backward

variable (A : Backward L)

mutual
/-- The value before one instruction, given the label environment and the value
after it. -/
def instr (env : List L) (out : L) : Instr → L
  | .block _ body => seq (out :: env) out body
  | .loop _ body => loopFix (fun X => seq (X :: env) out body) (A.loopFuel env out body)
  | .if_ _ b₁ b₂ => seq (out :: env) out b₁ ⊔ seq (out :: env) out b₂
  | .br l => labelVal env l
  | .brIf l | .brOnNull l | .brOnNonNull l | .brOnCast l _ _ | .brOnCastFail l _ _ =>
      labelVal env l ⊔ out
  | .brTable ls l => ls.foldr (fun l' acc => labelVal env l' ⊔ acc) (labelVal env l)
  | .return_ | .unreachable => ⊥
  | .returnCall _ | .returnCallRef _ | .returnCallIndirect _ _ => ⊥
  | .tryTable _ _ _ | .throw _ | .throwRef => ⊤
  | i => A.transfer i out

/-- The value before an instruction sequence, given the label environment and
the value after it. -/
def seq (env : List L) (out : L) : List Instr → L
  | [] => out
  | i :: is => instr env (seq env out is) i
end

@[simp] theorem seq_nil (env : List L) (out : L) : A.seq env out [] = out := by
  simp [seq]

@[simp] theorem seq_cons (env : List L) (out : L) (i : Instr) (is : List Instr) :
    A.seq env out (i :: is) = A.instr env (A.seq env out is) i := by
  simp [seq]

end Backward

end Silmaril.Wasm.Dataflow

module

public import Silmaril.Wasm.Auto.Equiv.Thms

/-!
# Store-to-load forwarding for the extended checker: definitions

A post-pass on the final states of the symbolic runs of `Silmaril.Wasm.Auto.Equiv`, applied to both
sides before they are compared:

* `fwd K t e`, `fwdM K m`: under the guards `K` (simplified, known to hold), a load from a memory
  term `mstore m t' p' a' arg' v`
  - **forwards** the stored value `v` when the load and the store are full-width accesses of the
    same type at the same address (equal simplified address terms, equal offsets) and the load's
    in-bounds guard is in `K` (the load is in bounds, so the store was too, and the load reads
    back the stored bytes: `Memory.load_store`);
  - **skips** the store when the two accesses have the same simplified base address and disjoint
    byte ranges by their offsets (unconditional: an in-bounds store leaves other bytes unchanged,
    `load_store_disjoint`, and an out-of-bounds store changes nothing);
* `fwdG seen G`: drops a guard equal (after simplification) to an earlier one (it cannot fail
  there), and rewrites each trap state under the guards before it;
* `fwdS S`: the whole final state, rewritten under all its guards;
* `checkXF`, `checkOutXF`: `checkX`/`checkOutX` on the forwarded states.

The soundness theorems are in `Silmaril.Wasm.Auto.EquivFwd.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivFwd

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv

/-- A load of type `t` from the (forwarded) memory term given last. -/
def fwdLoad (K : List Guard) (t : IntType) (p : Option (PackSize × Signedness)) (a : XT)
    (arg : MemArg) : XT → XT
  | .mstore m t' p' a' arg' v =>
    if p = none ∧ p' = none ∧ t' = t ∧ canon .i32 a' = canon .i32 a ∧ arg'.offset = arg.offset ∧
        Guard.inb (canon .i32 a) arg (t.width / 8) ∈ K then v
    else if canon .i32 a' = canon .i32 a ∧
        (arg'.offset.val + accBytes t' p' ≤ arg.offset.val ∨
          arg.offset.val + accBytes t (p.map Prod.fst) ≤ arg'.offset.val) then
      fwdLoad K t p a arg m
    else .load (.mstore m t' p' a' arg' v) t p a arg
  | m => .load m t p a arg

mutual

/-- **Forwarding** in a value term read at type `t`. -/
def fwd (K : List Guard) : IntType → XT → XT
  | t, .un op a => .un op (fwd K t a)
  | t, .bin op a b => .bin op (fwd K t a) (fwd K t b)
  | _, .rel t' op a b => .rel t' op (fwd K t' a) (fwd K t' b)
  | _, .wrap a => .wrap (fwd K .i64 a)
  | _, .ext sx a => .ext sx (fwd K .i32 a)
  | t, .sel c a b => .sel (fwd K .i32 c) (fwd K t a) (fwd K t b)
  | t, .load m t' p a arg =>
    if t = t' then fwdLoad K t' p (fwd K .i32 a) arg (fwdM K m)
    else .load (fwdM K m) t' p (fwd K .i32 a) arg
  | _, e => e

/-- Forwarding in a memory term. -/
def fwdM (K : List Guard) : XT → XT
  | .mstore m t p a arg v => .mstore (fwdM K m) t p (fwd K .i32 a) arg (fwd K t v)
  | e => e

end

/-- Forwarded slots. -/
def fwdSlots (K : List Guard) (l : List (IntType × XT)) : List (IntType × XT) :=
  l.map fun p => (p.1, fwd K p.1 p.2)

/-- A state rewritten under the guards `K`. -/
def fwdT (K : List Guard) (T : XState) : XState where
  locals := fwdSlots K T.locals
  stack := fwdSlots K T.stack
  globs := fwdSlots K T.globs
  mem := fwdM K T.mem
  guards := []

/-- Guards without repetitions, trap states rewritten under the guards before them. -/
def fwdG (seen : List Guard) : List (Guard × XState) → List (Guard × XState)
  | [] => []
  | (g, T) :: G =>
    if g.canon ∈ seen then fwdG seen G else (g, fwdT seen T) :: fwdG (g.canon :: seen) G

/-- **The forwarded final state.** -/
def fwdS (S : XState) : XState :=
  let K := S.guards.map fun g => g.1.canon
  { fwdT K S with guards := fwdG [] S.guards }

/-- **The equivalence check with forwarding.** -/
def checkXF (lt st gt : List IntType) (mem : Bool) (a b : List Instr) : Bool :=
  match xsexec mem (initX lt st gt) a, xsexec mem (initX lt st gt) b with
  | some A, some B =>
    let A' := fwdS A
    let B' := fwdS B
    decide (guardKeys A' = guardKeys B') && decide (A'.key = B'.key) &&
      decide (canonSlots A'.stack = canonSlots B'.stack)
  | _, _ => false

end Silmaril.Wasm.Auto.EquivFwd

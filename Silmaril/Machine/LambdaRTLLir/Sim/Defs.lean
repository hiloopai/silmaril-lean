module

public import Silmaril.Machine.LambdaRTLLir.Defs
public import Silmaril.Machine.CBackend.Lir.Semantics.Defs

/-!
# λRTL to the C-backend `Lir` machine: lowering of a word fragment

The operator model of `Silmaril.Machine.LambdaRTLLir` is built on `Lir`'s
`Silmaril.Machine.Lir.{Unop,Binop}` (header `Silmaril.Machine.CBackend.Lir.Syntax.Defs`, which the
RTL closure re-exports), whose small-step machine (`Silmaril.Machine.Lir.step`) is the simulation
target here. The source of this file was written against two textually identical copies of
those types; it states the operator model again as `COp`, `capp`, `cmodel`, kept as is; `Lir` evaluation and λRTL instruction semantics then agree by
`rfl`. The value type `LVal` is reused (both copies define `Word := BitVec 64`).

Fragment (over `V = R`, the `Lir` registers):

* `opLower d o`: `const w`, `unary u (var y)` and `binary b (pair (var y) (var z))` lower to the
  `Lir` operations `const d w`, `unary u d y`, `binary b d y z`;
* `lowerPre k`: the maximal prefix of `let1` bindings whose operands lower, and the remaining
  region (`tail k`); `lower k` is the list of operations;
* `StraightWord k`: the tail is `br ℓ (var r)`; it lowers to the one-block function
  `straightProg params k r` ending in `ret [reg r]`;
* `condProg`: the tail is `case (app test (var c)) x r₁ y r₂` with straight-line branches; it
  lowers to an entry block ending in `branch c 1 2` and two returning blocks.

`AgreeOn S σ fr` relates a λRTL store to a `Lir` frame on the registers in `S`: the frame holds
`w` exactly where the store holds `word w`, and is unwritten where the store holds a non-word.
`expect` is the `Lir` behaviour predicted by a λRTL outcome.
-/

@[expose] public section

namespace Silmaril.Machine.LambdaRTLLir.Sim

open Silmaril.Machine.Lir
open Silmaril.SSA.LambdaRTL (Region Model Val upd obs)

/-- Instructions over the C-backend `Lir` operators. -/
inductive COp
  | const (w : Word)
  | unary (u : Unop)
  | binary (b : Binop)
  | test
  deriving DecidableEq

/-- Instruction semantics, from the C-backend `Unop.eval` and `Binop.eval`. -/
def capp : COp → LVal → Option LVal
  | .const w, _ => some (.word w)
  | .unary u, .word x => some (.word (u.eval x))
  | .binary b, .pair (.word x) (.word y) => (b.eval x y).map .word
  | .test, .word x => some (if x ≠ 0 then .inl .unit else .inr .unit)
  | _, _ => none

/-- The λRTL model of C-backend `Lir` operators in `Option`. -/
def cmodel : Model COp Option LVal where
  unit := .unit
  pair := .pair
  inl := .inl
  inr := .inr
  unpair
    | .pair a b => some (a, b)
    | _ => none
  split
    | .inl a => some (.inl a)
    | .inr b => some (.inr b)
    | _ => none
  app := capp
  abort _ := none

/-- The word held by a value, if it is one. -/
def wordOf : LVal → Option Word
  | .word w => some w
  | _ => none

variable {R L : Type} [DecidableEq R]

/-- Store/frame agreement on a set of registers. -/
def AgreeOn (S : Finset R) (σ : R → LVal) (fr : Frame R) : Prop :=
  ∀ x ∈ S, fr.get x = wordOf (σ x)

/-- Lowering of one binding `d := o` of the fragment. -/
def opLower (d : R) : Silmaril.SSA.LambdaRTL.Op R COp → Option (Op R)
  | .app (.const w) _ => some (.const d w)
  | .app (.unary u) (.var y) => some (.unary u d y)
  | .app (.binary b) (.pair (.var y) (.var z)) => some (.binary b d y z)
  | _ => none

/-- The maximal lowerable `let1` prefix, and the rest of the region. -/
def lowerPre : Region R L COp → List (Op R) × Region R L COp
  | .let1 x o k =>
    match opLower x o with
    | some i => (i :: (lowerPre k).1, (lowerPre k).2)
    | none => ([], .let1 x o k)
  | k => ([], k)

/-- The `Lir` operations of the lowerable prefix. -/
def lower (k : Region R L COp) : List (Op R) := (lowerPre k).1

/-- The region after the lowerable prefix. -/
def tail (k : Region R L COp) : Region R L COp := (lowerPre k).2

/-- The returned register of a `br ℓ (var r)`. -/
def retReg : Region R L COp → Option R
  | .br _ (.var r) => some r
  | _ => none

/-- The word-only straight-line fragment: lowerable bindings ending in `br ℓ (var r)`. -/
def StraightWord (k : Region R L COp) : Prop := (retReg (tail k)).isSome = true

instance (k : Region R L COp) : Decidable (StraightWord k) :=
  inferInstanceAs (Decidable (_ = true))

/-- The returning block of a straight-line region. -/
def retBlock (k : Region R L COp) (r : R) : Block R := ⟨(lower k).map .op, .ret [.reg r]⟩

/-- One-function, one-block program of a straight-line region returning register `r`. -/
def straightProg (params : List (Loc R)) (k : Region R L COp) (r : R) : Prog R :=
  ⟨[⟨params, 0, [retBlock k r]⟩]⟩

/-- Lowering of a `StraightWord` region (`none` outside the fragment). -/
def lowerStraight (params : List (Loc R)) (k : Region R L COp) : Option (Prog R) :=
  (retReg (tail k)).map (straightProg params k)

/-- The `case` on `test (var c)` at the end of a prefix: `(c, x, r₁, y, r₂)`. -/
def testCase : Region R L COp → Option (R × R × Region R L COp × R × Region R L COp)
  | .case (.app .test (.var c)) x r₁ y r₂ => some (c, x, r₁, y, r₂)
  | _ => none

/-- Three-block program of a prefix ending in `case (test c)` with straight-line branches:
block `0` runs the prefix and branches on `c`, blocks `1`/`2` run the `inl`/`inr` branch. -/
def condProg (params : List (Loc R)) (k : Region R L COp) (c : R) (r₁ : Region R L COp) (a : R)
    (r₂ : Region R L COp) (b : R) : Prog R :=
  ⟨[⟨params, 0, [⟨(lower k).map .op, .branch c 1 2⟩, retBlock r₁ a, retBlock r₂ b]⟩]⟩

/-- Lowering of a prefix ending in a `test` case with straight-line branches whose payload
binders are dead (`none` outside this fragment). -/
def lowerCond (params : List (Loc R)) (k : Region R L COp) : Option (Prog R) :=
  match testCase (tail k) with
  | some (c, x, r₁, y, r₂) =>
    match retReg (tail r₁), retReg (tail r₂) with
    | some a, some b =>
      if x ∉ r₁.fv ∧ y ∉ r₂.fv then some (condProg params k c r₁ a r₂ b) else none
    | _, _ => none
  | none => none

/-- The `Lir` behaviour predicted by a λRTL outcome: return the word, otherwise stuck. -/
def expect (o : Option (L × LVal)) (m : Memory) : Behavior :=
  match o.bind (fun e => wordOf e.2) with
  | some w => .returned [w] m
  | none => .stuck

end Silmaril.Machine.LambdaRTLLir.Sim

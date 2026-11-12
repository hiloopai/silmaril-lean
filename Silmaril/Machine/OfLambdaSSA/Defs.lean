module

public import Silmaril.Machine.RTL.Thms

/-!
# The RTL fragment of lambda-SSA

`RTL.SSA.ofLambdaSSA` flattens a lambda-SSA region over RTL opcodes into an
SSA-form RTL function. Its compiler keeps one register per word and never looks
at types, so a region can compile and still mean something else in RTL:

* a `pair` whose first component is a tuple compiles to the concatenation of the
  two register lists, while lambda-SSA keeps the nested pair;
* under the root wrapper `cfg (br 0 (var 0)) 1 …`, the function's argument
  (variable `1` inside the block) and the block's current parameter (variable
  `0`) are compiled to the same registers, so after a back edge they disagree.

`Thms` proves both failures on concrete regions. This file states the fragment
in which the compiler is correct, as a judgment that follows the compiler
case by case.

A value of the fragment has a `Shape`: a single word (`atom w`, one register),
or a flat tuple of `n` words (`packValues ws`, `n` registers). A `pair` puts a
word in front of a tuple, `let₂` takes the front word off a nonempty tuple,
opcodes take and return tuples of their arities, labels carry tuples of fixed
widths, and the blocks of a `cfg` take tuples of the widths recorded in the
annotation. Under the root wrapper, the block sees only its own parameter.
-/

@[expose] public section

namespace Silmaril.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

/-- The shape of a value of the RTL fragment. -/
inductive Shape where
  /-- One word, held as `atom w` in one register. -/
  | word
  /-- A flat tuple of `n` words, held as `packValues ws` in `n` registers. -/
  | tuple (n : ℕ)
  deriving DecidableEq

/-- `v` is the value of shape `s` whose words, in register order, are `ws`. -/
def Shape.Holds : Shape → Value Word → List Word → Prop
  | .word, v, ws => ∃ w, v = .atom w ∧ ws = [w]
  | .tuple n, v, ws => v = packValues ws ∧ ws.length = n

variable {sigs : List RTL.Signature}

/-- A term of the fragment, in a context of shapes, has a shape. The branch
test is not a term of the fragment: it only appears as the scrutinee of a
`case`. -/
inductive TmFits (sigs : List RTL.Signature) : List Shape → Tm (Opcode sigs) → Shape → Prop where
  | var {Γ : List Shape} {i : ℕ} {s : Shape} : Γ[i]? = some s → TmFits sigs Γ (.var i) s
  | unit {Γ : List Shape} : TmFits sigs Γ .unit (.tuple 0)
  | pair {Γ : List Shape} {a b : Tm (Opcode sigs)} {n : ℕ} :
      TmFits sigs Γ a .word → TmFits sigs Γ b (.tuple n) → TmFits sigs Γ (.pair a b) (.tuple (n + 1))
  | op {Γ : List Shape} {f : Opcode sigs} {a : Tm (Opcode sigs)} :
      f ≠ .test → TmFits sigs Γ a (.tuple f.arity) → TmFits sigs Γ (.op f a) (.tuple f.results)
  | let₁ {Γ : List Shape} {a b : Tm (Opcode sigs)} {s s' : Shape} :
      TmFits sigs Γ a s → TmFits sigs (s :: Γ) b s' → TmFits sigs Γ (.let₁ a b) s'
  | let₂ {Γ : List Shape} {a b : Tm (Opcode sigs)} {n : ℕ} {s' : Shape} :
      TmFits sigs Γ a (.tuple (n + 1)) → TmFits sigs (.tuple n :: .word :: Γ) b s' →
      TmFits sigs Γ (.let₂ a b) s'

/-- A region of the fragment, with its annotation, in a context of shapes and
under labels carrying tuples of the given widths. -/
inductive RegionFits (sigs : List RTL.Signature) :
    List Shape → Region (Opcode sigs) → SSA.Ann → List ℕ → Prop where
  | br {Γ : List Shape} {L : List ℕ} {ℓ w : ℕ} {arg : Tm (Opcode sigs)} :
      L[ℓ]? = some w → TmFits sigs Γ arg (.tuple w) → RegionFits sigs Γ (.br ℓ arg) .br L
  | let₁ {Γ : List Shape} {L : List ℕ} {a : Tm (Opcode sigs)} {body : Region (Opcode sigs)}
      {ab : SSA.Ann} {s : Shape} :
      TmFits sigs Γ a s → RegionFits sigs (s :: Γ) body ab L →
      RegionFits sigs Γ (.let₁ a body) (.let₁ ab) L
  | let₂ {Γ : List Shape} {L : List ℕ} {a : Tm (Opcode sigs)} {body : Region (Opcode sigs)}
      {ab : SSA.Ann} {n : ℕ} :
      TmFits sigs Γ a (.tuple (n + 1)) → RegionFits sigs (.tuple n :: .word :: Γ) body ab L →
      RegionFits sigs Γ (.let₂ a body) (.let₂ ab) L
  | case {Γ : List Shape} {L : List ℕ} {arg : Tm (Opcode sigs)} {l r : Region (Opcode sigs)}
      {al ar : SSA.Ann} :
      TmFits sigs Γ arg (.tuple 1) → RegionFits sigs (.tuple 0 :: Γ) l al L →
      RegionFits sigs (.tuple 0 :: Γ) r ar L →
      RegionFits sigs Γ (.case (.op .test arg) l r) (.case al ar) L
  | cfg {Γ : List Shape} {L : List ℕ} {entry : Region (Opcode sigs)} {k : ℕ}
      {blocks : Fin k → Region (Opcode sigs)} {ws : List ℕ} {ae : SSA.Ann} {abs : List SSA.Ann} :
      ws.length = k → RegionFits sigs Γ entry ae (ws ++ L) →
      (∀ i : Fin k, RegionFits sigs (.tuple (ws.getD i 0) :: Γ) (blocks i) (abs.getD i .br)
        (ws ++ L)) →
      RegionFits sigs Γ (.cfg entry k blocks) (.cfg ws ae abs) L

/-- A function body of the fragment, for a function taking `params` words and
returning `results`. Labels `0` and `1` are the return and the trap. Under the
root wrapper `cfg (br 0 (var 0)) 1 …` the block is checked in a context holding
only its own parameter, the context `rootOps` compiles it in. -/
def RootFits (sigs : List RTL.Signature) (r : Region (Opcode sigs)) (a : SSA.Ann)
    (params results : ℕ) : Prop :=
  match r, a with
  | .cfg (.br 0 (.var 0)) 1 blocks, .cfg [w] .br [ab] =>
      w = params ∧ RegionFits sigs [.tuple params] (blocks 0) ab [params, results, 0]
  | r, a => RegionFits sigs [.tuple params] r a [results, 0]

/-! ## Examples

Regions used to show what the fragment excludes and includes. -/

/-- A call oracle that never returns: every call is stuck. -/
def noCalls : CallOracle := fun _ _ _ _ _ => False

/-- `br 0 (pair (var 0) unit)`, for a function of one word to one word: the
pair's first component is a tuple. -/
def pairExample : Region (Opcode []) := .br 0 (.pair (.var 0) .unit)

/-- A loop through the root wrapper that returns its block's parameter: like
`RTL.SSA.aliasRegion`, but its exit reads variable `1`, the block's word,
instead of the function's argument. -/
def loopExample : Region (Opcode []) :=
  .cfg (.br 0 (.var 0)) 1 fun _ =>
    .case (.op .test (.var 0)) (.br 0 (.op (.const 0) .unit)) (.br 1 (.var 1))

end Silmaril.Machine.OfLambdaSSA

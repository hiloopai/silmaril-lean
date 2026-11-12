module

public import Silmaril.Wasm.SpecTec.Sim10.Encode.Defs
public import Silmaril.Wasm.SpecTec.Sim.Floats.Defs
public import Silmaril.Wasm.SpecTec.Sim20.Pure.Defs

/-!
# The 1.0 numeric agreement hypothesis

`NumAgree10 env P` says that the wasm-1.0 script's numeric dispatchers `$unop_`, `$binop_`,
`$testop_`, `$relop_` and `$cvtop__`, read in `env`, return at the encodings of V1 operands
exactly V1's numeric results under the profile `P` (`Silmaril.Wasm.Numerics`): every result the
profile allows for the set-valued float operators and the float resizings, the one result for the
others, and the empty list exactly where V1 traps (integer division, `trunc`).

It is the 1.0 counterpart of `Sim20.Pure.NumAgree` and `CvtAgree`, stated against V1's operators
(`V1.IntUnOp` has no `extend`, and `V1.ConvertOp` no `truncSat`). At the spec profile
`Profile.spec nd r` the profile's float relations are V1's (`floatUnOpRel`, `floatBinOpRel`,
`convertRel`), so `NumAgree10 env (Profile.spec nd r)` is what the numeric rules of V1's
`PureStep` need. `Sim10.Num.Thms` proves it at `Sim.Floats.floatIntB P`, for every `P`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10

open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.SpecTec.Sim20 (numTypeV intBinOpV floatUnOpV floatBinOpV intTestOpV intRelOpV
  floatRelOpV)

/-- The arguments of `$cvtop__` at a V1 conversion `op` and operand `x`. -/
abbrev cvtArgsV1 (op : V1.ConvertOp) (x : BitVec op.toCore.source.width) : List ArgV :=
  [.val (numTypeV op.toCore.source), .val (numTypeV op.toCore.target), .val (cvtOpV op),
    .val (numV ⟨op.toCore.source, x⟩)]

/-- **The 1.0 numeric agreement hypothesis** at a profile `P`. -/
structure NumAgree10 (env : Env) (P : Profile) : Prop where
  /-- `$unop_(Inn, …)`: Core's `intUnOp`. -/
  intUnOp : ∀ (t : IntType) (op : V1.IntUnOp) (x : BitVec t.width),
    Applies env "unop_" [.val (numTypeV (.int t)), .val (intUnOpV op), .val (pctV x.toNat)]
      (.list [pctV (intUnOp t op.toCore x).toNat])
  /-- `$unop_(Fnn, …)`: every result the profile allows. -/
  floatUnOp : ∀ (t : FloatType) (op : FloatUnOp) (x : BitVec t.width),
    ∃ vs, Applies env "unop_" [.val (numTypeV (.float t)), .val (floatUnOpV op),
      .val (Sim.floatV t x)] (.list vs) ∧
      ∀ c, c ∈ vs ↔ ∃ z, floatUnOpP P t op x z ∧ c = Sim.floatV t z
  /-- `$binop_(Inn, …)`: Core's `intBinOp`; the list is empty exactly when it traps. -/
  intBinOp : ∀ (t : IntType) (op : IntBinOp) (x y : BitVec t.width),
    ∃ vs, Applies env "binop_" [.val (numTypeV (.int t)), .val (intBinOpV op),
      .val (pctV x.toNat), .val (pctV y.toNat)] (.list vs) ∧
      ∀ c, c ∈ vs ↔ ∃ z, intBinOp t op x y = .ok z ∧ c = pctV z.toNat
  /-- `$binop_(Fnn, …)`: every result the profile allows. -/
  floatBinOp : ∀ (t : FloatType) (op : FloatBinOp) (x y : BitVec t.width),
    ∃ vs, Applies env "binop_" [.val (numTypeV (.float t)), .val (floatBinOpV op),
      .val (Sim.floatV t x), .val (Sim.floatV t y)] (.list vs) ∧
      ∀ c, c ∈ vs ↔ ∃ z, floatBinOpP P t op x y z ∧ c = Sim.floatV t z
  /-- `$testop_(Inn, …)`. -/
  intTestOp : ∀ (t : IntType) (op : IntTestOp) (x : BitVec t.width),
    Applies env "testop_" [.val (numTypeV (.int t)), .val (intTestOpV op), .val (pctV x.toNat)]
      (pctV (intTestOp t op x).toNat)
  /-- `$relop_(Inn, …)`. -/
  intRelOp : ∀ (t : IntType) (op : IntRelOp) (x y : BitVec t.width),
    Applies env "relop_" [.val (numTypeV (.int t)), .val (intRelOpV op), .val (pctV x.toNat),
      .val (pctV y.toNat)] (pctV (intRelOp t op x y).toNat)
  /-- `$relop_(Fnn, …)`. -/
  floatRelOp : ∀ (t : FloatType) (op : FloatRelOp) (x y : BitVec t.width),
    Applies env "relop_" [.val (numTypeV (.float t)), .val (floatRelOpV op),
      .val (Sim.floatV t x), .val (Sim.floatV t y)] (pctV (floatRelOp t op x y).toNat)
  /-- `$cvtop__` at a V1 conversion: the profile's results, empty exactly when it traps. -/
  cvtOp : ∀ (op : V1.ConvertOp) (x : BitVec op.toCore.source.width),
    ∃ vs, Applies env "cvtop__" (cvtArgsV1 op x) (.list vs) ∧
      (∀ c, c ∈ vs ↔ ∃ z, convertP P op.toCore x (.ok z) ∧ c = numV ⟨op.toCore.target, z⟩) ∧
      (vs = [] ↔ ∃ e, convertP P op.toCore x (.error e))

end Silmaril.Wasm.SpecTec.Sim10

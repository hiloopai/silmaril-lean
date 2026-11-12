module

public import Silmaril.Wasm.SpecTec.Sim20.VecAgree.Defs
public import Silmaril.Wasm.SpecTec.Sim20.Encode.Defs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecNumeric

/-!
# Vector lanes and vector numerics of wasm-2.0 (definitions)

`VecNumAgree env P`: the corrected script's vector numeric functions `$vunop_`, `$vbinop_` and
`$vrelop_` return, at the encodings of V2 operands, exactly V2's results: the list of every
result V2 permits for the set-valued unary and binary operators, the one result for the
comparisons. It is the vector counterpart of round 3's `Pure.NumAgree` and, like it, a statement
about the script's `3-numerics` and the builtins that is **assumed**, not proved. The script
computes these functions lane-wise, through `$lanes_`, the lane primitives (`$fabs_`, `$iadd_`, …)
and `$inv_lanes_`; reducing `VecNumAgree` to the lane primitives is not done here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecLane

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)

/-- **The vector numerics hypothesis**, at the float shapes and at the integer shapes. -/
structure VecNumAgree (env : Env) (P : Profile) : Prop where
  /-- `$vunop_(Fnn X M, …)`. -/
  floatUn : ∀ (s : FloatShape) (op : FloatUnOp) (c : BitVec 128),
    ∃ vs, Applies env "vunop_" [.val (shapeV (.float s)), .val (floatUnOpV op), .val (pctV c.toNat)]
      (.list vs) ∧ ∀ w, w ∈ vs ↔ ∃ r, VecFloatUnOpResult P s op c r ∧ w = pctV r.toNat
  /-- `$vbinop_(Fnn X M, …)`. -/
  floatBin : ∀ (s : FloatShape) (op : V2.VecFloatBinOp) (c₁ c₂ : BitVec 128),
    ∃ vs, Applies env "vbinop_" [.val (shapeV (.float s)), .val (vecFloatBinOpV op),
      .val (pctV c₁.toNat), .val (pctV c₂.toNat)] (.list vs) ∧
      ∀ w, w ∈ vs ↔ ∃ r, VecFloatBinOpResult P s op c₁ c₂ r ∧ w = pctV r.toNat
  /-- `$vrelop_(Fnn X M, …)`. -/
  floatRel : ∀ (s : FloatShape) (op : FloatRelOp) (c₁ c₂ : BitVec 128),
    Applies env "vrelop_" [.val (shapeV (.float s)), .val (floatRelOpV op), .val (pctV c₁.toNat),
      .val (pctV c₂.toNat)] (pctV (VecFloatRelOp s op c₁ c₂).toNat)
  /-- `$vunop_(Jnn X M, …)`. -/
  intUn : ∀ (s : IntShape) (op : VecIntUnOp) (c : BitVec 128),
    ∃ vs, Applies env "vunop_" [.val (shapeV (.int s)), .val (vecIntUnOpV op), .val (pctV c.toNat)]
      (.list vs) ∧ ∀ w, w ∈ vs ↔ ∃ r, VecIntUnOpResult s op c r ∧ w = pctV r.toNat
  /-- `$vbinop_(Jnn X M, …)`. -/
  intBin : ∀ (s : IntShape) (op : V2.VecIntBinOp) (c₁ c₂ : BitVec 128),
    ∃ vs, Applies env "vbinop_" [.val (shapeV (.int s)), .val (vecIntBinOpV op),
      .val (pctV c₁.toNat), .val (pctV c₂.toNat)] (.list vs) ∧
      ∀ w, w ∈ vs ↔ ∃ r, VecIntBinOpResult P s op c₁ c₂ r ∧ w = pctV r.toNat
  /-- `$vrelop_(Jnn X M, …)`. -/
  intRel : ∀ (s : IntShape) (op : IntRelOp) (c₁ c₂ : BitVec 128),
    Applies env "vrelop_" [.val (shapeV (.int s)), .val (vecIntRelOpV op), .val (pctV c₁.toNat),
      .val (pctV c₂.toNat)] (pctV (VecIntRelOp s op c₁ c₂).toNat)

end Silmaril.Wasm.SpecTec.Sim20.VecLane

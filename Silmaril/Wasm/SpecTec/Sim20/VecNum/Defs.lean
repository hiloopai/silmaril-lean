module

public import Silmaril.Wasm.SpecTec.Sim20.VecLane.Thms

/-!
# The vector numeric dispatchers of wasm-2.0 as builtins (definitions)

Round 7 assumed `VecLane.VecNumAgree env P`: the script's `$vunop_`, `$vbinop_` and `$vrelop_`
return V2's results. In the 2.0 script every clause of the three dispatchers binds the lanes of
its operands in an `if` premise (`lane_1* = $lanes_(sh, v128_1)`), which the IL evaluator only
tests, so every clause definitely fails (`VecNum.tryClausesUndef_of_all`, kernel-checked as
`clauseUnb_vunop` … for `Original.d263`–`d265`). A call therefore denotes exactly what the
builtins answer. So `VecNumAgree` is a statement about the builtins alone:

* it is **false** at round 7's builtins `VecLane.vecB P`, and at every `B` that does not answer
  `$vunop_` (`VecNum.not_vecNumAgree`);
* it **holds** at `vecNB P` below, which is `vecB P` with the three dispatchers answered by V2's
  result lists (`VecNum.vecNumAgree_vecNB`).

This header gives the encodings of the dispatcher arguments, a classical decoding (`dec`), the
answers (`vecNCall`) and the builtins `vecNB P`. Away from `$vunop_`, `$vbinop_` and `$vrelop_`,
`vecNB P` answers as `vecB P` does.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecNum

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (pctV)

/-! ## Encoded arguments -/

/-- The arguments of `$vunop_(Fnn X M, op, c)`. -/
def encFU (a : FloatShape × FloatUnOp × BitVec 128) : List ArgV :=
  [.val (shapeV (.float a.1)), .val (floatUnOpV a.2.1), .val (pctV a.2.2.toNat)]

/-- The arguments of `$vbinop_(Fnn X M, op, c₁, c₂)`. -/
def encFB (a : FloatShape × V2.VecFloatBinOp × BitVec 128 × BitVec 128) : List ArgV :=
  [.val (shapeV (.float a.1)), .val (vecFloatBinOpV a.2.1), .val (pctV a.2.2.1.toNat),
    .val (pctV a.2.2.2.toNat)]

/-- The arguments of `$vrelop_(Fnn X M, op, c₁, c₂)`. -/
def encFR (a : FloatShape × FloatRelOp × BitVec 128 × BitVec 128) : List ArgV :=
  [.val (shapeV (.float a.1)), .val (floatRelOpV a.2.1), .val (pctV a.2.2.1.toNat),
    .val (pctV a.2.2.2.toNat)]

/-- The arguments of `$vunop_(Jnn X M, op, c)`. -/
def encIU (a : IntShape × VecIntUnOp × BitVec 128) : List ArgV :=
  [.val (shapeV (.int a.1)), .val (vecIntUnOpV a.2.1), .val (pctV a.2.2.toNat)]

/-- The arguments of `$vbinop_(Jnn X M, op, c₁, c₂)`. -/
def encIB (a : IntShape × V2.VecIntBinOp × BitVec 128 × BitVec 128) : List ArgV :=
  [.val (shapeV (.int a.1)), .val (vecIntBinOpV a.2.1), .val (pctV a.2.2.1.toNat),
    .val (pctV a.2.2.2.toNat)]

/-- The arguments of `$vrelop_(Jnn X M, op, c₁, c₂)`. -/
def encIR (a : IntShape × IntRelOp × BitVec 128 × BitVec 128) : List ArgV :=
  [.val (shapeV (.int a.1)), .val (vecIntRelOpV a.2.1), .val (pctV a.2.2.1.toNat),
    .val (pctV a.2.2.2.toNat)]

/-- **Classical decoding**: the `a` with `enc a = ws`, if there is one. On an injective `enc`, it
inverts `enc` (`VecNum.dec_enc`). -/
noncomputable def dec {α : Type} (enc : α → List ArgV) (ws : List ArgV) : Option α :=
  open Classical in
  if h : ∃ a, enc a = ws then some (Classical.choose h) else none

/-! ## The answers -/

/-- The V2 results as a list of `vec_(V128)` values. -/
noncomputable def resList (R : BitVec 128 → Prop) : Value :=
  .list ((Sim.Floats.bitsWhere 128 R).map fun r => pctV r.toNat)

/-- `$vunop_`: every result V2 permits. -/
noncomputable def vunopCall (P : Profile) (ws : List ArgV) : Option Value :=
  ((dec encFU ws).map fun a => resList (VecFloatUnOpResult P a.1 a.2.1 a.2.2)).or
    ((dec encIU ws).map fun a => resList (VecIntUnOpResult a.1 a.2.1 a.2.2))

/-- `$vbinop_`: every result V2 permits. -/
noncomputable def vbinopCall (P : Profile) (ws : List ArgV) : Option Value :=
  ((dec encFB ws).map fun a => resList (VecFloatBinOpResult P a.1 a.2.1 a.2.2.1 a.2.2.2)).or
    ((dec encIB ws).map fun a => resList (VecIntBinOpResult P a.1 a.2.1 a.2.2.1 a.2.2.2))

/-- `$vrelop_`: V2's comparison. -/
noncomputable def vrelopCall (ws : List ArgV) : Option Value :=
  ((dec encFR ws).map fun a => pctV (VecFloatRelOp a.1 a.2.1 a.2.2.1 a.2.2.2).toNat).or
    ((dec encIR ws).map fun a => pctV (VecIntRelOp a.1 a.2.1 a.2.2.1 a.2.2.2).toNat)

/-- The three dispatchers, and nothing else. -/
noncomputable def vecNCall (P : Profile) (x : IL.Id) (ws : List ArgV) : Option Value :=
  if x = "vunop_" then vunopCall P ws
  else if x = "vbinop_" then vbinopCall P ws
  else if x = "vrelop_" then vrelopCall ws
  else none

/-- **Round 7's builtins `VecLane.vecB P` with the three vector numeric dispatchers answered.** -/
noncomputable def vecNB (P : Profile) : Builtins :=
  ⟨fun x ws => (vecNCall P x ws).or ((VecLane.vecB P).call x ws)⟩

end Silmaril.Wasm.SpecTec.Sim20.VecNum

module

public import Silmaril.Wasm.Verify.Reach.Defs

@[expose] public section

/-!
# Escaping references and callable functions

The per-export reachability invariant behind `Silmaril.Wasm.Verify.checkFrom`. The invariant
`CfgIn G fs Pl` of `Silmaril.Wasm.Verify.Reach` uses one set `G` both for references that may sit
in values and for functions that may be called: a direct `call x` becomes
`ref.func a; call_ref` (the administrative pair `.ref (.func a), .callRefType d`), so the callee
is, for one step, a reference value of the code. Here the two are told apart:

* `V`: the function references that may appear as **values** anywhere (the store, locals,
  operands), the *escaping* functions;
* `C`: the functions that may be **called** during an activation (direct callees of the
  export's function, closed under calls, and every function of `V`, for indirect calls).

A reference is *transient* when it is immediately followed by `callRefType` or
`returnCallRefType` (`callAdm`): those pairs are created only by `call` and `return_call`, and
consumed by the call. `LooseIn V b code` says that every reference of the code other than a
transient one is in `V`, and every frame's locals hold references into `V`; the flag `b` says
whether the code is itself followed by a call (`nextCall`). Transient references are only
required to be in `C`, by the reachability invariant `CfgIn C`.

* `instrRefFuncs i`: the function indices named by `ref.func` (nested bodies included).
* `RefFuncIn V fs i`: those resolve into `V`; `PlVC V C fs i`: `InstrIn C fs i` and
  `RefFuncIn V fs i`, the source-instruction predicate of the split analysis.
* `VIn V b c`: the store holds references into `V`, the frame's locals too, and `LooseIn V b`
  of the code.

The preservation theorem is `Silmaril.Proofs.Wasm.Verify.Split.Step` (`Step.vIn`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-! ## `ref.func` targets -/

mutual

/-- The function indices named by `ref.func` in an instruction, including nested bodies. -/
def instrRefFuncs : Instr → List Nat
  | .refFunc x => [x.toNat]
  | .block _ b => exprRefFuncs b
  | .loop _ b => exprRefFuncs b
  | .tryTable _ _ b => exprRefFuncs b
  | .if_ _ b₁ b₂ => exprRefFuncs b₁ ++ exprRefFuncs b₂
  | _ => []

/-- `instrRefFuncs` of an instruction sequence. -/
def exprRefFuncs : List Instr → List Nat
  | [] => []
  | i :: is => instrRefFuncs i ++ exprRefFuncs is

end

/-- Every `ref.func` target of `i` resolves, through `fs`, into `V`. -/
def RefFuncIn (V : Nat → Prop) (fs : List Nat) (i : Instr) : Prop :=
  ∀ x ∈ instrRefFuncs i, ∀ a, fs[x]? = some a → V a

/-- The source-instruction predicate of the split analysis: named functions in `C`,
`ref.func` targets in `V`. -/
def PlVC (V C : Nat → Prop) (fs : List Nat) (i : Instr) : Prop :=
  InstrIn C fs i ∧ RefFuncIn V fs i

/-! ## Transient references -/

/-- The administrative call instructions that consume a transient reference. -/
def callAdm : Admin → Bool
  | .callRefType _ => true
  | .returnCallRefType _ => true
  | _ => false

/-- Whether the code is followed by a call instruction (`b`: what follows the whole list). -/
def nextCall (b : Bool) : List Admin → Bool
  | [] => b
  | x :: _ => callAdm x

/-- The locals of a frame hold references into `V`. -/
def LocalsIn (V : Nat → Prop) (fr : Frame) : Prop :=
  ∀ r, some (Val.ref r) ∈ fr.locals → RefIn V r

/-- Every non-transient reference of the code is in `V`, and every frame's locals hold
references into `V`. The flag `b` says whether the code is followed by a call instruction;
bodies of labels, handlers and frames are followed by none. -/
def LooseIn (V : Nat → Prop) : Bool → List Admin → Prop
  | _, [] => True
  | b, .ref r :: l => (RefIn V r ∨ nextCall b l = true) ∧ LooseIn V b l
  | b, .label _ _ body :: l => LooseIn V false body ∧ LooseIn V b l
  | b, .handler _ _ body :: l => LooseIn V false body ∧ LooseIn V b l
  | b, .frame _ fr body :: l => LocalsIn V fr ∧ LooseIn V false body ∧ LooseIn V b l
  | b, .plain _ :: l => LooseIn V b l
  | b, .callRefType _ :: l => LooseIn V b l
  | b, .returnCallRefType _ :: l => LooseIn V b l
  | b, .trap :: l => LooseIn V b l

/-- **The escaping-reference invariant** of a configuration. -/
def VIn {H : Type} (V : Nat → Prop) (b : Bool) (c : Config H) : Prop :=
  StoreIn V c.store ∧ LocalsIn V c.frame ∧ LooseIn V b c.code

end Silmaril.Wasm.Verify

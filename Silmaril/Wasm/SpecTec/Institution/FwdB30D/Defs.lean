module

public import Silmaril.Wasm.SpecTec.Institution.FwdB30S.Defs
public import Silmaril.Wasm.SpecTec.Institution.FwdB30X.Defs

/-!
# `Step` facts at `Wasm30.builtins` at non-rigid successors: definitions

`FwdB30S` made the facts of `stepModel Wasm30.builtins` exact (at `adminsToV is'` itself, not
only up to `CfgRel`) when the successor's code is `RigidV`: no `CALL_REF`, label, handler or
frame at the top. This topic looks inside label, handler and frame bodies.

* `deepRigid a`: `a` is not a `CALL_REF` (in either representation), and, if it is a label, a
  handler or a frame, its body is `deepRigidL`. `Bwd.AdminEq` relates a `deepRigid` instruction
  only to itself (`FwdB30D.adminEq_deep`).
* `callFree body`: no instruction of `body` is a `call_ref` at the top. Nested blocks need not
  be checked: `Bwd.AdminEq` compares instructions that are not administrative by equality.

For the `Step` rules of unbounded arity (`struct.new`, `array.new_fixed`, `throw`, whose value
prefix has any length), the forced-length check of `FwdB30S.stepOk` fails: a rule forcing no
length does not refute a proper infix ending in the same instruction. The right-hand side does
instead: a `ctxt-instrs` step there would have to step a proper suffix of the redex to a code
shorter than every right-hand side the suffix could match.

* `rhsLen r`: the length of the code a rule's right-hand side forces, when it is a list literal
  (as `FwdB30X.ruleLen`, on the other side of `~>`).
* `stepRhsT`: `rhsLen` of the 36 rules of `Step` of the pinned wasm-3.0 script, checked by kernel
  `rfl` in `Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30DTables`.
* `rhsOk t M`: every rule of `Step` from rule 3 on names a constructor outside `t :: valTags`, or
  forces a right-hand side of length at least `M`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30D

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

mutual
/-- An administrative instruction that `Bwd.AdminEq` relates only to itself: not a `CALL_REF`,
and a label, handler or frame only with a `deepRigidL` body. -/
def deepRigid : Admin → Bool
  | .plain (.callRef _) => false
  | .callRefType _ => false
  | .label _ _ is => deepRigidL is
  | .handler _ _ is => deepRigidL is
  | .frame _ _ is => deepRigidL is
  | _ => true

/-- Every instruction of the list is `deepRigid`. -/
def deepRigidL : List Admin → Bool
  | [] => true
  | a :: l => deepRigid a && deepRigidL l
end

/-! ## Right-hand sides -/

section Rhs

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec.Institution.FwdB30X (codeLen valTags outside stepInfoT)

/-- The forced length of the right-hand side of a conclusion `lhs ~> rhs`. -/
def concRhs : Exp → Option Nat
  | .tupE [_, r] => codeLen r
  | _ => none

/-- The forced length of a rule's right-hand side. -/
def rhsLen : Rule → Option Nat
  | .ruleD _ _ _ e _ => concRhs e

/-- `rhsLen` of the 36 rules of `Step`, in order. -/
def stepRhsT : List (Option Nat) :=
  [none, none, none, some 1, some 1, some 1, some 1, some 1, none, none, some 2, some 0, some 0,
   some 1, some 0, some 1, some 1, some 0, some 1, some 0, some 1, some 0, some 1, some 0, some 1,
   some 0, some 1, some 1, some 0, some 1, some 1, some 0, some 1, some 1, some 1, some 0]

/-- Every rule of `Step` from rule 3 on names a constructor outside `t :: valTags` or forces a
right-hand side of length at least `M`. -/
def rhsOk (t : MixopS) (M : Nat) : Bool :=
  (List.range 36).all fun i => i < 3 || outside (t :: valTags) (stepInfoT.getD i ([], none)) ||
    (stepRhsT.getD i none).any (M ≤ ·)

end Rhs

/-- No instruction of a block body is a `call_ref` at the top. -/
def callFree (body : List Instr) : Bool :=
  body.all fun i => deepRigid (.plain i)

end Silmaril.Wasm.SpecTec.Institution.FwdB30D

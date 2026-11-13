module

public import Silmaril.Compiler.Core.Verified.StateExpr.Defs

/-! # `x++;` and `x--;` as statements: the recogniser

Cerberus elaborates the statement `x++;` (and `++x;`, `x--;`, `--x;`, whose value is discarded) to
a sequenced read-modify-write of the local's object:

`let strong _ = bound(let weak p = pure(x) in seq_rmw(int, p, v =>`
`  case v of Specified(z) => Specified(conv_int(int, catch_exceptional_condition(int, op, conv_int(int, z), 1)))`
`  | Unspecified(_) => …)) in pure(Unit)`

with `op` the addition or the subtraction. `rmwStmt` recognises this shape; the update is
std.core's `conv_int` (`ConvInt.convInt`) of Cerberus's guarded operation (`Guard.convOf`). The
proof of its run is `RmwSound.rmw_runs`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Rmw

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics (EE)

/-- The symbol `c` names std.core's `conv_int`. -/
def convFun (file : File Codec.wireModel Unit Unit) (c : Sym) : Bool :=
  match ConvInt.lookupFun file c with
  | some d => ConvInt.convInt file d
  | none => false

/-- `x++;` or `x--;`: the local and the operator. -/
def rmwStmt (file : File Codec.wireModel Unit Unit) : EE → Option (Sym × IntOp)
  | .mk _ (.sseq (.mk _ (.base (none, _)))
      (.mk _ (.bound (.mk _ (.wseq (.mk _ (.base (some p, _))) (.mk _ (.pure (.mk _ () (.sym x))))
        (.mk _ (.action (.mk .pos (.mk _ _ (.seqRmw false
          (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
          (.mk _ () (.sym p')) v
          (.mk _ () (.case_ (.mk _ () (.sym v'))
            ((.mk _ (.ctor .specified [.mk _ (.base (some z, _))]),
              .mk _ () (.ctor .specified [.mk _ () (.call (.sym c)
                [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))),
                 .mk _ () (.catchExceptionalCondition (.signed .int) op q
                   (.mk _ () (.val (.object (.integer one)))))])])) :: _))))))))))))
      (.mk _ (.pure (.mk _ () (.val .unit))))) =>
    if decide (p'.key = p.key ∧ v'.key = v.key ∧ one = 1 ∧ (op = .add ∨ op = .sub)) &&
        Guard.convOf file z q && convFun file c then some (x, op) else none
  | _ => none

/-- A bound post-increment or post-decrement expression, retaining its old value. -/
def boundRmw (file : File Codec.wireModel Unit Unit) : EE → Option (Sym × IntOp)
  | .mk _ (.bound (.mk _ (.wseq (.mk _ (.base (some p, _))) (.mk _ (.pure (.mk _ () (.sym x))))
        (.mk _ (.action (.mk .pos (.mk _ _ (.seqRmw false
          (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
          (.mk _ () (.sym p')) v
          (.mk _ () (.case_ (.mk _ () (.sym v'))
            ((.mk _ (.ctor .specified [.mk _ (.base (some z, _))]),
              .mk _ () (.ctor .specified [.mk _ () (.call (.sym c)
                [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))),
                 .mk _ () (.catchExceptionalCondition (.signed .int) op q
                   (.mk _ () (.val (.object (.integer one)))))])])) :: _))))))))))) =>
    if decide (p'.key = p.key ∧ v'.key = v.key ∧ one = 1 ∧ (op = .add ∨ op = .sub)) &&
        Guard.convOf file z q && convFun file c then some (x, op) else none
  | _ => none

/-- Compute the updated value, then recover the value preceding a post-increment/decrement.
The update itself remains in the runtime expression. -/
def oldTerm (x : Sym) (op : IntOp) : StateExpr.Term :=
  .bin (if op = .add then .sub else .add) (.bin op (.var x.key) (.lit 1)) (.lit 1)

end Silmaril.Compile.Core.Verified.Rmw

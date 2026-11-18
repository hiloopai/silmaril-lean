module

public import Silmaril.Logic.Consequence.FirstOrder.Derivation.SExp.Defs
public import Silmaril.Logic.Consequence.FirstOrder.Derivation.Thms
public import Silmaril.Logic.Consequence.Derivation.SExp.Thms
public import Silmaril.Logic.Concrete.Codec.Thms
import Silmaril.Proofs.Logic.Consequence.FirstOrder.DerivationSExp

/-!
# First-order proofs as S-expressions: presentations and checked pipelines

* `seqCodec` (`silmaril.fol.sequent`, v1): judgments over a named signature; `treeCodec` and
  `linesCodec`: the generic derivation formats over it.
* `checkTree` and `checkLines`: decode, elaborate, check; the conclusion, or the stage that
  rejected the proof. `checkTree_encode`, `checkLines_encode`: on an encoding, they are the raw
  checks.
* `checkTree_sound`, `checkLines_sound`: an accepted proof's conclusion is derived by checked
  proof trees, hence true in every structure satisfying its hypotheses.
-/

@[expose] public section

namespace Silmaril.Consequence.FirstOrder.ND

open Silmaril.Logic.Institution.Examples.UFOL
open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete (SExpCodec)

variable (opArity relArity : String → Option ℕ)

theorem readSeq_encode (s : Seq (named opArity relArity)) :
    readSeq opArity relArity (encodeSeq s) = some s :=
  Proofs.Logic.Consequence.FirstOrder.DerivationSExp.readSeq_encode s

/-- **The presentation of first-order judgments** over a named signature. -/
def seqCodec : SExpCodec (Seq (named opArity relArity)) :=
  .ofReader "silmaril.fol.sequent" "1" encodeSeq (readSeq opArity relArity) (readSeq_encode _ _)

/-- The tree format for first-order proofs. -/
def treeCodec : SExpCodec (ProofTree SE (Seq (named opArity relArity))) :=
  ProofSExp.treeCodec (seqCodec opArity relArity)

/-- The lines format for first-order proofs. -/
def linesCodec : SExpCodec (List (Line SE (Seq (named opArity relArity)))) :=
  ProofSExp.linesCodec (seqCodec opArity relArity)

/-- **Check a proof tree**: decode, elaborate, check. -/
def checkTree (e : SE) : Except Rejection (Seq (named opArity relArity)) :=
  match (treeCodec opArity relArity).decode e with
  | none => .error .syntax
  | some raw => checkRawTree opArity relArity raw

/-- **Check indexed lines**: decode, elaborate, check. -/
def checkLines (e : SE) : Except Rejection (Seq (named opArity relArity)) :=
  match (linesCodec opArity relArity).decode e with
  | none => .error .syntax
  | some raw => checkRawLines opArity relArity raw

theorem checkTree_encode (raw : ProofTree SE (Seq (named opArity relArity))) :
    checkTree opArity relArity ((treeCodec opArity relArity).encode raw) =
      checkRawTree opArity relArity raw := by
  simp [checkTree, SExpCodec.decode_encode]

theorem checkLines_encode (raw : List (Line SE (Seq (named opArity relArity)))) :
    checkLines opArity relArity ((linesCodec opArity relArity).encode raw) =
      checkRawLines opArity relArity raw := by
  simp [checkLines, SExpCodec.decode_encode]

variable {opArity relArity}

/-- **An accepted raw proof tree is a derivation.** -/
theorem checkRawTree_sound {raw : ProofTree SE (Seq (named opArity relArity))}
    {s : Seq (named opArity relArity)} (h : checkRawTree opArity relArity raw = .ok s) :
    (system (named opArity relArity)).derives [] s :=
  Proofs.Logic.Consequence.FirstOrder.DerivationSExp.checkRawTree_sound h

/-- **An accepted proof tree is a derivation.** -/
theorem checkTree_sound {e : SE} {s : Seq (named opArity relArity)}
    (h : checkTree opArity relArity e = .ok s) : (system (named opArity relArity)).derives [] s := by
  unfold checkTree at h; split at h
  · cases h
  · exact checkRawTree_sound h

/-- **Accepted raw indexed lines are a derivation** of the last line's conclusion. -/
theorem checkRawLines_sound {raw : List (Line SE (Seq (named opArity relArity)))}
    {s : Seq (named opArity relArity)} (h : checkRawLines opArity relArity raw = .ok s) :
    (system (named opArity relArity)).derives [] s :=
  Proofs.Logic.Consequence.FirstOrder.DerivationSExp.checkRawLines_sound h

/-- **Accepted indexed lines are a derivation.** -/
theorem checkLines_sound {e : SE} {s : Seq (named opArity relArity)}
    (h : checkLines opArity relArity e = .ok s) : (system (named opArity relArity)).derives [] s := by
  unfold checkLines at h; split at h
  · cases h
  · exact checkRawLines_sound h

end Silmaril.Consequence.FirstOrder.ND

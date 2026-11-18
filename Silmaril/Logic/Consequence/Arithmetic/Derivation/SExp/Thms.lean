module

public import Silmaril.Logic.Consequence.Arithmetic.Derivation.SExp.Defs
public import Silmaril.Logic.Consequence.Arithmetic.Derivation.Thms
public import Silmaril.Logic.Consequence.Derivation.SExp.Thms
import Silmaril.Proofs.Logic.Consequence.Arithmetic.Derivation.SExp
public import Silmaril.Logic.Concrete.Codec.Thms

/-!
# PA and Q proofs as S-expressions: presentations and checked pipelines

* `seqCodec` (`silmaril.arithmetic.sequent`, v1): the judgments.
* `treeCodec` and `linesCodec`: the generic derivation formats over `seqCodec`.
* `checkTree T e` and `checkLines T e`: decode, elaborate, check, and return the conclusion or
  the stage that rejected the proof. `checkTreeBytes` and `checkLinesBytes` first read one
  S-expression from bytes.
* `checkTree_sound`, `checkLines_sound` (and the byte versions): an accepted proof's conclusion
  is derivable in `T` (`Seq.Derivable`, the existing natural deduction), hence valid in ℕ.
-/

@[expose] public section

namespace Silmaril.Consequence.Arithmetic.ND

open Silmaril.Logic.Arithmetic
open Silmaril.Logic.Smt (SE readForms)
open Silmaril.Logic.Concrete (SExpCodec)

theorem readSeq_encode (s : Seq) : readSeq (encodeSeq s) = some s :=
  Proofs.Logic.Consequence.Arithmetic.Derivation.SExp.readSeq_encode s

/-- **The presentation of PA judgments.** -/
def seqCodec : SExpCodec Seq :=
  .ofReader "silmaril.arithmetic.sequent" "1" encodeSeq readSeq readSeq_encode

/-- The tree format for PA proofs. -/
def treeCodec : SExpCodec (ProofTree SE Seq) := ProofSExp.treeCodec seqCodec

/-- The lines format for PA proofs. -/
def linesCodec : SExpCodec (List (Line SE Seq)) := ProofSExp.linesCodec seqCodec

/-- Elaborate and check a raw proof tree in `T`. -/
def checkRawTree (T : Theory) (raw : ProofTree SE Seq) : Except Rejection Seq :=
  match raw.elaborate elabRule with
  | none => .error .elaboration
  | some t => if (system T).check [] t then .ok t.concl else .error .check

/-- Elaborate and check raw indexed lines in `T`; the conclusion is the last line's. -/
def checkRawLines (T : Theory) (raw : List (Line SE Seq)) : Except Rejection Seq :=
  match raw.getLast? with
  | none => .error .empty
  | some last =>
    match Line.elaborate elabRule [] raw with
    | none => .error .elaboration
    | some ls => if (system T).checkLines [] [] ls then .ok last.concl else .error .check

/-- **Check a proof tree** in `T`: decode, elaborate, check. -/
def checkTree (T : Theory) (e : SE) : Except Rejection Seq :=
  match treeCodec.decode e with
  | none => .error .syntax
  | some raw => checkRawTree T raw

/-- **Check indexed lines** in `T`: decode, elaborate, check. -/
def checkLines (T : Theory) (e : SE) : Except Rejection Seq :=
  match linesCodec.decode e with
  | none => .error .syntax
  | some raw => checkRawLines T raw

theorem checkTree_encode (T : Theory) (raw : ProofTree SE Seq) :
    checkTree T (treeCodec.encode raw) = checkRawTree T raw := by
  simp [checkTree, SExpCodec.decode_encode]

theorem checkLines_encode (T : Theory) (raw : List (Line SE Seq)) :
    checkLines T (linesCodec.encode raw) = checkRawLines T raw := by
  simp [checkLines, SExpCodec.decode_encode]

/-- Read exactly one S-expression from bytes. -/
def readOne (bytes : List UInt8) : Except Rejection SE :=
  match readForms bytes with
  | some [e] => .ok e
  | _ => .error .syntax

/-- Check a proof tree written as bytes. -/
def checkTreeBytes (T : Theory) (bytes : List UInt8) : Except Rejection Seq :=
  readOne bytes >>= checkTree T

/-- Check indexed lines written as bytes. -/
def checkLinesBytes (T : Theory) (bytes : List UInt8) : Except Rejection Seq :=
  readOne bytes >>= checkLines T

/-- **An accepted raw proof tree is a derivation.** -/
theorem checkRawTree_sound {T : Theory} {raw : ProofTree SE Seq} {s : Seq}
    (h : checkRawTree T raw = .ok s) : s.Derivable T :=
  Proofs.Logic.Consequence.Arithmetic.Derivation.SExp.checkRawTree_sound h

/-- **Accepted raw indexed lines are a derivation** of the last line's conclusion. -/
theorem checkRawLines_sound {T : Theory} {raw : List (Line SE Seq)} {s : Seq}
    (h : checkRawLines T raw = .ok s) : s.Derivable T :=
  Proofs.Logic.Consequence.Arithmetic.Derivation.SExp.checkRawLines_sound h

/-- **An accepted proof tree is a derivation.** -/
theorem checkTree_sound {T : Theory} {e : SE} {s : Seq} (h : checkTree T e = .ok s) :
    s.Derivable T := by
  unfold checkTree at h; split at h
  · cases h
  · exact checkRawTree_sound h

/-- **Accepted indexed lines are a derivation.** -/
theorem checkLines_sound {T : Theory} {e : SE} {s : Seq} (h : checkLines T e = .ok s) :
    s.Derivable T := by
  unfold checkLines at h; split at h
  · cases h
  · exact checkRawLines_sound h

theorem checkTreeBytes_sound {T : Theory} {bytes : List UInt8} {s : Seq}
    (h : checkTreeBytes T bytes = .ok s) : s.Derivable T := by
  unfold checkTreeBytes readOne at h
  split at h
  · exact checkTree_sound h
  · cases h

theorem checkLinesBytes_sound {T : Theory} {bytes : List UInt8} {s : Seq}
    (h : checkLinesBytes T bytes = .ok s) : s.Derivable T := by
  unfold checkLinesBytes readOne at h
  split at h
  · exact checkLines_sound h
  · cases h

end Silmaril.Consequence.Arithmetic.ND

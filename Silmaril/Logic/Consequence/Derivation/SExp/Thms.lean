module

public import Silmaril.Logic.Consequence.Derivation.SExp.Defs
import Silmaril.Proofs.Logic.Consequence.Derivation.SExp.Basic

/-!
# Derivations as S-expressions: the presentations

* `readTree_encode`, `readLines_encode`: the readers invert the encoders.
* `treeCodec cj` (`silmaril.derivation.tree`, v1) and `linesCodec cj`
  (`silmaril.derivation.lines`, v1): presentations of raw proof trees and raw indexed lines over
  the judgment presentation `cj`; each decoder accepts exactly the canonical forms.
-/

@[expose] public section

namespace Silmaril.Consequence.ProofSExp

open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete (SExpCodec)

universe u

variable {J : Type u} (cj : SExpCodec J)

theorem readTree_encode (t : ProofTree SE J) : readTree cj (encodeTree cj t) = some t :=
  Proofs.Logic.Consequence.Derivation.SExp.readTree_encode cj t

theorem readLines_encode (ls : List (Line SE J)) : readLines cj (encodeLines cj ls) = some ls :=
  Proofs.Logic.Consequence.Derivation.SExp.readLines_encode cj ls

/-- **The tree format** over the judgment presentation `cj`. -/
def treeCodec : SExpCodec (ProofTree SE J) :=
  .ofReader "silmaril.derivation.tree" "1" (encodeTree cj) (readTree cj) (readTree_encode cj)

/-- **The indexed lines format** over the judgment presentation `cj`. -/
def linesCodec : SExpCodec (List (Line SE J)) :=
  .ofReader "silmaril.derivation.lines" "1" (encodeLines cj) (readLines cj) (readLines_encode cj)

end Silmaril.Consequence.ProofSExp

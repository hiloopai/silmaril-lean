module

public import Silmaril.Logic.Metamath.Verify.Defs
public import Silmaril.Logic.Metamath.Verify.Soundness
public import Silmaril.Logic.Metamath.Theory.Cut
public import Mathlib.Data.String.Basic
import Silmaril.Proofs.Logic.Metamath.Verify.EndToEnd

@[expose] public section

/-!
# Soundness of Metamath text verification

Every theorem of an accepted database is derivable from its preceding axioms.
Earlier theorems used as lemmas are eliminated by cut admissibility. The final
contract also identifies each source `$p` statement by its label, typecode and
body tokens; it does not merely state a property of some unrelated database.

These theorems take an equality proving successful execution. Running the
checker as native code or in an elaboration-time test does not by itself
produce that equality as a Lean proof. `Verify.Kernel` gives a small proof
machine example whose acceptance is established by kernel reduction.
-/

namespace Silmaril.Logic.Metamath.Verify

open Text

/-- Cut is admissible for string symbols, since `String` is infinite. -/
theorem cutAdmissible_string : CutAdmissible String String :=
  Silmaril.Proofs.Logic.Metamath.Verify.cutAdmissible_string

/-- Successful text verification consists of parsing and checking the parsed source. -/
theorem verifyText_ok {text : String} {db : Database String String}
    (h : verifyText text = .ok db) : ∃ src, parse text = .ok src ∧ check src = .ok db :=
  Silmaril.Proofs.Logic.Metamath.Verify.verifyText_ok h

/-- Every theorem of an accepted database is derivable from the axioms before it. -/
theorem verifyText_sound {text : String} {db : Database String String}
    (h : verifyText text = .ok db) :
    ∀ i (hi : i < db.entries.size), db.entries[i].kind = .theorem →
      Derivable (db.kindBefore .axiom i) db.entries[i].assertion :=
  Silmaril.Proofs.Logic.Metamath.Verify.verifyText_sound h

/-- Each source `$p` statement is recorded with its label, typecode and body,
and is derivable from the preceding `$a` statements. -/
theorem verifyText_provable {text : String} {db : Database String String}
    (h : verifyText text = .ok db) {src : Source} (hsrc : parse text = .ok src)
    {l tc : String} {body : List String} {pf : ProofText}
    (hst : Stmt.provable l tc body pf ∈ src) :
    ∃ i, ∃ hi : i < db.entries.size, db.entries[i].label = l ∧
      db.entries[i].assertion.concl.tc = tc ∧
      db.entries[i].assertion.concl.body.map symToken = body ∧
      Derivable (db.kindBefore .axiom i) db.entries[i].assertion :=
  Silmaril.Proofs.Logic.Metamath.Verify.verifyText_provable h hsrc hst

end Silmaril.Logic.Metamath.Verify

module

public import Silmaril.Logic.Metamath.Verify.Defs
public import Silmaril.Logic.Metamath.Verify.Soundness
public import Silmaril.Logic.Metamath.Theory.Cut
public import Mathlib.Data.String.Basic

@[expose] public section

namespace Silmaril.Proofs.Logic.Metamath.Verify

open Silmaril.Logic.Metamath Silmaril.Logic.Metamath.Verify Text

/-- Cut is admissible for string symbols, since `String` is infinite. -/
theorem cutAdmissible_string : CutAdmissible String String :=
  fun _ _ _ _ _ _ hB hA => Derivable.cut_insert hB hA

theorem verifyText_ok {text : String} {db : Database String String}
    (h : verifyText text = .ok db) : ∃ src, parse text = .ok src ∧ check src = .ok db := by
  unfold verifyText at h
  split at h
  · cases h
  · rename_i src hsrc
    split at h
    · cases h
    · rename_i db' hdb
      cases h
      exact ⟨src, hsrc, hdb⟩

/-- Every theorem of an accepted database is derivable from the axioms before it. -/
theorem verifyText_sound {text : String} {db : Database String String}
    (h : verifyText text = .ok db) :
    ∀ i (hi : i < db.entries.size), db.entries[i].kind = .theorem →
      Derivable (db.kindBefore .axiom i) db.entries[i].assertion := by
  obtain ⟨_, -, hdb⟩ := verifyText_ok h
  exact (check_sound hdb).derivable_axioms cutAdmissible_string

/-- End-to-end: each `$p` statement written in an accepted file is recorded,
with its label, typecode and math string, and is derivable from the `$a`
statements before it. -/
theorem verifyText_provable {text : String} {db : Database String String}
    (h : verifyText text = .ok db) {src : Source} (hsrc : parse text = .ok src)
    {l tc : String} {body : List String} {pf : ProofText}
    (hst : Stmt.provable l tc body pf ∈ src) :
    ∃ i, ∃ hi : i < db.entries.size, db.entries[i].label = l ∧
      db.entries[i].assertion.concl.tc = tc ∧
      db.entries[i].assertion.concl.body.map symToken = body ∧
      Derivable (db.kindBefore .axiom i) db.entries[i].assertion := by
  obtain ⟨src', hsrc', hdb⟩ := verifyText_ok h
  rw [hsrc] at hsrc'
  cases hsrc'
  exact check_provable_axioms cutAdmissible_string hdb hst


end Silmaril.Proofs.Logic.Metamath.Verify

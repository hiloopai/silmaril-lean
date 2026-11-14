module

public import Silmaril.Semantics.TraceModels.Defs
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter
import Batteries.Tactic.Alias

/-!
# PartialWriter.Traces: proofs

Proofs for `Silmaril.Semantics.TraceModels.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B : Type u} [Monoid W]

private theorem runs_value_iff (f : A → PartialWriter W (B ⊕ A)) (a : A) (b : B) :
    Part.Runs (fun a => (f a).value) a b ↔ ∃ w, Runs f a w b := by
  constructor
  · intro h
    induction h with
    | done hs => exact ⟨_, .done hs⟩
    | more hs _ ih => obtain ⟨w, hw⟩ := ih; exact ⟨_, .step hs hw⟩
  · rintro ⟨w, h⟩
    induction h with
    | done hs => exact .done hs
    | step hs _ ih => exact .more hs ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.runs_value_iff := Silmaril.Elgot.PartialWriter.runs_value_iff

namespace Prefix

private theorem append {f : A → PartialWriter W (B ⊕ A)} {a b c : A} {v w : W}
    (h : Prefix f a v b) (k : Prefix f b w c) : Prefix f a (v * w) c := by
  induction h with
  | start => simpa only [one_mul] using k
  | step hs _ ih => simpa only [mul_assoc] using Prefix.step hs (ih k)
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.append := Silmaril.Elgot.PartialWriter.Prefix.append

private theorem append_run {f : A → PartialWriter W (B ⊕ A)} {a z : A} {b : B} {v w : W}
    (h : Prefix f a v z) (k : Runs f z w b) : Runs f a (v * w) b := by
  induction h with
  | start => simpa only [one_mul] using k
  | step hs _ ih => simpa only [mul_assoc] using Runs.step hs (ih k)
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.append_run := Silmaril.Elgot.PartialWriter.Prefix.append_run

end Prefix

namespace Runs

private theorem unique {f : A → PartialWriter W (B ⊕ A)} {a : A} {b c : B} {v w : W}
    (h : Runs f a v b) (k : Runs f a w c) : v = w ∧ b = c := by
  induction h generalizing w c with
  | done hs =>
      cases k with
      | done ht => exact ⟨rfl, Sum.inl.inj (_root_.Part.mem_unique hs ht)⟩
      | step ht _ => cases _root_.Part.mem_unique hs ht
  | step hs _ ih =>
      cases k with
      | done ht => cases _root_.Part.mem_unique hs ht
      | step ht hk =>
          have heq := Sum.inr.inj (_root_.Part.mem_unique hs ht)
          subst heq
          obtain ⟨rfl, rfl⟩ := ih hk
          exact ⟨rfl, rfl⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Runs.unique := Silmaril.Elgot.PartialWriter.Runs.unique

private theorem last {f : A → PartialWriter W (B ⊕ A)} {a : A} {b : B} {v : W}
    (h : Runs f a v b) :
    ∃ w z, Prefix f a w z ∧ Sum.inl b ∈ (f z).value ∧ w * (f z).output = v := by
  induction h with
  | done hs => exact ⟨1, _, .start _, hs, one_mul _⟩
  | step hs _ ih =>
      obtain ⟨w, z, hp, ht, hw⟩ := ih
      exact ⟨_, z, .step hs hp, ht, by rw [mul_assoc, hw]⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Runs.last := Silmaril.Elgot.PartialWriter.Runs.last

end Runs

end Silmaril.Elgot.PartialWriter

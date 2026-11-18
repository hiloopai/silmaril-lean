module

public import Silmaril.ProofFormats.LeanNDJSON.Arithmetic.Defs
public import Silmaril.Formats.LeanNDJSON.Validate.Thms

/-!
# Proofs for PA proofs from Lean-NDJSON
-/

@[expose] public section

namespace Silmaril.Proofs.ProofFormats.LeanNDJSON.Arithmetic

open Silmaril.ProofFormats.LeanNDJSON.Arithmetic Silmaril.Formats.LeanNDJSON
open Silmaril.Consequence.Arithmetic.ND

theorem importCheckFrom_sound {T : Theory} {es : List Event} {decl : String} {s : Seq}
    (h : importCheckFrom T es decl = .ok s) : s.Derivable T := by
  simp only [importCheckFrom, bind, Except.bind] at h
  split at h
  · cases h
  · next e _ =>
    cases hc : checkTree T e with
    | error r => simp [hc, Except.mapError] at h
    | ok s' => simp [hc, Except.mapError] at h; exact h ▸ checkTree_sound hc

theorem readFile_valid {bytes : List UInt8} {es : List Event} (h : readFile bytes = .ok es) :
    ∃ f, parseFile bytes = .ok f ∧ f.events = es ∧ Valid es := by
  simp only [readFile, bind, Except.bind] at h
  split at h
  · cases h
  · next f hf =>
    have hf' : parseFile bytes = .ok f := by
      cases hp : parseFile bytes <;> simp [hp, Except.mapError] at hf; exact hf ▸ rfl
    by_cases h1 : serialValid? .initial f.events = true
    · by_cases h2 : (declNames f.events).Nodup
      · simp [h1, h2, pure, Except.pure] at h
        exact ⟨f, hf', h, h ▸ ⟨(serialValid?_iff _ _).1 h1, h2⟩⟩
      · simp [h1, h2, throw, throwThe, MonadExceptOf.throw] at h
    · simp [h1, throw, throwThe, MonadExceptOf.throw] at h

theorem importCheck_sound {T : Theory} {bytes : List UInt8} {decl : String} {s : Seq}
    (h : importCheck T bytes decl = .ok s) : s.Derivable T ∧ ∃ es, readFile bytes = .ok es ∧ Valid es := by
  simp only [importCheck, bind, Except.bind] at h
  split at h
  · cases h
  · next es hes =>
    obtain ⟨_, _, _, hv⟩ := readFile_valid hes
    exact ⟨importCheckFrom_sound h, es, hes, hv⟩

end Silmaril.Proofs.ProofFormats.LeanNDJSON.Arithmetic

module

public import Silmaril.Net.Http1.Codings.Defs

/-!
# Transfer codings: laws

* `checkCodings_ok_final`: an accepted nonempty coding list ends in `chunked`, and `chunked`
  occurs exactly once (§6.1, §6.3 rule 4).
* `decodeTransfer_encodeTransfer`: if a coding library's decoders invert its encoders
  (`Decoders.Inverts`, the abstract assumption on content codings), undoing the codings
  recovers the content for every coding list it can apply.
* `decodeTransfer_nil`: with only `chunked`, the content is the dechunked octets.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)

theorem decodeTransfer_nil (d : Decoders) (x : Bytes) : decodeTransfer d [] x = some x := rfl

theorem innerCodings_chunked : innerCodings [chunkedName] = [] := by decide

/-- Round trip of transfer codings, under the decoder/encoder assumption. -/
theorem decodeTransfer_encodeTransfer {d : Decoders} {e : Encoders} (h : d.Inverts e) :
    ∀ (cs : List Bytes) (x y : Bytes), encodeTransfer e cs x = some y →
      decodeTransfer d cs y = some x := by
  intro cs
  induction cs with
  | nil => intro x y hy; cases hy; rfl
  | cons c cs ih =>
    intro x y hy
    simp only [encodeTransfer, Option.bind_eq_some_iff] at hy
    obtain ⟨f, hf, hy⟩ := hy
    obtain ⟨g, hg, hgf⟩ := h _ f hf
    simp [decodeTransfer, ih _ _ hy, hg, hgf]

/-- An accepted, nonempty list of request codings ends in a single `chunked`. -/
theorem checkCodings_ok_final {impl : Bytes → Bool} {tcs : List Bytes}
    (h : checkCodings impl tcs = .ok) (hne : tcs ≠ []) :
    tcs.getLast? = some chunkedName ∧ chunkedName ∉ tcs.dropLast := by
  obtain ⟨init, last, rfl⟩ := List.eq_nil_or_concat tcs |>.resolve_left hne
  have hr : (init.concat last).reverse = last :: init.reverse := by simp
  unfold checkCodings at h
  rw [hr] at h
  simp only at h
  by_cases h₁ : last = chunkedName
  · subst h₁
    by_cases h₂ : chunkedName ∈ init.reverse
    · simp [h₂] at h
    · simp only [List.mem_reverse] at h₂
      simp [h₂]
  · simp [h₁] at h

end Silmaril.Net.Http1

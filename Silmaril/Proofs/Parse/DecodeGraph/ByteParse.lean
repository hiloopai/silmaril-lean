module

public import Silmaril.Parse.DecodeGraph.ByteParse.Defs

public section

namespace Silmaril.Parse.DecodeGraph.Proofs

variable {Context Buffer : Type*}

theorem soundFor_ofParser {Value : Type} {grammar : ByteParse.Bytes → Value → Prop}
    {parser : ByteParse.Parser Value} :
    SoundFor .byteArray (ofParser parser) (ofGrammar fun _ => grammar) ↔ ByteParse.Sound grammar parser := by
  constructor
  · intro sound bytes stop pos value endPos start bound run
    have result := sound (input := ⟨(), bytes, stop, pos⟩) (result := (value, endPos)) ⟨trivial, start, bound⟩ run
    exact ⟨result.2.1, result.2.2.1, result.2.2.2.2⟩
  · rintro sound ⟨⟨⟩, bytes, stop, pos⟩ ⟨value, endPos⟩ ⟨_, start, bound⟩ run
    obtain ⟨advance, inside, spec⟩ := sound start bound run
    exact ⟨trivial, advance, inside, bound, spec⟩

theorem completeFor_ofParser {Value : Type} {grammar : ByteParse.Bytes → Value → Prop}
    {parser : ByteParse.Parser Value} :
    CompleteFor .byteArray (ofParser parser) (ofGrammar fun _ => grammar) ↔ ByteParse.Complete grammar parser := by
  constructor
  · intro complete segment value bytes stop pos spec inside bound eqSegment
    have start : pos ≤ stop := by omega
    have encoded : grammar (ByteParse.seg bytes pos (pos + segment.length)) value := by rw [eqSegment]; exact spec
    exact complete (input := ⟨(), bytes, stop, pos⟩) (result := (value, pos + segment.length))
      ⟨trivial, start, bound⟩ ⟨trivial, Nat.le_add_right .., inside, bound, encoded⟩
  · rintro complete ⟨⟨⟩, bytes, stop, pos⟩ ⟨value, endPos⟩ _ ⟨_, advance, inside, bound, spec⟩
    change pos ≤ endPos at advance
    change endPos ≤ stop at inside
    change stop ≤ bytes.size at bound
    change grammar (ByteParse.seg bytes pos endPos) value at spec
    have endpoint : pos + (ByteParse.seg bytes pos endPos).length = endPos := by
      simp only [ByteParse.seg, List.extract_eq_take_drop, List.length_take, List.length_drop, Array.length_toList]
      change pos + min (endPos - pos) (bytes.size - pos) = endPos
      omega
    have run := complete spec (by rwa [endpoint]) bound (by rw [endpoint])
    rwa [endpoint] at run

theorem successes_deterministic {Value : Type} (run : Context → Buffer → Nat → Nat → ByteParse.Res Value) :
    Deterministic (successes run) := by
  rintro ⟨ctx, bytes, stop, pos⟩ ⟨left, leftEnd⟩ ⟨right, rightEnd⟩
    (hl : run ctx bytes stop pos = .ok left leftEnd) (hr : run ctx bytes stop pos = .ok right rightEnd)
  obtain ⟨rfl, rfl⟩ := ByteParse.Res.ok.inj (hl.symm.trans hr)
  rfl

theorem positive_ofGrammar {Value : Type} {grammar : Context → ByteParse.Bytes → Value → Prop}
    (nonempty : ∀ ctx, ByteParse.NonEmpty (grammar ctx)) : Positive (ofGrammar grammar) := by
  rintro input value endPos ⟨advance, _, _, accepted⟩
  change input.pos ≤ endPos at advance
  change grammar input.context (input.bytes.extract input.pos endPos) value at accepted
  by_cases same : endPos = input.pos
  · exact (nonempty input.context accepted (by simp [same])).elim
  · omega

end Silmaril.Parse.DecodeGraph.Proofs
